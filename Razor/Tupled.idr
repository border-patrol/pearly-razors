||| An expression language with mechanical proof of type-safety.
|||
||| `Tupled` is an expression language supporting Let-bindings, and
||| Tuples.  Standard constructions are used to represent the language
||| as an EDSL, together with proof of progress taken from PLFA Part
||| 2.
|||
||| This module compliments Section 3 of the Functional Pearl, but does
||| not appear due to similarities with `Razor.Recorded`.
|||
module Razor.Tupled

import Razor.Common

%default total

namespace Types

  public export
  data Ty = TyInt
          | TyChar
          | TyTuple (Vect (S n) Ty)

namespace Terms

  mutual
    ||| Fields in a Tuple.
    public export
    data Fields : (g     : List Ty)
               -> (types : Vect (S n) Ty)
               -> Type
      where
        Singleton : {ty    : Ty}
                 -> (field : Tupled g ty)
                          -> Fields g (ty::Nil)

        Extend : {ty    : Ty}
              -> {tys   : Vect (S n) Ty}
              -> (field : Tupled g ty)
              -> (rest  : Fields g      tys)
                       -> Fields g (ty::tys)

    public export
    data Tupled : List Ty -> Ty -> Type where
         -- Let-Bindings & Variables
          Var : Elem ty g -> Tupled g ty

          Let : (this     : Tupled        g  expr)
             -> (beInThis : Tupled (expr::g) body)
                         -> Tupled        g  body

          -- Base Values
          I : Int  -> Tupled g TyInt
          C : Char -> Tupled g TyChar

          -- Tuples & Accessors
          MkTuple : {types : Vect (S n) Ty}
                 -> (values : Fields g          types)
                           -> Tupled g (TyTuple types)

          Proj : {types : Vect (S n) Ty}
              -> (i     : Fin (S n))
              -> (tuple : Tupled g (TyTuple types))
              -> (idx   : AtIndex i types ty)
                       -> Tupled g ty

  public export
  index : {types  : Vect (S n) Ty}
       -> (fields : Fields  g types)
       -> (idx    : AtIndex i types ty)
                 -> Tupled  g       ty
  index (Singleton field) Here = field
  index (Extend field rest) Here = field

  index (Singleton _) (There Here) impossible
  index (Singleton _) (There (There later)) impossible

  index (Extend field rest) (There later)
    = index rest later


namespace Renaming

  public export
  weaken : (Contains  old           type -> Contains  new           type)
        -> (Contains (old += type') type -> Contains (new += type') type)

  weaken func Here         = Here
  weaken func (There rest) = There (func rest)

  mutual
    namespace Fields
      public export
      rename : (forall type  . Contains old type -> Contains new type)
            -> (forall types . Fields old types -> Fields new types)
      rename f (Singleton first)  = Singleton (rename f first)
      rename f (Extend next rest) = Extend (rename f next) (rename f rest)


    public export
    rename : (forall type . Contains old type -> Contains new type)
          -> (forall type . Tupled   old type -> Tupled   new type)
    -- Let-Bindings & Variables
    rename f (Var x) = Var (f x)
    rename f (Let this beInThis) = Let (rename f this)
                                       (rename (weaken f) beInThis)

    -- Base Values
    rename f (I x) = I x
    rename f (C x) = C x

    -- Tuples & Accessors
    rename f (MkTuple values)   = MkTuple (rename f values)
    rename f (Proj i tuple idx) = Proj i (rename f tuple) idx

namespace Substitution

  public export
  weakens : (forall type . Contains  old           type -> Tupled  new           type)
         -> (forall type . Contains (old += type') type -> Tupled (new += type') type)
  weakens f Here         = Var Here
  weakens f (There rest) = rename There (f rest)


  namespace General
    mutual
      namespace Fields
        public export
        subst : (f     : forall type . Contains old type -> Tupled new type)
             -> (forall types . Fields old types -> Fields new types)
        subst f (Singleton first) = Singleton (subst f first)
        subst f (Extend next rest) = Extend (subst f next) (subst f rest)

      public export
      subst : (forall type . Contains old type -> Tupled new type)
           -> (forall type . Tupled   old type -> Tupled new type)
      -- Let-Bindings & Variables
      subst f (Var x) = f x
      subst f (Let this beInThis) = Let (subst f this)
                                        (subst (weakens f) beInThis)

      -- Base Values
      subst f (I x) = I x
      subst f (C x) = C x

      -- Tuples & Accesors
      subst f (MkTuple values)   = MkTuple (subst f values)
      subst f (Proj i tuple idx) = Proj i (subst f tuple) idx

  namespace Single
    public export
    apply : (this   : Tupled ctxt typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> Tupled ctxt typeA
    apply this Here         = this
    apply this (There rest) = Var rest

    public export
    subst : (this   : Tupled  ctxt           typeB)
         -> (inThis : Tupled (ctxt += typeB) typeA)
                   -> Tupled  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis = General.subst (apply this) inThis


namespace Values
  mutual
    namespace Fields
      public export
      data Value : (fields : Fields g types) -> Type
        where
          SingletonV : (field : Value v) -> Value (Singleton v)
          ExtendV : {field  : Tupled ctxt type}
                 -> {fields : Fields ctxt types}
                 -> (next : Value field)
                 -> (rest : Value fields)
                         -> Value (Extend field fields)

    public export
    data Value : Tupled ctxt type -> Type where

      -- Base Values
      IV : Value (I i)
      CV : Value (C c)

      -- Tuples
      MkTupleV : Value fields
              -> Value (MkTuple fields)

namespace Reduction

  mutual
    namespace Fields
      public export
      data Redux : (this, that : Fields g types) -> Type where
          -- Single field.
          SimplifySingleton : (prf : Redux this that)
                                  -> Redux (Singleton this) (Singleton that)

          SimplifyExtend : {this, that : Tupled ctxt type}
                        -> {rest : Fields ctxt types}
                        -> (prf : Redux this that)
                        -> Redux (Extend this rest) (Extend that rest)

          SimplifyExtendV : {this, that : Fields ctxt types}
                         -> (value      : Values.Value v)
                         -> (rest       : Fields.Redux this that)
                                       -> Redux (Extend v this) (Extend v that)


    public export
    data Redux : (this, that : Tupled ctxt type) -> Type where
      -- Let Bindings
      SimplifyLetValue : Redux this that
                      -> Redux (Let this body)
                               (Let that body)
      ReduceLetBody : Value value
                   -> Redux (Let value body)
                            (subst value body)

      SimplifyTupleR : Redux this that
                    -> Redux (MkTuple this) (MkTuple that)


      -- Accessors
      SimplifyProj : {0  labels : Vect (S n) Ty}
                  -> {   this, that : Tupled g (TyTuple labels)}
                  -> {0  idx        : AtIndex i labels ty}
                  -> Redux this that
                  -> Redux (Proj i this idx) (Proj i that idx)

      ReduceProj : {types  : Vect (S n) Ty}
                -> {fields : Fields g types}
                -> {idx    : AtIndex i types type}
                -> (values : Value fields)
                    -> Redux (Proj i (MkTuple fields) idx)
                             (index fields idx)

namespace Progress


  public export
  data Progress : (term : Tupled Nil type) -> Type where
      Done : Value term -> Progress term
      Step : {this,that : Tupled Nil type} -> (step : Redux this that) -> Progress this

  namespace Fields
    public export
    data Progress : (fields : Fields Nil types) -> Type where
      Done : (value : Value fields) -> Progress fields
      Step : {this,that : Fields Nil types} -> (step  : Redux this that) -> Progress this

  mutual
    namespace Fields
      public export
      progress : (fields : Fields Nil types) -> Progress fields
      progress (Singleton first) with (progress first)
        progress (Singleton first) | (Done x) = Done (SingletonV x)
        progress (Singleton first) | (Step prf) = Step (SimplifySingleton prf)


      progress (Extend next rest) with (progress next)
        progress (Extend next rest) | (Done x) with (progress rest)
          progress (Extend next rest) | (Done x) | (Done xs)  = Done (ExtendV x xs)
          progress (Extend next rest) | (Done x) | (Step prf) = Step (SimplifyExtendV x prf)

        progress (Extend next rest) | (Step prf) = Step (SimplifyExtend prf)

    public export
    progress : (term : Tupled Nil type) -> Progress term
    progress (Var Here) impossible

    -- Let-Bindings & Variables
    progress (Var _) impossible
    progress (Let this beInThis) with (progress this)
      progress (Let this beInThis) | (Done x) = Step (ReduceLetBody x)
      progress (Let this beInThis) | (Step prf) = Step (SimplifyLetValue prf)

    -- Base Values
    progress (I x) = Done IV
    progress (C x) = Done CV

    -- Tuples & Accessors
    progress (MkTuple values) with (progress values)
      progress (MkTuple values) | (Done v)   = Done (MkTupleV v)
      progress (MkTuple values) | (Step prf) = Step (SimplifyTupleR prf)

    progress (Proj i tuple idx) with (progress tuple)
      progress (Proj i (MkTuple fields) idx) | (Done (MkTupleV x)) = Step (ReduceProj x)
      progress (Proj i tuple idx) | (Step prf) = Step (SimplifyProj prf)

namespace Evaluation

  public export
  data Reduces : (this : Tupled ctxt type)
              -> (that : Tupled ctxt type)
              -> Type
    where
      Refl  : {this : Tupled ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : Tupled ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : Tupled ctxt type)
                       -> Type
    where
      Normalised : {term : Tupled ctxt type} -> Value term -> Finished term
      OOF : Finished term

  public export
  data Steps : (term : Tupled Nil type) -> Type where
    MkSteps : {this, that : Tupled Nil type}
           -> (steps  : Inf (Reduces this that))
           -> (result : Finished that)
           -> Steps this

  public export
  data Fuel = Empty | More (Lazy Fuel)

  public export
  covering
  forever : Fuel
  forever = More forever

  public export
  compute : (fuel : Fuel)
         -> (term : Tupled Nil type)
         -> Steps term
  compute Empty term = MkSteps Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = MkSteps Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (MkSteps steps result)
        = MkSteps (Trans step steps) result

public export
covering
run : (this : Tupled Nil type)
           -> Maybe (Subset (Tupled Nil type) (Reduces this))
run this with (compute forever this)
  run this | (MkSteps steps (Normalised {term} x)) = Just (Element term steps)
  run this | (MkSteps steps OOF) = Nothing


namespace Examples
    public export
    abc : Tupled Nil (TyTuple [TyInt, TyChar, TyChar])
    abc = MkTuple (Extend (I 1) (Extend (C 'c') (Singleton (C '2'))))

    public export
    a : Tupled Nil (TyInt)
    a = Proj FZ abc Here

    public export
    b : Tupled Nil (TyChar)
    b = Proj (FS FZ) abc (There Here)
