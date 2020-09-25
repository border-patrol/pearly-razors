||| An expression language with mechanical proof of type-safety.
|||
||| `Variant` is an expression language supporting Let-bindings, and
||| type unsafe variants.  Standard constructions are used to
||| represent the language as an EDSL, together with proof of progress
||| taken from PLFA Part 2.
|||
||| This module compliments Section 4.1 of the Functional Pearl.
|||
module Razor.Variant

import Razor.Common

%default total

namespace Types

  public export
  data Ty = TyInt
          | TyChar
          | TyVariant (Vect (S n) (Pair String Ty))

namespace Terms
  mutual
    public export
    data Case : (ctxt  : List Ty)
             -> (label : String)
             -> (type  : Ty)
             -> (body  : Ty)
             -> Type
      where
        MkCase : (label  : String)
              -> (branch : Variant (ctxt +=    type) body)
                        -> Case     ctxt label type body

    public export
    data Cases : (ctxt  : List Ty)
              -> (types : Vect (S n) (Pair String Ty))
              -> (body  : Ty)
              -> Type
      where
          Singleton : (branch : Case  g   label  ty   b)
                             -> Cases g [(label, ty)] b

          Extend : (branch : Case  g   label  ty          b)
                -> (rest   : Cases g                 kvs  b)
                          -> Cases g ((label, ty) :: kvs) b


    public export
    data Variant : List Ty -> Ty -> Type where
      -- Let-Binding & Variables
      Var : Elem ty g -> Variant g ty

      Let : {expr, body : Ty}
         -> (this     : Variant        g  expr)
         -> (beInThis : Variant (expr::g) body)
                     -> Variant        g  body

      -- Base Values
      I : Int  -> Variant g TyInt
      C : Char -> Variant g TyChar

      -- Variants & Accessors
      Tag : {kvs : Vect (S n) (Pair String Ty)}
         -> (label : String)
         -> (value : Variant g ty)
         -> (prf   : Elem (label, ty) kvs)
                  -> Variant g (TyVariant kvs)

      Match : {kvs : Vect (S n) (Pair String Ty)}
           -> {b : Ty}
           -> (value : Variant g (TyVariant kvs))
           -> (cases : Cases   g            kvs   b)
                    -> Variant g                  b


namespace Renaming
  public export
  weaken : forall type
         . (Contains  old           type -> Contains  new           type)
        -> (Contains (old += type') type -> Contains (new += type') type)

  weaken func Here         = Here
  weaken func (There rest) = There (func rest)

  mutual
    namespace Case

      public export
      rename : (forall type . Contains old type -> Contains new type)
            -> (forall type, body . Case old label type body
                                 -> Case new label type body)
      rename f (MkCase label branch)
        = MkCase label (rename (weaken f) branch)

    namespace Cases
      public export
      rename : (forall type . Contains (old) type -> Contains (new) type)
            -> (forall types, type . Cases old types type
                                  -> Cases new types type)
      rename f (Singleton branch)
        = Singleton (Case.rename f branch)
      rename f (Extend branch rest)
        = Extend (Case.rename f branch) (rename f rest)

    public export
    rename : (forall type . Contains old type -> Contains new type)
          -> (forall type . Variant  old type -> Variant  new type)
    -- Let-Bindings & Variables
    rename f (Var x) = Var (f x)
    rename f (Let this beInThis)
      = Let (rename f this)
            (rename (weaken f) beInThis)

    -- Base Variables
    rename f (I x) = I x
    rename f (C x) = C x

    -- Variants & Accesors
    rename f (Tag label value prf) = Tag label (rename f value) prf
    rename f (Match value cases) = Match (rename f value)
                                         (Cases.rename f cases)


namespace Substitution
  public export
  weakens : forall old, new
          . (f : forall type
               . Contains old type
              -> Variant  new type)
         -> (forall type . Contains (old += type') type
                        -> Variant  (new += type') type)
  weakens f Here         = Var Here
  weakens f (There rest) = rename There (f rest)

  namespace General
    mutual
      namespace Case
        public export
        subst : (f : forall type
                   . Contains old type
                  -> Variant  new type)
             -> (forall type, body . Case old label type body
                                  -> Case new label type body)
        subst f (MkCase label branch)
          = MkCase label (subst (weakens f) branch)

      namespace Cases
        public export
        subst : (f : forall type
                   . Contains old type
                  -> Variant new type)
             -> (forall types, type . Cases old types type
                                   -> Cases new types type)
        subst f (Singleton branch)
          = Singleton (Case.subst f branch)
        subst f (Extend branch rest)
          = Extend (Case.subst f branch) (subst f rest)


      public export
      subst : (forall type . Contains old type -> Variant new type)
           -> (forall type . Variant  old type -> Variant new type)
      -- Let-Bindings & Variables
      subst f (Var x) = f x
      subst f (Let this beInThis)
        = Let (subst f this) (subst (weakens f) beInThis)

      -- Base Values
      subst f (I x) = I x
      subst f (C x) = C x

      -- Variants & Accessors
      subst f (Tag label value prf)
        = Tag label (subst f value) prf
      subst f (Match value cases)
        = Match (subst f value) (subst f cases)

  namespace Single
    public export
    apply : (this : Variant ctxt typeB)
         -> (idx  : Contains (ctxt += typeB) typeA)
                 -> Variant ctxt typeA
    apply this Here         = this
    apply this (There rest) = Var rest

    public export
    subst : (this   : Variant  ctxt           typeB)
         -> (inThis : Variant (ctxt += typeB) typeA)
                   -> Variant  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis
       = General.subst (apply this) inThis


namespace Values

  public export
  data Value : Variant ctxt type -> Type where
    -- Base Values
    IV : Value (I i)
    CV : Value (C c)

    -- Variants
    MkTagV : {kvs    : Vect (S n) (Pair String Ty)}
          -> {value' : Variant Nil type}
          -> (value  : Value value')
          -> {prf    : Elem (label, type) kvs}
                    -> Value (Tag label value' prf)


namespace Reduction

  namespace Cases
    public export
    data Redux : (value  : Variant g type)
              -> (cases  : Cases g kvs body)
              -> (idx    : Elem (label, type) kvs)
              -> (result : Variant g body)
              -> Type
      where
        ReduceSingleton : {value : Variant g type}
                                -> Value value
                                -> Redux value
                                         (Singleton (MkCase label branch))
                                         Here
                                         (subst value branch)
        ReduceExtend : {value : Variant g type}
                    -> {rest  : Cases g kvs body}
                    -> Value value
                    -> Redux value
                             (Extend (MkCase label branch) rest)
                             Here
                             (Single.subst value branch)
        SkipThis : Redux value rest later result
                -> Redux value
                         (Extend branch rest)
                         (There later)
                         result

  public export
  data Redux : (this, that : Variant ctxt type) -> Type where
    -- Let Bindings
    SimplifyLetValue : Redux this that
                    -> Redux (Let this body)
                             (Let that body)
    ReduceLetBody : Value value
                 -> Redux (Let value body)
                          (subst value body)

    -- Variants & Accessors
    SimplifyTag : {kvs   : Vect (S n) (Pair String Ty)}
               -> {prf   : Elem (label, type) kvs}
               -> (redux : Redux this that)
                        -> Redux (Tag label this prf) (Tag label that prf)

    SimplifyMatchCase : {cases : Cases _ kvs type}
                     -> (redux : Redux this that)
                              -> Redux (Match this cases) (Match that cases)

    ReduceCases : {kvs   : Vect (S n) (Pair String Ty)}
               -> {idx   : Elem (label, type') kvs}
               -> {value : Variant g type'}
               -> {this  : Cases g kvs type}
               -> {that  : Variant g type}
               -> (prf   : Value value)
               -> (redux : Redux value this idx that)
                        -> Redux (Match (Tag label value idx) this)
                                 that


namespace Progress

  public export
  data Progress : (term : Variant Nil type)
                       -> Type
    where
      Done : {term  : Variant Nil type}
          -> (value : Value term)
                   -> Progress term

      Step : {type       : Ty}
          -> {this, that : Variant Nil type}
          -> (step       : Redux this that)
                        -> Progress this

  namespace Cases
    public export
    data Progress : (label : String)
                 -> (value : Variant Nil type)
                 -> (idx   : Elem (label, type) kvs)
                 -> (term  : Cases Nil kvs body)
                 -> Type
      where
        Step : {value : Variant Nil type'}
            -> {idx   : Elem (label, type') kvs}
            -> {cases : Cases Nil kvs type}
            -> {that  : Variant Nil type}
            -> (step  : Redux value cases idx that)
                    -> Progress label value idx cases
  mutual
    namespace Cases
      public export
      progress : {value' : Variant Nil type}
              -> (idx    : Elem (label, type) kvs)
              -> (value  : Value value')
              -> (term   : Cases Nil kvs body)
                        -> Progress label value' idx term
      progress Here value (Singleton (MkCase label branch))
        = Step (ReduceSingleton value)
      progress Here value (Extend (MkCase label branch) rest)
        = Step (ReduceExtend value)
      progress (There later) value (Extend branch rest) with (progress later value rest)
        progress (There later) value (Extend branch rest) | Step step
          = Step (SkipThis step)



    public export
    progress : forall type . (term : Variant Nil type) -> Progress term
    -- Let-Bindings & Variables
    progress (Var _) impossible

    progress (Let this beInThis) with (progress this)
      progress (Let this beInThis) | (Done value) = Step (ReduceLetBody value)
      progress (Let this beInThis) | (Step step) = Step (SimplifyLetValue step)

    -- Base Values
    progress (I x) = Done IV
    progress (C x) = Done CV

    -- Variants & Accessors
    progress (Tag label value prf) with (progress value)
      progress (Tag label value prf) | (Done value') = Done (MkTagV value')
      progress (Tag label value prf) | (Step step) = Step (SimplifyTag step)

    progress (Match value cases) with (progress value)
      progress (Match (Tag label value' prf) cases) | (Done (MkTagV x)) with (progress prf x cases)
        progress (Match (Tag label value' prf) cases) | (Done (MkTagV x)) | (Step step)
          = Step (ReduceCases x step)
      progress (Match value cases) | (Step step) = Step (SimplifyMatchCase step)


namespace Evaluation

  public export
  data Reduces : (this : Variant ctxt type)
              -> (that : Variant ctxt type)
              -> Type
    where
      Refl  : {this : Variant ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : Variant ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : Variant ctxt type)
                       -> Type
    where
      Normalised : {term : Variant ctxt type}
                -> (this : Value term)
                        -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : Variant Nil type) -> Type where
    RunEval : {this, that : Variant Nil type}
           -> (steps      : Inf (Reduces this that))
           -> (result     : Finished that)
                         -> Evaluate this

  public export
  data Fuel = Empty | More (Lazy Fuel)

  public export
  covering
  forever : Fuel
  forever = More forever

  public export
  compute : (fuel : Fuel)
         -> (term : Variant Nil type)
                 -> Evaluate term
  compute Empty term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : (this : Variant Nil type)
           -> Maybe (Subset (Variant Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x)) = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing


namespace Examples

  public export
  ici : Variant Nil (TyVariant [("int", TyInt), ("char", TyChar)])
  ici = Tag "int" (I 1) Here

  public export
  icc : Variant Nil (TyVariant [("int", TyInt), ("char", TyChar)])
  icc = Tag "char" (C 'c') (There Here)

  public export
  iciM : Variant Nil TyInt
  iciM = Match ici (Extend (MkCase "int" (Var Here)) (Singleton (MkCase "char" $ I 2)))

  public export
  iccM : Variant Nil TyInt
  iccM = Match icc (Extend (MkCase "int" $ Var Here) (Singleton (MkCase "char" $ I 2)))

{-
  public export
  snip : Variant Nil TyInt
  snip = (Match (Tag "int" (I 1) Here) (Extend (MkCase "int" (Var Here))
                                       (Singleton (MkCase "char" (I 2)))))
-}
