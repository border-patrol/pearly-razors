||| An expression language with mechanical proof of type-safety.
|||
||| `Recorded` is an expression language supporting Let-bindings, and
||| Records i.e. Named Tuples.  Standard constructions are used to
||| represent the language as an EDSL, together with proof of progress
||| taken from PLFA Part 2.
|||
||| This module represents Section 3 of the Functional Pearl.
|||
module Razor.Recorded

import Razor.Common

%default total

namespace Types

  public export
  data Ty = TyInt
          | TyChar
          | TyRecord (Vect (S n) (Pair String Ty))

namespace Terms

  mutual
    ||| Field in a record.
    public export
    data Field : (g : List Ty)
              -> (label : String)
              -> (type  : Ty)
              -> Type
      where
        MkField : (label : String)
               -> (value : Recorded g type)
                        -> Field g label type

    ||| Record Fields.
    public export
    data Fields : (g : List Ty)
               -> (types : Vect (S n) (Pair String Ty))
               -> Type
      where
        Singleton : (first : Field  g   label ty)
                          -> Fields g ((label,ty)::Nil)

        Extend : (next : Field  g   label  ty)
              -> (rest : Fields g               tys)
                      -> Fields g ((label, ty)::tys)

    public export
    data Recorded : List Ty -> Ty -> Type where
          -- Let-Bindings & Variables
          Var : Elem ty g -> Recorded g ty

          Let : {expr, body : Ty}
             -> (this     : Recorded        g  expr)
             -> (beInThis : Recorded (expr::g) body)
                         -> Recorded        g  body

          -- Base Values
          I : Int  -> Recorded g TyInt
          C : Char -> Recorded g TyChar

          -- Records & Accessors
          MkRecord : {types  : Vect (S n) (Pair String Ty)}
                  -> (values : Fields   g           types)
                            -> Recorded g (TyRecord types)

          Proj : {type : Ty}
              -> {types : Vect (S n) (Pair String Ty)}
              -> (rec   : Recorded g (TyRecord types))
              -> (label : String)
              -> (idx   : Elem (label, type) types)
                       -> Recorded g type

  public export
  index : (idx    : Elem (label, type) types)
       -> (fields : Fields g types)
       -> Recorded g type
  index Here (Singleton (MkField label value)) = value
  index Here (Extend (MkField label value) rest) = value
  index (There later) (Extend next rest) = index later rest

namespace Renaming

  public export
  weaken : (Contains  old           type -> Contains  new           type)
        -> (Contains (old += type') type -> Contains (new += type') type)

  weaken func Here         = Here
  weaken func (There rest) = There (func rest)

  mutual
    namespace Fields
      public export
      rename : (forall type  . Contains old type  -> Contains new type)
            -> (forall types . Fields   old types -> Fields   new types)
      rename f (Singleton (MkField label first))
        = Singleton (MkField label (rename f first))
      rename f (Extend (MkField label next) rest)
        = Extend (MkField label (rename f next)) (rename f rest)

    public export
    rename : (forall type . Contains old type -> Contains new type)
          -> (forall type . Recorded old type -> Recorded new type)
    -- Let-Bindings & Variables
    rename f (Var x) = Var (f x)
    rename f (Let this beInThis)
      = Let (rename f this)
            (rename (weaken f) beInThis)

    -- Base Values
    rename f (I x) = I x
    rename f (C x) = C x

    -- Records & Accessors
    rename f (MkRecord values) = MkRecord (rename f values)
    rename f (Proj rec label idx) = Proj (rename f rec) label idx

namespace Substitution
  public export
  weakens : (forall type . Contains  old type
                        -> Recorded  new type)
         -> (forall type . Contains (old += type') type
                        -> Recorded (new += type') type)
  weakens f Here         = Var Here
  weakens f (There rest) = rename There (f rest)

  namespace General
    mutual
      namespace Fields
        public export
        subst : (f : forall type  . Contains old type  -> Recorded new type)
                 -> (forall types . Fields   old types -> Fields   new types)
        subst f (Singleton (MkField label first))
          = Singleton (MkField label (subst f first))
        subst f (Extend (MkField label next) rest)
          = Extend (MkField label (subst f next)) (subst f rest)

      public export
      subst : (forall type . Contains old type -> Recorded new type)
           -> (forall type . Recorded old type -> Recorded new type)
      -- Let-Bindings & Variables
      subst f (Var x) =  f x
      subst f (Let this beInThis)
        = Let (subst f this)
              (subst (weakens f) beInThis)

      -- Base Values
      subst f (I x) = I x
      subst f (C x) = C x

      -- Records & Accesors
      subst f (MkRecord values) = MkRecord (subst f values)
      subst f (Proj rec label idx) = Proj (subst f rec) label idx

  namespace Single
    public export
    apply : (this : Recorded  ctxt           typeB)
         -> (idx  : Contains (ctxt += typeB) typeA)
                 -> Recorded  ctxt           typeA
    apply this Here         = this
    apply this (There rest) = Var rest

    public export
    subst : (this   : Recorded  ctxt           typeB)
         -> (inThis : Recorded (ctxt += typeB) typeA)
                   -> Recorded  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis
      = General.subst (apply this) inThis


namespace Values
  mutual
    namespace Field
      public export
      data Value : (field  : Field g label type) -> Type
        where
          MkFieldV : (prf : Value v)
                         -> Value (MkField label v)

    namespace Fields
      public export
      data Value : (fields : Fields g types) -> Type
        where
          SingletonV : (field : Value value)
                             -> Value (Singleton value)

          ExtendV : {value  : Field g label type}
                 -> {values : Fields g types}
                 -> (next   : Value value)
                 -> (rest   : Value values)
                           -> Value (Extend value values)

    public export
    data Value : Recorded ctxt type -> Type where
      -- Base Values
      IV : Value (I i)
      CV : Value (C c)

      -- Records
      MkRecordV : Value fields -> Value (MkRecord fields)


namespace Reduction

  mutual
    namespace Field
      public export
      data Redux : (this, that : Field ctxt label type) -> Type
        where
          SimplifyField : {label      : String}
                       -> {this, that : Recorded g type}
                       -> (prf        : Redux this that)
                                     -> Redux (MkField label this)
                                              (MkField label that)

    namespace Fields
      public export
      data Redux : (this, that : Terms.Fields g types) -> Type
        where
          SimplifySingleton : (prf : Redux this that)
                                  -> Redux (Singleton this)
                                           (Singleton that)

          SimplifyExtend : {this, that : Field g label type}
                        -> {rest       : Fields g types}
                        -> (prf        : Redux this that)
                                      -> Redux (Extend this rest)
                                               (Extend that rest)

          SimplifyExtendV : {this, that : Fields ctxt types}
                         -> {v          : Field ctxt label type}
                         -> (value      : Value v)
                         -> (rest       : Redux this that)
                                       -> Redux (Extend v this)
                                                (Extend v that)


    public export
    data Redux : (this, that : Recorded ctxt type) -> Type where
      -- Let Bindings
      SimplifyLetValue : Redux this that
                      -> Redux (Let this body)
                               (Let that body)
      ReduceLetBody : Value value
                   -> Redux (Let value body)
                            (subst value body)

      SimplifyRecord : Redux this that
                    -> Redux (MkRecord this) (MkRecord that)


      -- Accessors
      SimplifyProj : {type       : Ty}
                  -> {labels     : Vect (S n) (Pair String Ty)}
                  -> {this, that : Recorded g (TyRecord labels)}
                  -> {idx        : Elem (label,type) labels}
                                -> Redux this that
                                -> Redux (Proj this label idx) (Proj that label idx)

      ReduceProj : {type   : Ty}
                -> {label  : String}
                -> {types  : Vect (S n) (Pair String Ty)}
                -> {fields : Fields g types}
                -> {idx    : Elem (label,type) types}
                -> (values : Value fields)
                          -> Redux (Proj (MkRecord fields) label idx)
                                   (index idx fields)

namespace Progress

  public export
  data Progress : (term : Recorded Nil type)
                       -> Type
    where
      Done : {term : Recorded Nil type} -> Value term -> Progress term
      Step : {type : Ty}
          -> {this, that : Recorded Nil type}
          -> (step  : Redux this that)
                   -> Progress this

  namespace Field
    public export
    data Progress : (field : Field Nil label type) -> Type where
      Done : Value field -> Progress field
      Step : {this, that : Field Nil label type}
          -> (step       : Redux this that)
                        -> Progress this

  namespace Fields
    public export
    data Progress : (fields : Fields Nil types) -> Type where
      Done :  (value : Value fields) -> Progress fields

      Step : {this, that : Fields Nil types}
          -> (step       : Redux this that)
                        -> Progress this


  mutual
    namespace Field
      public export
      progress : (field : Field Nil label type)
              -> Progress field
      progress (MkField label value) with (progress value)
        progress(MkField label value) | (Done v)
          = Done (MkFieldV v)
        progress(MkField label value) | (Step step)
          = Step (SimplifyField step)

    namespace Fields
      public export
      progress : (fields : Fields Nil types)
              -> Progress fields
      progress (Singleton first) with (Field.progress first)
        progress (Singleton first) | (Done x) = Done (SingletonV x)
        progress (Singleton first) | (Step prf)
          = Step (SimplifySingleton prf)


      progress (Extend next rest) with (progress next)
        progress (Extend next rest) | (Done x) with (progress rest)
          progress (Extend next rest) | (Done x) | (Done xs)
            = Done (ExtendV x xs)
          progress (Extend next rest) | (Done x) | (Step prf)
            = Step (SimplifyExtendV x prf)

        progress (Extend next rest) | (Step prf) = Step (SimplifyExtend prf)

    public export
    progress : forall type . (term : Recorded Nil type) -> Progress term
    -- Let-Bindings & Variables
    progress (Var _) impossible
    progress (Let this beInThis) with (progress this)
      progress (Let this beInThis) | (Done x)
        = Step (ReduceLetBody x)
      progress (Let this beInThis) | (Step prf)
        = Step (SimplifyLetValue prf)

    -- Base Values
    progress (I x) = Done IV
    progress (C x) = Done CV

    -- Records & Accessors
    progress (MkRecord values) with (progress values)
      progress (MkRecord values) | (Done v)   = Done (MkRecordV v)
      progress (MkRecord values) | (Step prf) = Step (SimplifyRecord prf)

    progress (Proj rec label idx) with (progress rec)
      progress (Proj (MkRecord fields) label idx) | (Done (MkRecordV fieldsV))
        = Step (ReduceProj fieldsV)
      progress (Proj rec label idx) | (Step prf)
        = Step (SimplifyProj prf)

namespace Evaluation

  public export
  data Reduces : (this : Recorded ctxt type)
              -> (that : Recorded ctxt type)
                      -> Type
    where
      Refl  : {this : Recorded ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : Recorded ctxt type}
                              -> Redux this that
                              -> Reduces that end
                              -> Reduces this end

  public export
  data Finished : (term : Recorded ctxt type)
                       -> Type
    where
      Normalised : {term : Recorded ctxt type} -> Value term -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : Recorded Nil type) -> Type where
    RunEval : {this, that : Recorded Nil type}
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
         -> (term : Recorded Nil type)
                 -> Evaluate term
  compute Empty term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : (this : Recorded Nil type)
           -> Maybe (Subset (Recorded Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing


namespace Examples

  public export
  pairIC : Recorded Nil (TyRecord [("first", TyInt), ("second", TyChar)])
  pairIC = MkRecord (Extend    (MkField "first"  (I 1))
                    (Singleton (MkField "second" (C 'c'))))

  public export
  i : Recorded Nil TyInt
  i = Proj pairIC "first" Here

  public export
  c : Recorded Nil TyChar
  c = Proj pairIC "second" (There Here)
