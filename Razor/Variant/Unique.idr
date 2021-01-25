||| An expression language with mechanical proof of type-safety.
|||
||| `Variant` is an expression language supporting Let-bindings, and
||| type safe variants.  Standard constructions are used to
||| represent the language as an EDSL, together with proof of progress
||| taken from PLFA Part 2.
|||
||| This module compliments Section 4.3 of the Functional Pearl.
|||
||| Although the code appears to be total, there is a known issues
||| with Idris2 totality checker that causes it to slow down when
||| dealing with mutually defined terms.
|||
module Razor.Variant.Unique

import Razor.Common

%default covering

namespace Types

  public export
  data Level = TYPE | VALUE

  public export
  data Ty : Level -> Type where
    TyInt  : Ty VALUE
    TyChar : Ty VALUE
    TyVariant : (fields : Vect (S n) (Pair String (Ty VALUE))) -> Ty VALUE

    TyVariantDecl : (fields : Vect (S n) (Pair String (Ty VALUE))) -> Ty TYPE

namespace Context
  public export
  Context : List Level -> Type
  Context = DList Level Ty

  public export
  Elem : {level : Level}
      -> {levels : List Level}
      -> (ctxt : Context levels)
      -> (type : Ty level)
      -> Type
  Elem ctxt type = Elem Level Ty type ctxt

namespace Terms
  mutual

    namespace Patterns
      public export
      data Case : (ctxt  : Context levels)
               -> (label : String)
               -> (type  : Ty VALUE)
               -> (body  : Ty VALUE)
               -> Type
        where
          MkCase : {type, body : Ty VALUE}
                -> (label  : String)
                -> (branch : Variant (ctxt +=    type) body)
                          -> Case     ctxt label type  body

      public export
      data Cases : (ctxt  : Context levels)
                -> (types : Vect (S n) (Pair String (Ty VALUE)))
                -> (body  : Ty VALUE)
                -> Type
        where
            Singleton : {type, body : Ty VALUE}
                     -> (branch : Case  ctxt   label  type   body)
                               -> Cases ctxt [(label, type)] body

            Extend : {type, body : Ty VALUE}
                  -> (branch : Case ctxt   label  type          body)
                  -> (rest   : Cases ctxt                   kvs  body)
                            -> Cases ctxt ((label, type) :: kvs) body

    namespace Delcarations
      public export
      data Field : (ctxt  : Context levels)
                -> (label : String)
                -> (type  : Ty VALUE)
                -> Type
        where
          MkField : {type' : Ty VALUE}
                 -> (label : String)
                 -> (desc  : Variant ctxt type')
                          -> Field ctxt label type'
          MkPrim : (label : String)
                -> (type' : Ty VALUE)
                         -> Field ctxt label type'

      public export
      data Fields : (ctxt : Context levels)
                 -> (kvs  : Vect (S n) (Pair String (Ty VALUE)))
                 -> Type
        where
          Singleton : (field : Field  ctxt   label  type)
                            -> Fields ctxt [(label, type)]

          Extend : (field : Field ctxt             label  type)
                -> (rest  : Fields ctxt  fields)
                         -> Fields ctxt (fields += (label, type))


    public export
    data Variant : forall lvls, lvl . Context lvls -> Ty lvl -> Type where
      -- Let-Bindings & Variables
      Var : Elem g ty -> Variant g ty

      Let : {expr : Ty levelE}
         -> {body : Ty levelB}
         -> (this     : Variant        g  expr)
         -> (beInThis : Variant (expr::g) body)
                     -> Variant        g  body

      -- Base Values
      I : Int -> Variant g TyInt
      C : Char -> Variant g TyChar

      -- Variant Type Constructors
      VariantTy : {kvs : Vect (S n) (Pair String (Ty VALUE))}
               -> (fields : Fields   g                kvs)
                         -> Variant  g (TyVariantDecl kvs)

      -- Variant Value Constructors
      Tag : {ty : Ty VALUE}
         -> {kvs : Vect (S n) (Pair String (Ty VALUE))}
         -> (label : String)
         -> (value : Variant g ty)
         -> (type  : Variant g (TyVariantDecl kvs))
         -> (prf   : Elem (label, ty)         kvs)
                  -> Variant g (TyVariant     kvs)

      -- Variant Matching
      Match : {kvs : Vect (S n) (Pair String (Ty VALUE))}
           -> {b : Ty VALUE}
           -> (value : Variant g (TyVariant kvs))
           -> (cases : Cases   g            kvs   b)
                    -> Variant g                  b


namespace Renaming

  public export
  weaken : (f : Context.Elem old type
             -> Context.Elem new type)
        -> (Context.Elem (old += type') type
         -> Context.Elem (new += type') type)
  weaken func Here = Here
  weaken func (There rest) = There (func rest)

  mutual
    namespace Case

      public export
      rename : forall levelsO, levelsN
             . {old : Context levelsO}
            -> {new : Context levelsN}
            -> (forall level . {type : Ty level}
                            -> Context.Elem old type
                            -> Context.Elem new type)

            -> ({type, body : Ty VALUE} -> Case old label type body
                                      -> Case new label type body)
      rename f (MkCase label branch)
        = MkCase label (rename (weaken f) branch)

    namespace Cases
      public export
      rename : forall levelsO, levelsN
             . {old : Context levelsO}
            -> {new : Context levelsN}
            -> (f : forall level
                  . {type : Ty level}
                          -> Context.Elem old type
                          -> Context.Elem new type)

            -> (forall types . Cases old types type
                            -> Cases new types type)

      rename f (Singleton branch)
        = Singleton (Case.rename f branch)
      rename f (Extend branch rest)
        = Extend (Case.rename f branch) (rename f rest)


    namespace Fields
      public export
      rename : forall levelsO, levelsN
             . {old : Context levelsO}
            -> {new : Context levelsN}
            -> (f : forall level . {type : Ty level}
                                 -> Context.Elem old type
                                 -> Context.Elem new type)
            -> (forall types . Fields old types
                            -> Fields new types)

      rename f (Singleton (MkField label first))
        = Singleton (MkField label (rename f first))
      rename f (Singleton (MkPrim label first))
        = Singleton (MkPrim label first)

      rename f (Extend (MkPrim label next) rest)
        = Extend (MkPrim label next) (rename f rest)
      rename f (Extend (MkField label next) rest)
        = Extend (MkField label (rename f next)) (rename f rest)


    public export
    rename : forall levelsO, levelsN
           . {old : Context levelsO}
          -> {new : Context levelsN}
          -> (f : forall level . {type : Ty level}
                              -> Elem old type
                              -> Elem new type)
          -> (forall level . {type : Ty level}
                           -> Variant old type
                           -> Variant new type)
    -- Let Binding & Variables
    rename f (Var x) = Var (f x)
    rename f (Let this beInThis)
      = Let (rename f this) (rename (weaken f) beInThis)

    -- Base Values
    rename f (I x) = I x
    rename f (C x) = C x

    -- Variant Type Constructors
    rename f (VariantTy fields) = VariantTy (rename f fields)

    -- Variant Value Constructors
    rename f (Tag label value type prf)
      = Tag label (rename f value) (rename f type) prf

    -- Variant Matching
    rename f (Match value cases)
      = Match (rename f value) (rename f cases)


namespace Substitution

  public export
  weakens : forall levelsO, levelsN
          . {old   : Context levelsO}
         -> {new   : Context levelsN}
         -> {type  : Ty level}
         -> {type' : Ty level'}
         -> (f     : Elem    old type
                  -> Variant new type)
                  -> (Elem   (old += type') type
                  -> Variant (new += type') type)
  weakens func Here        = Var Here
  weakens func (There rest) = rename There (func rest)


  namespace General
    mutual
      namespace Fields
        public export
        subst : forall levelsO, levelsN
              . {old : Context levelsO}
             -> {new : Context levelsN}
             -> (f : forall level
                    . {type : Ty level}
                    -> Elem    old type
                    -> Variant new type)

             -> (forall types . Fields old types
                             -> Fields new types)

        subst f (Singleton (MkField label desc))
          = Singleton (MkField label (subst f desc))
        subst f (Singleton (MkPrim  label desc))
          = Singleton (MkPrim label desc)
        subst f (Extend (MkField label desc) rest)
          = Extend (MkField label (subst f desc)) (subst f rest)
        subst f (Extend (MkPrim label desc) rest)
          = Extend (MkPrim label desc) (subst f rest)


      namespace Case
        public export
        subst : forall levelsO, levelsN
              . {old : Context levelsO}
             -> {new : Context levelsN}
             -> (f : forall level
                   . {type : Ty level}
                   -> Elem    old type
                   -> Variant new type)
             -> ({type, body : Ty VALUE} -> Case old label type body
                                         -> Case new label type body)
        subst f (MkCase label branch)
          = MkCase label (subst (weakens f) branch)

      namespace Cases
        public export
        subst : forall levelsO, levelsN
              . {old : Context levelsO}
             -> {new : Context levelsN}
             -> (f : forall level
                   . {type : Ty level}
                   -> Elem    old type
                   -> Variant new type)
             -> (forall types . Cases old types type
                             -> Cases new types type)
        subst f (Singleton branch) =
          Singleton (Case.subst f branch)
        subst f (Extend branch rest)
          = Extend (Case.subst f branch) (subst f rest)

      public export
      subst : forall levelsO, levelsN
            . {old : Context levelsO}
           -> {new : Context levelsN}
           -> (f : forall level
                 . {type : Ty level}
                 -> Elem    old type
                 -> Variant new type)
           -> (forall level . {type : Ty level}
                            -> Variant old type
                            -> Variant new type)
      -- Let-Binding & Variables
      subst f (Var x) = f x
      subst f (Let this beInThis)
        = Let (subst f this)
              (subst (weakens f) beInThis)

      -- Base Values
      subst f (I x) = I x
      subst f (C x) = C x

      -- Variant Type Constructors
      subst f (VariantTy fields)
        = VariantTy (subst f fields)

      -- Variant Value Constructors
      subst f (Tag label value type prf)
        = Tag label (subst f value) (subst f type) prf

      -- Variant Matching
      subst f (Match value cases)
        = Match (subst f value) (subst f cases)


  namespace Single
    public export
    apply : forall levelA, levelB
          . {typeA  : Ty levelA}
         -> {typeB  : Ty levelB}
         -> (this   : Variant  ctxt           typeB)
         -> (idx    : Elem    (ctxt += typeB) typeA)
                   -> Variant  ctxt           typeA
    apply this Here         = this
    apply this (There rest) = Var rest

    public export
    subst : forall levelA, levelB
         .  {typeA  : Ty levelA}
         -> {typeB  : Ty levelB}
         -> {ctxt   : Context lvls}
         -> (this   : Variant  ctxt           typeB)
         -> (inThis : Variant (ctxt += typeB) typeA)
                   -> Variant  ctxt           typeA
    subst this inThis = General.subst (Single.apply this) inThis


namespace Values
  mutual
    namespace Field
      public export
      data Value : (field : Field g label type) -> Type where
          MkFieldV : (prf : Value field)
                         -> Value (MkField label field)

          MkPrimV : Value (MkPrim label type)

    namespace Fields
      public export
      data Value : (fields : Fields g types) -> Type where
          SingletonV : {field : Field g label type}
                    -> (prf   : Value field)
                             -> Value (Singleton field)

          ExtendV : {field  : Field  g label type}
                 -> {fields : Fields g kvs}
                 -> (prf    : Field.Value field)
                 -> (rest   : Fields.Value fields)
                           -> Value (Extend field fields)
    public export
    data Value : Variant ctxt type -> Type where
      -- Base Values
      IV : Value (I i)
      CV : Value (C c)


      -- Variant Type Constructors
      VariantTyV : Value fields
                -> Value (VariantTy fields)

      -- Variant Value Constructors
      TagV : {kvs    : Vect (S n) (Pair String (Ty VALUE))}
          -> {mtype  : Ty VALUE}
          -> {value  : Variant g mtype}
          -> {type   : Variant g (TyVariantDecl kvs)}
          -> (prfV   : Value value)
          -> (prfT   : Value type)
          -> {idx    : Elem (label, mtype) kvs}
                    -> Value (Tag label value type idx)

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
                    -> {rest : Cases g kvs body}
                    -> Value value
                    -> Redux value
                             (Extend (MkCase label branch) rest)
                             Here
                             (subst value branch)
        SkipThis : Redux value rest later result
                -> Redux value
                         (Extend branch rest)
                         (There later)
                         result

  mutual
    namespace Field
      public export
      data Redux : (this, that : Field ctxt label type) -> Type where
          SimplifyField : {label : String}
                       -> {this, that : Variant g type}
                       -> (prf : Redux this that)
                       -> Redux (MkField label this) (MkField label that)

    namespace Fields
      public export
      data Redux : (this, that : Fields g types) -> Type where
          SimplifySingleton : {this, that : Field g label type}
                           -> (prf : Redux this that)
                                  -> Redux (Singleton this) (Singleton that)

          SimplifyExtendValue : {this, that : Field  g label type}
                             -> {rest       : Fields g types}
                             -> (prf        : Redux this that)
                                           -> Redux (Extend this rest)
                                                    (Extend that rest)

          SimplifyExtendRest : {this, that : Fields ctxt types}
                            -> {field      : Field ctxt label type}
                            -> (value      : Field.Value field)
                            -> (rest       : Redux this that)
                                          -> Redux (Extend field this)
                                                   (Extend field that)

    public export
    data Redux : (this, that : Variant ctxt type) -> Type where
      -- Let Bindings
      SimplifyLetValue : {this, that : Variant  ctxt typeV}
                      -> {body       : Variant (ctxt += typeV) typeB}
                      -> (redux      : Redux this that)
                                    -> Redux (Let this body)
                                             (Let that body)

      ReduceLetBody : {value : Variant ctxt typeV}
                   -> {body  : Variant (ctxt += typeV) typeB}
                   -> (prfV  : Value value)
                            -> Redux (Let value body)
                                    (subst value body)

      -- Variant Type Constructors
      SimplifyVariantTy : Redux this that
                       -> Redux (VariantTy this)
                                (VariantTy that)

      -- Variant Value Constructors
      SimplifyTagType : {kvs        : Vect (S n) (Pair String (Ty VALUE))}
                     -> {this, that : Variant ctxt (TyVariantDecl kvs)}
                     -> {value      : Variant ctxt type'}
                     -> {idx        : Elem (label, type') kvs}
                     -> (redux      : Redux this that)
                                   -> Redux (Tag label value this idx)
                                            (Tag label value that idx)

      SimplifyTagValue : {kvs        : Vect (S n) (Pair String (Ty VALUE))}
                      -> {this, that : Variant ctxt type'}
                      -> {type       : Variant ctxt (TyVariantDecl kvs)}
                      -> {idx        : Elem (label, type') kvs}
                      -> (prfT       : Value type)
                      -> (redux      : Redux this that)
                                    -> Redux (Tag label this type idx)
                                             (Tag label that type idx)

      -- Variant Matching
      SimplifyMatchCase : {cases : Cases ctxt kvs type}
                       -> (redux : Redux this that)
                                -> Redux (Match this cases) (Match that cases)

      ReduceCases : {kvs   : Vect (S n) (Pair String (Ty VALUE))}
                 -> {idx   : Elem (label, typeV) kvs}
                 -> {value : Variant g typeV}
                 -> {type  : Variant g (TyVariantDecl kvs)}
                 -> {body  : Ty VALUE}
                 -> {this  : Cases g kvs body}
                 -> {that  : Variant g body}
                 -> (prfV   : Value value)
                 -> (prfT   : Value type)
                 -> (redux : Redux value this idx that)
                          -> Redux (Match (Tag label value type idx) this)
                                   that

namespace Progress

  public export
  data Progress : (term : Variant Nil type)
               -> Type
    where
      Done : {term  : Variant Nil type}
          -> (value : Value term)
                   -> Progress term
      Step : {this, that : Variant Nil type}
          -> (step       : Redux this that)
                        -> Progress this

  namespace Field
    public export
    data Progress : (field : Field Nil label type) -> Type where
      Done : (value : Value field) -> Progress field

      Step : {this, that : Field Nil label type}
          -> (step       : Redux this that)
                        -> Progress this

  namespace Fields
    public export
    data Progress : (fields : Fields Nil types) -> Type where
      Done :  (value : Value fields) -> Progress fields

      Step : {this,that : Fields Nil types}
          -> (step      : Redux this that)
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

  -- The body is defined later on.
  public export
  progress : (term : Variant Nil type) -> Progress term

  mutual
    namespace Field
      public export
      progress : (field : Field Nil label type) -> Progress field
      progress (MkPrim label desc) = Done (MkPrimV)
      progress (MkField label desc) with (Progress.progress desc)
        progress (MkField label desc) | (Done value) = Done (MkFieldV value)
        progress (MkField label desc) | (Step step) = Step (SimplifyField step)


    namespace Fields
      public export
      progress : (fields : Fields Nil types) -> Progress fields
      progress (Singleton field) with (Field.progress field)
        progress (Singleton field) | (Done value) = Done (SingletonV value)
        progress (Singleton field) | (Step step)  = Step (SimplifySingleton step)

      progress (Extend field rest) with (Field.progress field)
        progress (Extend field rest) | (Done value) with (Fields.progress rest)
          progress (Extend field rest) | (Done value) | (Done values)
            = Done (ExtendV value values)
          progress (Extend field rest) | (Done value) | (Step step)
            = Step (SimplifyExtendRest value step)
        progress (Extend field rest) | (Step step)
         = Step (SimplifyExtendValue step)

    namespace Cases
      public export
      progress : {value' : Variant Nil type}
              -> (idx   : Elem (label, type) kvs)
              -> (value : Value value')
              -> (term  : Cases Nil kvs body)
              -> Progress label value' idx term
      progress Here value (Singleton (MkCase label branch))
        = Step (ReduceSingleton value)

      progress Here value (Extend (MkCase label branch) rest)
        = Step (ReduceExtend value)

      progress (There later) value (Extend branch rest) with (progress later value rest)
        progress (There later) value (Extend branch rest) | (Step step)
          = Step (SkipThis step)

    -- Body of progress from above.

    -- Let-Binding & Variables
    progress (Var _) impossible

    progress (Let this beInThis) with (progress this)
      progress (Let this beInThis) | (Done value) = Step (ReduceLetBody value)
      progress (Let this beInThis) | (Step step) = Step (SimplifyLetValue step)

    -- Base Value
    progress (I x) = Done IV
    progress (C x) = Done CV

    -- Variant Type Constructors
    progress (VariantTy fields) with (Fields.progress fields)
      progress (VariantTy fields) | (Done value) = Done (VariantTyV value)
      progress (VariantTy fields) | (Step step) = Step (SimplifyVariantTy step)

    -- Variant Value Constructors
    progress (Tag label field type prf) with (progress type)
      progress (Tag label field type prf) | (Done valueT) with (progress field)
        progress (Tag label field type prf) | (Done valueT) | (Done valueF)
          = Done (TagV valueF valueT)
        progress (Tag label field type prf) | (Done valueT) | (Step stepF)
          = Step (SimplifyTagValue valueT stepF)
      progress (Tag label field type prf) | (Step step)
        = Step (SimplifyTagType step)

    -- Variant Matching
    progress (Match field cases) with (progress field)
      progress (Match (Tag label value t idx) cases) | (Done (TagV prfV prfT)) with (Cases.progress idx prfV cases)
        progress (Match (Tag label value t idx) cases) | (Done (TagV prfV prfT)) | (Step step)
          = Step (ReduceCases prfV prfT step)

      progress (Match field cases) | (Step step) = Step (SimplifyMatchCase step)

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
                        -> Value term
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
      compute (More fuel) term | (Step step {that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : (this : Variant Nil type)
           -> Maybe (Subset (Variant Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

namespace Example
  public export
  iciTy : Variant Nil (TyVariantDecl [("int", TyInt), ("char", TyChar)])
  iciTy = VariantTy (Extend (MkPrim "int" TyInt) (Singleton (MkPrim "char" TyChar)))

  public export
  ici : Variant Nil (TyVariant [("int", TyInt), ("char", TyChar)])
  ici = Tag "int" (I 1) iciTy (Here)


  public export
  icc : Variant Nil (TyVariant [("int", TyInt), ("char", TyChar)])
  icc = Let iciTy $ Tag "char" (C 'c') (Var Here) (There Here)

  public export
  iciM : Variant Nil TyInt
  iciM = Match ici (Extend            (MkCase "int"  (Var Here))
                           (Singleton (MkCase "char" (I 2))))

  public export
  iccM : Variant Nil TyInt
  iccM = Match icc (Extend            (MkCase "int"  (Var Here))
                           (Singleton (MkCase "char" (I 2))))
