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
    IntTyDesc : Ty TYPE
    IntTy     : Ty VALUE

    CharTyDesc : Ty TYPE
    CharTy     : Ty VALUE

    VariantTyDesc : (fields : Vect (S n) (Ty TYPE))  -> Ty TYPE
    VariantTy     : (fields : Vect (S n) (Ty VALUE)) -> Ty VALUE

  public export
  data TyCheckVariant : (prfTy : (desc : Ty TYPE) -> (type : Ty VALUE) -> Type)
                     -> (fieldsD : Vect (S n) (Ty TYPE))
                     -> (fieldsV : Vect (S n) (Ty VALUE))
                                -> Type
    where
      CheckOne  : (prf : check type value) -> TyCheckVariant check [type] [value]
      CheckRest : (one  : check type value)
               -> (rest : TyCheckVariant check        types          values)
                       -> TyCheckVariant check (type::types) (value::values)


  public export
  data TyCheck : (desc : Ty TYPE)
              -> (type : Ty VALUE)
                      -> Type
    where
      CheckInt  : TyCheck IntTyDesc  IntTy
      CheckChar : TyCheck CharTyDesc CharTy
      CheckVar  : (prf : TyCheckVariant TyCheck types values)
                      -> TyCheck (VariantTyDesc types) (VariantTy values)

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
               -> (type  : Ty VALUE)
               -> (body  : Ty level)
               -> Type
        where
          MkCase : {type : Ty VALUE}
                -> {body : Ty level}
                -> (branch : Variant (ctxt +=    type) body)
                          -> Case     ctxt       type  body

      public export
      data Cases : (ctxt  : Context levels)
                -> (types : Vect (S n) (Ty VALUE))
                -> (body  : Ty level)
                -> Type
        where
            Singleton : {type : Ty VALUE}
                     -> {body : Ty level}
                     -> (branch : Case  ctxt  type   body)
                               -> Cases ctxt [type] body

            Extend :  {type : Ty VALUE}
                   -> {body : Ty level}
                   -> (branch : Case  ctxt   type         body)
                   -> (rest   : Cases ctxt          kvs  body)
                             -> Cases ctxt (type :: kvs) body

    namespace Delcarations
      public export
      data Field : (ctxt  : Context levels)
                -> (type  : Ty TYPE)
                -> Type
        where
          MkField : {type : Ty TYPE}
                 -> (desc : Variant ctxt type)
                         -> Field   ctxt type

      public export
      data Fields : (ctxt : Context levels)
                 -> (kvs  : Vect (S n) (Ty TYPE))
                 -> Type
        where
          Singleton : (field : Field  ctxt  type)
                            -> Fields ctxt [type]

          Extend : (field : Field  ctxt            type)
                -> (rest  : Fields ctxt  fields)
                         -> Fields ctxt (fields += type)


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
      I : Int  -> Variant g IntTy
      C : Char -> Variant g CharTy

      -- Type Constructors
      TyInt  : Variant g IntTyDesc
      TyChar : Variant g CharTyDesc

      TyVariant : {kvs : Vect (S n) (Ty TYPE)}
               -> (fields : Fields   g                kvs)
                         -> Variant  g (VariantTyDesc kvs)

      -- Variant Value Constructors
      Tag : {ty    : Ty VALUE}
         -> {types  : Vect (S n) (Ty TYPE)}
         -> {values : Vect (S n) (Ty VALUE)}
         -> (value : Variant g ty)
         -> (type  : Variant g (VariantTyDesc types))
         -> (chk   : TyCheck   (VariantTyDesc types) (VariantTy values))
         -> (prf   : Elem       ty         values)
                  -> Variant g (VariantTy  values)

      -- Variant Matching
      Match : {values : Vect (S n) (Ty VALUE)}
           -> (value : Variant g (VariantTy values))
           -> (cases : Cases   g            values   b)
                    -> Variant g                     b


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

            -> ({type : Ty VALUE} ->
                {body : Ty level} -> Case old type body
                                  -> Case new type body)
      rename f (MkCase branch)
        = MkCase (rename (weaken f) branch)

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

      rename f (Singleton (MkField first))
        = Singleton (MkField (rename f first))

      rename f (Extend (MkField next) rest)
        = Extend (MkField (rename f next)) (rename f rest)


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

    -- Type Constructors
    rename f (TyInt)  = TyInt
    rename f (TyChar) = TyChar
    rename f (TyVariant fields) = TyVariant (rename f fields)

    -- Variant Value Constructors
    rename f (Tag value type chk prf)
      = Tag (rename f value) (rename f type) chk prf

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

        subst f (Singleton (MkField desc))
          = Singleton (MkField (subst f desc))

        subst f (Extend (MkField desc) rest)
          = Extend (MkField (subst f desc)) (subst f rest)


      namespace Case
        public export
        subst : forall levelsO, levelsN
              . {old : Context levelsO}
             -> {new : Context levelsN}
             -> (f : forall level
                   . {type : Ty level}
                   -> Elem    old type
                   -> Variant new type)
             -> ({type : Ty VALUE} ->
                 {body : Ty level} -> Case old type body
                                   -> Case new type body)
        subst f (MkCase branch)
          = MkCase (subst (weakens f) branch)

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

      -- Type Constructors
      subst f TyInt  = TyInt
      subst f TyChar = TyChar

      subst f (TyVariant fields)
        = TyVariant (subst f fields)

      -- Variant Value Constructors
      subst f (Tag value type chk prf)
        = Tag (subst f value) (subst f type) chk prf

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
      data Value : (field : Field g type) -> Type where
          MkField : (prf : Value field)
                        -> Value (MkField field)

    namespace Fields
      public export
      data Value : (fields : Fields g types) -> Type where
          Singleton : {field : Field g type}
                   -> (prf   : Value field)
                            -> Value (Singleton field)

          Extend : {field  : Field  g type}
                -> {fields : Fields g kvs}
                -> (prf    : Field.Value field)
                -> (rest   : Fields.Value fields)
                          -> Value (Extend field fields)
    public export
    data Value : Variant ctxt type -> Type where
      -- Base Values
      I : Value (I i)
      C : Value (C c)


      -- Type Constructors
      TyInt     : Value TyInt
      TyChar    : Value TyChar

      TyVariant : Value fields
               -> Value (TyVariant fields)


      -- Variant Value Constructors
      Tag : {types  : Vect (S n) (Ty TYPE)}
         -> {type   : Variant g (VariantTyDesc types)}

         -> {values : Vect (S n) (Ty VALUE)}

         -> {chk    : TyCheck (VariantTyDesc types) (VariantTy values)}

         -> {value  : Variant g value_type}

         -> {idx    : Elem value_type values}

         -> (prfT   : Value type)
         -> (prfV   : Value value)

                   -> Value (Tag value type chk idx)


namespace Reduction

  namespace Cases
    public export
    data Redux : (value  : Variant g type)
              -> (cases  : Cases g types body)
              -> (idx    : Elem type types)
              -> (result : Variant g body)
              -> Type
      where
        ReduceSingleton : {value : Variant g type}
                       -> {branch : Variant (type::g) type'}
                       -> Value value
                       -> Redux value
                                (Singleton (MkCase branch))
                                Here
                                (subst value branch)
        ReduceExtend : {value : Variant g type}
                    -> {rest : Cases g types body}
                    -> Value value
                    -> Redux value
                             (Extend (MkCase branch) rest)
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
      data Redux : (this, that : Field ctxt type) -> Type where
          SimplifyField :{this, that : Variant g type}
                       -> (prf : Redux this that)
                       -> Redux (MkField this) (MkField that)

    namespace Fields
      public export
      data Redux : (this, that : Fields g types) -> Type where
          SimplifySingleton : {this, that : Field g type}
                           -> (prf : Redux this that)
                                  -> Redux (Singleton this) (Singleton that)

          SimplifyExtendValue : {this, that : Field  g type}
                             -> {rest       : Fields g types}
                             -> (prf        : Redux this that)
                                           -> Redux (Extend this rest)
                                                    (Extend that rest)

          SimplifyExtendRest : {this, that : Fields ctxt types}
                            -> {field      : Field ctxt type}
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
      SimplifyTyVariant : Redux this that
                       -> Redux (TyVariant this)
                                (TyVariant that)

      -- Variant Value Constructors
      SimplifyTagType : {this, that : Variant ctxt (VariantTyDesc kvs)}
                     -> {value      : Variant ctxt type}
                     -> (redux      : Redux this that)
                                   -> Redux (Tag value this chk idx)
                                            (Tag value that chk idx)

      SimplifyTagValue : {type       : Variant ctxt (VariantTyDesc types)}
                      -> (prfT       : Value type)
                      -> {this, that : Variant ctxt type'}
                      -> (redux      : Redux this that)
                                    -> Redux (Tag this type chk idx)
                                             (Tag that type chk idx)

      -- Variant Matching
      SimplifyMatchCase : {cases : Cases ctxt kvs type}
                       -> (redux : Redux this that)
                                -> Redux (Match this cases) (Match that cases)

      ReduceCases : {value : Variant g type_value}
                 -> {type  : Variant g (VariantTyDesc types)}

                 -> {this  : Cases g kvs body}
                 -> {that  : Variant g body}

                 -> (prfV  : Value value)
                 -> (prfT  : Value type)
                 -> (redux : Redux value this idx that)
                          -> Redux (Match (Tag value type chk idx) this)
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
    data Progress : (field : Field Nil type) -> Type where
      Done : (value : Value field) -> Progress field

      Step : {this, that : Field Nil type}
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
    data Progress : (value : Variant Nil type)
                 -> (idx   : Elem type kvs)
                 -> (term  : Cases Nil kvs body)
                 -> Type
      where
        Step : {value : Variant Nil type'}
            -> {idx   : Elem type' kvs}
            -> {cases : Cases Nil kvs type}
            -> {that  : Variant Nil type}
            -> (step  : Redux value cases idx that)
                     -> Progress value idx cases

  -- The body is defined later on.
  public export
  progress : (term : Variant Nil type) -> Progress term

  mutual
    namespace Field
      public export
      progress : (field : Field Nil type) -> Progress field
      progress (MkField desc) with (Progress.progress desc)
        progress (MkField desc) | (Done value) = Done (MkField value)
        progress (MkField desc) | (Step step) = Step (SimplifyField step)


    namespace Fields
      public export
      progress : (fields : Fields Nil types) -> Progress fields
      progress (Singleton field) with (Field.progress field)
        progress (Singleton field) | (Done value) = Done (Singleton value)
        progress (Singleton field) | (Step step)  = Step (SimplifySingleton step)

      progress (Extend field rest) with (Field.progress field)
        progress (Extend field rest) | (Done value) with (Fields.progress rest)
          progress (Extend field rest) | (Done value) | (Done values)
            = Done (Extend value values)
          progress (Extend field rest) | (Done value) | (Step step)
            = Step (SimplifyExtendRest value step)
        progress (Extend field rest) | (Step step)
         = Step (SimplifyExtendValue step)

    namespace Cases
      public export
      progress : {value' : Variant Nil type}
              -> (idx   : Elem type kvs)
              -> (value : Value value')
              -> (term  : Cases Nil kvs body)
              -> Progress value' idx term
      progress Here value (Singleton (MkCase branch))
        = Step (ReduceSingleton value)

      progress Here value (Extend (MkCase branch) rest)
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
    progress (I x) = Done I
    progress (C x) = Done C

    -- Variant Constructors
    progress TyInt  = Done TyInt
    progress TyChar = Done TyChar

    progress (TyVariant fields) with (Fields.progress fields)
      progress (TyVariant fields) | (Done value) = Done (TyVariant value)
      progress (TyVariant fields) | (Step step) = Step (SimplifyTyVariant step)

    -- Variant Value Constructors
    progress (Tag field type chk prf) with (progress type)
      progress (Tag field type chk prf) | (Done valueT) with (progress field)
        progress (Tag field type chk prf) | (Done valueT) | (Done valueF)
          = Done (Tag valueT valueF)
        progress (Tag field type chk prf) | (Done valueT) | (Step stepF)
          = Step (SimplifyTagValue valueT stepF)
      progress (Tag field type chk prf) | (Step step)
        = Step (SimplifyTagType step)

    -- Variant Matching
    progress (Match field cases) with (progress field)
      progress (Match (Tag label value t idx) cases) | (Done (Tag prfT prfV)) with (Cases.progress idx prfV cases)
        progress (Match (Tag label value t idx) cases) | (Done (Tag prfT prfV)) | (Step step)
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
  iciTy : Variant Nil (VariantTyDesc [IntTyDesc, CharTyDesc])
  iciTy = TyVariant (Extend (MkField TyInt)
                            (Singleton (MkField TyChar)))


  public export
  ici : Variant Nil (VariantTy [IntTy, CharTy])
  ici = Tag (I 1) iciTy (CheckVar (CheckRest CheckInt (CheckOne CheckChar))) Here

  public export
  icc : Variant Nil (VariantTy [IntTy, CharTy])
  icc = Let iciTy (Tag (C 'c') (Var Here) (CheckVar (CheckRest CheckInt (CheckOne CheckChar))) (There Here))


  public export
  iciM : Variant Nil IntTy
  iciM = Match ici (Extend            (MkCase (Var Here))
                           (Singleton (MkCase (I 2))))

  public export
  iccM : Variant Nil IntTy
  iccM = Match icc (Extend            (MkCase (Var Here))
                           (Singleton (MkCase (I 2))))
