||| An approach to intrinsically-typed STLC with Type Synonyms and New types.
|||
||| We treat type 'aliases' and 'newtypes' as term level constructs,
||| which ensures named types can be differentiated by name i.e. De
||| Bruijn indices.  Type universes are used to separate descriptions
||| of how types are formed and their use to type values.
|||
||| Standard constructions are used to represent the language as an
||| EDSL, together with proof of progress taken from PLFA Part 2.
|||
||| This module compliments Section 5 of the Functional Pearl.
|||
||| Although the code appears to be total, there is a known issues
||| with Idris2 totality checker that causes it to slow down when
||| dealing with mutually defined terms.
|||
module Razor.LetFoo

import Razor.Common

%default covering

namespace Types

  ||| Levels at which types and their types are defined in our type
  ||| universes.
  public export
  data Level = TYPE -- Build types here
             | VALUE -- Use types here.

  ||| Our types are meta types...
  public export
  data MTy : Level -> Type where

    -- Explicit Type formers
    IntTyDesc : MTy TYPE
    IntTy : MTy VALUE

    CharTyDesc : MTy TYPE
    CharTy : MTy VALUE

    -- Implicit constructions.
    NewtypeTy : MTy level -> MTy level

  ||| A predicate to type check types against type formers.
  public export
  data TyCheck : (type : MTy TYPE)
              -> (value : MTy VALUE)
              -> Type
    where
      ChkInt  : TyCheck IntTyDesc IntTy
      ChkChar : TyCheck CharTyDesc CharTy

      ChkNewtype : TyCheck innerType innerValue
                -> TyCheck (NewtypeTy innerType)
                           (NewtypeTy innerValue)


  ||| A context is a list of types in different universes.
  public export
  Context : List Level -> Type
  Context = DList Level MTy

  public export
  Elem : Context lvls -> MTy level -> Type
  Elem g ty = Elem Level MTy ty g

namespace Terms

    public export
    data SystemFoo : Context lvls -> MTy level -> Type where
      -- STLC

      Var : Elem Level MTy type ctxt -> SystemFoo ctxt type

      -- Type Constructors
      TyInt  : SystemFoo ctxt IntTyDesc
      TyChar : SystemFoo ctxt CharTyDesc

      -- Type Ascriptions
      The : {  mtypeType  : MTy TYPE}
         -> {  mtypeValue : MTy VALUE}
         -> (  type  : SystemFoo ctxt mtypeType)
         -> (  value : SystemFoo ctxt mtypeValue)
         -> (0 prf   : TyCheck mtypeType mtypeValue)
                    -> SystemFoo ctxt mtypeValue

      -- Base Values

      I : Int -> SystemFoo ctxt IntTy
      C : Char -> SystemFoo ctxt CharTy

      -- NewType Type & Value Constructors, and Matching.
      TyCTor : {type : MTy TYPE}
            -> (desc : SystemFoo ctxt type)
                    -> SystemFoo ctxt (NewtypeTy type)

      CTor : {typeM : MTy TYPE}
          -> {typeV : MTy VALUE}
          -> (  type  : SystemFoo ctxt (NewtypeTy typeM))
          -> (  value : SystemFoo ctxt typeV)
          -> (0 prf   : TyCheck typeM typeV)
          -> SystemFoo ctxt (NewtypeTy typeV)

      Match : {type  : MTy VALUE}
           -> {bodyTy : MTy VALUE}
           -> (value : SystemFoo ctxt           (NewtypeTy type))
           -> (body  : SystemFoo (ctxt += type) bodyTy)
                    -> SystemFoo ctxt           bodyTy

      -- Binders
      Let : {  exprTy, bodyType : MTy VALUE}
         -> (  value : SystemFoo ctxt exprTy)
         -> (  body  : SystemFoo (ctxt += exprTy) bodyType)
                    -> SystemFoo  ctxt            bodyType

      NewType : {lvl : Level}
             -> {type : MTy TYPE}
             -> {bodyType : MTy lvl}
             -> (desc : SystemFoo ctxt     (NewtypeTy type))
             -> (body : SystemFoo (ctxt += (NewtypeTy type)) bodyType)
                     -> SystemFoo ctxt                       bodyType

      TypeAlias : {lvl : Level}
               -> {type : MTy TYPE}
               -> {bodyTy : MTy lvl}
               -> (desc : SystemFoo  ctxt    type)
               -> (body : SystemFoo (ctxt += type) bodyTy)
                       -> SystemFoo  ctxt          bodyTy


namespace Renaming

  public export
  weaken : (func : Types.Elem old type
                -> Types.Elem new type)
        -> (Elem (old += type') type
         -> Types.Elem (new += type') type)

  weaken func Here = Here
  weaken func (There rest) = There (func rest)

  public export
  rename : (f : {level : Level}
             -> {type  : MTy level}
                      -> Types.Elem old type
                      -> Types.Elem new type)
        -> ({level : Level}
         -> {type : MTy level}
         -> SystemFoo old type
         -> SystemFoo new type)

  -- STLC
  rename f (Var idx) = Var (f idx)

  -- Type Constructors
  rename f TyInt               = TyInt
  rename f TyChar              = TyChar

  -- Type Ascriptions
  rename f (The type value prf) = The (rename f type)
                                      (rename f value)
                                      prf
  -- Base Values
  rename f (I i) = (I i)
  rename f (C c)  = (C c)

  -- NewType Type & Value Constructors, and Matching.
  rename f (TyCTor desc) = TyCTor (rename f desc)

  rename f (CTor type value prf)
      = CTor (rename f type)
             (rename f value)
             prf

  rename f (Match scrutinee body)
      = Match (rename f scrutinee)
              (rename (weaken f) body)

  -- Binders
  rename f (Let expr body)
      = Let (rename f expr)
            (rename (weaken f) body)

  rename f (NewType type body)
      = NewType (rename f type)
                (rename (weaken f) body)

  rename f (TypeAlias type body)
      = TypeAlias (rename f type)
                  (rename (weaken f) body)

namespace Substitution
  public export
  weakens : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> SystemFoo new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> Types.Elem (old += type') type
                   -> SystemFoo (new += type') type)
  weakens f Here = Var Here
  weakens f (There rest) = rename There (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> SystemFoo new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> SystemFoo old type
                   -> SystemFoo new type)

    -- STLC
    subst f (Var idx) = f idx

    -- Types
    subst f TyInt  = TyInt
    subst f TyChar = TyChar

    -- Type Ascriptions
    subst f (The type value prf)
        = The (subst f type)
              (subst f value)
              prf

    -- Base Values
    subst f (I i) = (I i)
    subst f (C c) = (C c)

    -- NewType Type & Value Constructors, and Matching.
    subst f (Match scrutinee body)
        = Match (subst f scrutinee) (subst (weakens f) body)

    subst f (CTor type value prf)
        = CTor (subst f type) (subst f value) prf

    subst f (TyCTor desc) = TyCTor (subst f desc)

    -- Bindings
    subst f (Let expr body)
        = Let (subst f expr)
              (subst (weakens f) body)

    subst f (NewType desc body)
        = NewType (subst f desc) (subst (weakens f) body)

    subst f (TypeAlias type body)
        = TypeAlias (subst f type) (subst (weakens f) body)

  namespace Single
    public export
    apply : {levelA : Level}
         -> {typeA  : MTy levelA}
         -> (this   : SystemFoo ctxt typeB)
         -> (idx    : Elem (ctxt += typeB) typeA)
                   -> SystemFoo ctxt typeA
    apply this Here = this
    apply this (There rest) = Var rest

    public export
    subst : {levelA,levelB : Level}
         -> {typeA         : MTy levelA}
         -> {typeB         : MTy levelB}
         -> (this          : SystemFoo  ctxt           typeB)
         -> (inThis        : SystemFoo (ctxt += typeB) typeA)
                          -> SystemFoo  ctxt           typeA
    subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
      = General.subst (apply this) inThis


namespace Values

  public export
  data Value : SystemFoo ctxt type -> Type where
    TyCharV : Value TyChar
    TyIntV : Value TyInt

    TyCTorV : Value desc -> Value (TyCTor desc)
    CTorV   : Value value -> Value (CTor type value prf)

    IntV  : Value (I i)
    CharV : Value (C c)

namespace Reduction

  public export
  data Redux : (this : SystemFoo ctxt type)
            -> (that : SystemFoo ctxt type)
            -> Type
    where

      -- Ascriptions
      SimplifyTheType : (type : Redux this that)
                             -> Redux (The this value prf)
                                      (The that value prf)

      SimplifyTheValue : {this, that : SystemFoo ctxt vtype}
                      -> {type       : SystemFoo ctxt ttype}
                      -> (prf : Value type)
                      -> (value : Redux this that)
                      -> Redux (The type this prf')
                               (The type that prf')

      ReduceThe : {type  : SystemFoo ctxt ttype}
               -> {value : SystemFoo ctxt vtype}
               -> (typeVal  : Value type)
               -> (valueVal : Value value)
                           -> Redux (The type value prf)
                                    value

      -- Matching newtypes
      SimplifyTyCTor : (desc : Redux this that)
                            -> Redux (TyCTor this) (TyCTor that)

      SimplifyCTorType : {this, that : SystemFoo ctxt (NewtypeTy typeM)}
                      -> {value      : SystemFoo ctxt type}
                      -> (theType    : Redux this that)
                                    -> Redux (CTor this value prf)
                                             (CTor that value prf)

      SimplifyCTorValue : {this, that : SystemFoo ctxt typeV}
                       -> {theType : SystemFoo ctxt (NewtypeTy typeD)}
                       -> (typeV   : Value theType)
                       -> (value   : Redux this that)
                                  -> Redux (CTor theType this prf)
                                           (CTor theType that prf)

      SimplifyMatchScrut : {this, that : SystemFoo ctxt (NewtypeTy stype)}
                        -> {body : SystemFoo (ctxt += stype) btype}
                        -> (scutinee : Redux this that)
                                    -> Redux (Match this body)
                                             (Match that body)

      ReduceMatchBody : {type : SystemFoo ctxt (NewtypeTy ttype)}
                     -> {value : SystemFoo ctxt vtype}
                     -> {body : SystemFoo (ctxt += vtype) btype}
                     -> (valueVal : Value value)
                                 -> Redux (Match (CTor type value prf) body)
                                          (subst value body)

      -- Let binding
      SimplifyLetValue : {this, that : SystemFoo ctxt typeV}
                      -> {body : SystemFoo (ctxt += typeV) typeB}
                      -> (value   : Redux this that)
                                 -> Redux (Let this body)
                                          (Let that body)

      ReduceLetBody : {value : SystemFoo ctxt typeV}
                   -> {body  : SystemFoo (ctxt += typeV) typeB}
                   -> (valueVal : Value value)
                               -> Redux (Let value body)
                                        (subst value body)

      -- Newtypes

      SimplifyNewType : {this, that : SystemFoo ctxt (NewtypeTy typeV)}
                     -> {body : SystemFoo (ctxt += (NewtypeTy typeV)) typeB}
                     -> (desc : Redux this that)
                             -> Redux (NewType this body)
                                      (NewType that body)

      ReduceNewType : {typeD : MTy TYPE}
                   -> {desc : SystemFoo ctxt (NewtypeTy typeD)}
                   -> {body : SystemFoo (ctxt += (NewtypeTy typeD))    typeB}
                   -> (value : Value desc)
                            -> Redux (NewType desc body)
                                     (subst   desc body)

      SimplifyTypeAlias : {this, that : SystemFoo ctxt typeV}
                       -> {body       : SystemFoo (ctxt += typeV)    typeB}
                       -> (desc : Redux this that)
                               -> Redux (TypeAlias this body) (TypeAlias that body)

      ReduceTypeAlias : {desc : SystemFoo ctxt typeD}
                     -> {body : SystemFoo (ctxt += typeD)    typeB}
                     -> (descVal : Value desc)
                              -> Redux (TypeAlias desc body)
                                       (subst desc body)


namespace Progress
  public export
  data Progress : (term : SystemFoo Nil type)
                       -> Type
    where
      Done : forall mty . {term : SystemFoo Nil mty}
                        -> Value term
                        -> Progress term
      Step : {this, that : SystemFoo Nil type}
          -> (prf        : Redux this that)
                        -> Progress this

  public export
  progress : (term : SystemFoo Nil type)
          -> Progress term
  progress {type} (Var _) impossible


  -- Type Constructors
  progress TyInt  = Done TyIntV
  progress TyChar = Done TyCharV

  progress (The type value prf) with (progress type)
    progress (The type value prf) | (Done valueT) with (progress value)
      progress (The type value prf) | (Done valueT) | (Done valueV)
        = Step (ReduceThe valueT valueV)
      progress (The type value prf) | (Done valueT) | (Step prfV)
        = Step (SimplifyTheValue valueT prfV)
    progress (The type value prf) | (Step prfT)
        = Step (SimplifyTheType prfT)

  -- Base Values
  progress (I i) = Done IntV
  progress (C c) = Done CharV

  -- NewType Type & Value Constructors, and Matching.
  progress (TyCTor type) with (progress type)
    progress (TyCTor type) | (Done valueT) = Done (TyCTorV valueT)
    progress (TyCTor type) | (Step prfT) = Step (SimplifyTyCTor prfT)

  progress (CTor type value prf) with (progress type)
    progress (CTor type value prf) | (Done valueT) with (progress value)
      progress (CTor type value prf) | (Done valueT) | (Done valueV)
        = Done (CTorV valueV)
      progress (CTor type value prf) | (Done valueT) | (Step prfV)
        = Step (SimplifyCTorValue valueT prfV)
    progress (CTor type value prf) | (Step prfT)
        = Step (SimplifyCTorType prfT)

  progress (Match scrutinee body) with (progress scrutinee)
    progress (Match (CTor type' value prf) body) | (Done (CTorV valueV))
      = Step (ReduceMatchBody valueV)
    progress (Match scrutinee body) | (Step prfS)
      = Step (SimplifyMatchScrut prfS)

  -- Binders
  progress (Let value body) with (progress value)
      progress (Let value body) | (Done valueV)
        = Step (ReduceLetBody valueV)
      progress (Let value body) | (Step prfV)
        = Step (SimplifyLetValue prfV)

  progress (NewType desc body) with (progress desc)
    progress (NewType desc body) | (Done valueD)
      = Step (ReduceNewType valueD)
    progress (NewType desc body) | (Step prfD)
     = Step (SimplifyNewType prfD)

  progress (TypeAlias desc body) with (progress desc)
    progress (TypeAlias desc body) | (Done valueD)
      = Step (ReduceTypeAlias valueD)
    progress (TypeAlias desc body) | (Step prfD)
      = Step (SimplifyTypeAlias prfD)

namespace Evaluation

  public export
  data Reduces : (this : SystemFoo ctxt type)
              -> (that : SystemFoo ctxt type)
              -> Type
    where
      Refl  : {this : SystemFoo ctxt type}
                   -> Reduces this this

      Trans : {this, that, end : SystemFoo ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : SystemFoo ctxt type)
                       -> Type
    where
      Normalised : {term : SystemFoo ctxt type}
                        -> Value term
                        -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : SystemFoo Nil type) -> Type where
    RunEval : {this, that : SystemFoo Nil type}
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
  compute : forall type
          . (fuel : Fuel)
         -> (term : SystemFoo Nil type)
         -> Evaluate term
  compute Empty term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : forall type
    . (this : SystemFoo Nil type)
           -> Maybe (Subset (SystemFoo Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

-- namespace Example


-- --------------------------------------------------------------------- [ EOF ]
