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
module Razor.SystemFoo

import Razor.Common

%default covering

namespace Types

  ||| Levels at which types and their types are defined in our type
  ||| universes.
  public export
  data Level = Type0 -- Build types here
             | Type1 -- Use types here.

  ||| Our types are meta types...
  public export
  data MTy : Level -> Type where

    -- Explicit Type formers
    IntTyDesc : MTy Type0
    IntTy : MTy Type1

    CharTyDesc : MTy Type0
    CharTy : MTy Type1

    -- Implicit constructions.
    NewtypeTy : MTy level -> MTy level

    FuncTy : MTy level -> MTy level -> MTy level


  ||| A predicate to type check types against type formers.
  public export
  data TyCheck : (type : MTy Type0)
              -> (value : MTy Type1)
              -> Type
    where
      ChkInt  : TyCheck IntTyDesc IntTy
      ChkChar : TyCheck CharTyDesc CharTy

      ChkNewtype : TyCheck innerType innerValue
                -> TyCheck (NewtypeTy innerType)
                           (NewtypeTy innerValue)

      ChkFunc : TyCheck paramTy  paramValue
             -> TyCheck returnTy returnValue
             -> TyCheck (FuncTy paramTy    returnTy)
                        (FuncTy paramValue returnValue)

  ||| A context is a list of types in different universes.
  public export
  Context : List Level -> Type
  Context = DList Level MTy

  public export
  Contains : Context lvls -> MTy level -> Type
  Contains g ty = Elem Level MTy ty g

namespace Terms

    public export
    data SystemFoo : Context lvls -> MTy level -> Type where
      -- STLC

      Var : Elem Level MTy type ctxt -> SystemFoo ctxt type

      Func : {paramTy, bodyTy : MTy Type1}
          -> (term : SystemFoo (ctxt +=         paramTy) bodyTy)
                  -> SystemFoo  ctxt    (FuncTy paramTy  bodyTy)

      App : {paramTy, bodyTy : MTy Type1}
         -> (func  : SystemFoo ctxt (FuncTy paramTy bodyTy))
         -> (value : SystemFoo ctxt         paramTy)
                  -> SystemFoo ctxt                 bodyTy

      -- Type Constructors
      TyInt  : SystemFoo ctxt IntTyDesc
      TyChar : SystemFoo ctxt CharTyDesc

      TyFunc : {paramMTy, returnMTy : MTy Type0}
            -> (paramTy  : SystemFoo ctxt paramMTy)
            -> (returnTy : SystemFoo ctxt returnMTy)
                        -> SystemFoo ctxt (FuncTy paramMTy returnMTy)

      -- Type Ascriptions
      The : {  mtypeType  : MTy Type0}
         -> {  mtypeValue : MTy Type1}
         -> (  type  : SystemFoo ctxt mtypeType)
         -> (  value : SystemFoo ctxt mtypeValue)
         -> (0 prf   : TyCheck mtypeType mtypeValue)
                    -> SystemFoo ctxt mtypeValue

      -- Base Values

      I : Int -> SystemFoo ctxt IntTy
      C : Char -> SystemFoo ctxt CharTy

      -- NewType Type & Value Constructors, and Matching.
      TyCTor : {type : MTy Type0}
            -> (desc : SystemFoo ctxt type)
                    -> SystemFoo ctxt (NewtypeTy type)

      CTor : {typeM : MTy Type0}
          -> {typeV : MTy Type1}
          -> (  type  : SystemFoo ctxt (NewtypeTy typeM))
          -> (  value : SystemFoo ctxt typeV)
          -> (0 prf   : TyCheck typeM typeV)
          -> SystemFoo ctxt (NewtypeTy typeV)

      Match : {type  : MTy Type1}
           -> {bodyTy : MTy Type1}
           -> (value : SystemFoo ctxt           (NewtypeTy type))
           -> (body  : SystemFoo (ctxt += type) bodyTy)
                    -> SystemFoo ctxt           bodyTy

      -- Binders
      Let : {  mtypeType  : MTy Type0}
         -> {  mtypeValue : MTy Type1}
         -> {  bodyType   : MTy Type1}
         -> (  type  : SystemFoo ctxt mtypeType)
         -> (  value : SystemFoo ctxt mtypeValue)
         -> (0 prf   : TyCheck mtypeType mtypeValue)
         -> (  body  : SystemFoo (ctxt += mtypeValue) bodyType)
                    -> SystemFoo  ctxt                bodyType

      NewType : {lvl : Level}
             -> {type : MTy Type0}
             -> {bodyType : MTy lvl}
             -> (desc : SystemFoo ctxt (NewtypeTy type))
             -> (body : SystemFoo (ctxt += (NewtypeTy type)) bodyType)
                     -> SystemFoo ctxt                       bodyType

      TypeAlias : {lvl : Level}
               -> {type : MTy Type0}
               -> {bodyTy : MTy lvl}
               -> (desc : SystemFoo  ctxt    type)
               -> (body : SystemFoo (ctxt += type) bodyTy)
                       -> SystemFoo  ctxt          bodyTy


namespace Renaming

  public export
  weaken : (func : Types.Contains old type
                -> Types.Contains new type)
        -> (Contains (old += type') type
         -> Types.Contains (new += type') type)

  weaken func H = H
  weaken func (T rest) = T (func rest)

  public export
  rename : (f : {level : Level}
             -> {type  : MTy level}
                      -> Types.Contains old type
                      -> Types.Contains new type)
        -> ({level : Level}
         -> {type : MTy level}
         -> SystemFoo old type
         -> SystemFoo new type)

  -- STLC
  rename f (Var idx)        = Var (f idx)
  rename f (Func body)      = Func (rename (weaken f) body)
  rename f (App func param) = App (rename f func) (rename f param)

  -- Type Constructors
  rename f TyInt               = TyInt
  rename f TyChar              = TyChar
  rename f (TyFunc param body) = TyFunc (rename f param) (rename f body)

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
  rename f (Let type value prf body)
      = Let (rename f type)
            (rename f value)
            prf
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
                       -> Types.Contains old type
                       -> SystemFoo new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> Types.Contains (old += type') type
                   -> SystemFoo (new += type') type)
  weakens f H = Var H
  weakens f (T rest) = rename T (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Contains old type
                       -> SystemFoo new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> SystemFoo old type
                   -> SystemFoo new type)

    -- STLC
    subst f (Var idx)      = f idx
    subst f (Func body)    = Func (subst (weakens f) body)
    subst f (App func var) = App (subst f func) (subst f var)

    -- Types
    subst f TyInt  = TyInt
    subst f TyChar = TyChar
    subst f (TyFunc param return) = TyFunc (subst f param) (subst f return)

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
    subst f (Let type value prf body)
        = Let (subst f type)
              (subst f value)
              prf
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
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> SystemFoo ctxt typeA
    apply this H = this
    apply this (T rest) = Var rest

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
    FuncV : {body : SystemFoo (ctxt += paramTy) bodyTy}
                 -> Value (Func body)

    TyCharV : Value TyChar
    TyIntV : Value TyInt
    TyFuncV : {param : SystemFoo ctxt pty}
           -> {return : SystemFoo ctxt rty}
           -> Value param
           -> Value return
           -> Value (TyFunc param return)

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
      -- Functions reduce
      SimplifyFuncAppFunc : (func : Redux this that)
                                 -> Redux (App this var)
                                          (App that var)

      SimplifyFuncAppVar : {this, that : SystemFoo ctxt type}
                        -> {func       : SystemFoo ctxt (FuncTy type return)}
                        -> (value      : Value func)
                        -> (var        : Redux this that)
                                      -> Redux (App func this)
                                               (App func that)

      ReduceFunc : (prf : Value var)
                       -> Redux (App (Func body) var)
                                (subst var body)

      -- Simplify Function Types
      SimplifyTyFuncParam : (param : Redux this that)
                                  -> Redux (TyFunc this body)
                                           (TyFunc that body)

      SimplifyTyFuncBody : {this, that : SystemFoo ctxt type}
                        -> {param      : SystemFoo ctxt paramTy}
                        -> (value      : Value param)
                        -> (body       : Redux this that)
                                      -> Redux (TyFunc param this)
                                               (TyFunc param that)

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
      SimplifyLetType : {this, that : SystemFoo ctxt typeM}
                     -> {value : SystemFoo ctxt typeV}
                     -> {body : SystemFoo (ctxt += typeV) typeB}
                     -> (type : Redux this that)
                             -> Redux (Let this value prf body)
                                      (Let that value prf body)

      SimplifyLetValue : {type : SystemFoo ctxt typeM}
                      -> {this, that : SystemFoo ctxt typeV}
                      -> {body : SystemFoo (ctxt += typeV) typeB}
                      -> (typeVal : Value type)
                      -> (value   : Redux this that)
                                 -> Redux (Let type this prf body)
                                          (Let type that prf body)

      ReduceLetBody : {type  : SystemFoo ctxt typeM}
                   -> {value : SystemFoo ctxt typeV}
                   -> {0 prf : TyCheck typeM typeV}
                   -> {body : SystemFoo (ctxt += typeV) typeB}
                   -> (typeVal  : Value type)
                   -> (valueVal : Value value)
                               -> Redux (Let type value prf body)
                                        (subst value body)

      -- Newtypes

      SimplifyNewType : {this, that : SystemFoo ctxt (NewtypeTy typeV)}
                     -> {body : SystemFoo (ctxt += (NewtypeTy typeV)) typeB}
                     -> (desc : Redux this that)
                             -> Redux (NewType this body)
                                      (NewType that body)

      ReduceNewType : {typeD : MTy Type0}
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
  -- STLC
  progress {type} (Var _) impossible
  progress (Func body) = Done FuncV
  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Func b) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFunc prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  -- Type Constructors
  progress TyInt  = Done TyIntV
  progress TyChar = Done TyCharV

  progress (TyFunc param return) with (progress param)
    progress (TyFunc param return) | (Done valueP) with (progress return)
      progress (TyFunc param return) | (Done valueP) | (Done valueR)
        = Done (TyFuncV valueP valueR)
      progress (TyFunc param return) | (Done valueP) | (Step prfR)
        = Step (SimplifyTyFuncBody valueP prfR)
    progress (TyFunc param return) | (Step prfP)
      = Step (SimplifyTyFuncParam prfP)

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
  progress (Let type value prf body) with (progress type)
    progress (Let type value prf body) | (Done valueT) with (progress value)
      progress (Let type value prf body) | (Done valueT) | (Done valueV)
        = Step (ReduceLetBody valueT valueV)
      progress (Let type value prf body) | (Done valueT) | (Step prfV)
        = Step (SimplifyLetValue valueT prfV)
    progress (Let type value prf body) | (Step stepT)
      = Step (SimplifyLetType stepT)


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

namespace Example

  export
  example0 : SystemFoo Nil (FuncTy IntTy IntTy)
  example0 = TypeAlias TyInt
                       (The (TyFunc TyInt (Var H))
                            (Func (Var (H)))
                            (ChkFunc ChkInt ChkInt))

  export
  example1 : SystemFoo Nil CharTy
  example1 = NewType (TyCTor TyInt)
                     (Let (TyFunc (Var H) TyChar)
                          (Func (Match (Var H)
                                       (C 'c')
                                       ))
                          (ChkFunc (ChkNewtype ChkInt) ChkChar)
                          (App (Var H)
                               (CTor (Var (T H))
                                     (I 1)
                                     ChkInt)
                               )
                     )

-- --------------------------------------------------------------------- [ EOF ]
