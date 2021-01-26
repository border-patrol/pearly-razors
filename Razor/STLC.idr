||| An approach to intrinsically-typed STLC with types as terms.
|||
||| We use this razor to demonstrate succintly how Type universes are
||| used to separate descriptions of how types are formed and their
||| use to type values.
|||
||| Standard constructions are used to represent the language as an
||| EDSL, together with proof of progress taken from PLFA Part 2.
|||
||| This module compliments Appendix 2 of the Functional Pearl.
|||
||| Although the code appears to be total, there is a known issues
||| with Idris2 totality checker that causes it to slow down when
||| dealing with mutually defined terms.
|||
module Razor.STLC

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

    BoolTyDesc : MTy TYPE
    BoolTy     : MTy VALUE

    FuncTy : MTy level -> MTy level -> MTy level


  ||| A predicate to type check types against type formers.
  public export
  data TyCheck : (type : MTy TYPE)
              -> (value : MTy VALUE)
              -> Type
    where
      ChkBool : TyCheck BoolTyDesc BoolTy

      ChkFunc : TyCheck paramTy  paramValue
             -> TyCheck returnTy returnValue
             -> TyCheck (FuncTy paramTy    returnTy)
                        (FuncTy paramValue returnValue)

  ||| A context is a list of types in different universes.
  public export
  Context : List Level -> Type
  Context = DList Level MTy

  public export
  Elem : Context lvls -> MTy level -> Type
  Elem g ty = Elem Level MTy ty g

namespace Terms

    public export
    data STLC : Context lvls -> MTy level -> Type where
      -- STLC

      Var : Elem Level MTy type ctxt -> STLC ctxt type

      Func : {paramTyType     : MTy TYPE}
          -> {paramTy, bodyTy : MTy VALUE}
          -> (type : STLC ctxt paramTyType)
          -> (term : STLC (ctxt +=         paramTy) bodyTy)
          -> (prf  : TyCheck paramTyType paramTy)
                  -> STLC  ctxt    (FuncTy paramTy  bodyTy)

      App : {paramTy, bodyTy : MTy VALUE}
         -> (func  : STLC ctxt (FuncTy paramTy bodyTy))
         -> (value : STLC ctxt         paramTy)
                  -> STLC ctxt                 bodyTy

      -- Type Constructors
      TyBool : STLC ctxt BoolTyDesc
      TyFunc : {paramMTy, returnMTy : MTy TYPE}
            -> (paramTy  : STLC ctxt paramMTy)
            -> (returnTy : STLC ctxt returnMTy)
                        -> STLC ctxt (FuncTy paramMTy returnMTy)

      -- Base Values
      True  : STLC ctxt BoolTy
      False : STLC ctxt BoolTy

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
         -> STLC old type
         -> STLC new type)

  -- STLC
  rename f (Var idx) = Var (f idx)

  rename f (Func ty body prf)
    = Func (rename f ty) (rename (weaken f) body) prf

  rename f (App func param)
    = App (rename f func) (rename f param)

  -- Type Constructors
  rename f TyBool = TyBool
  rename f (TyFunc param body)
    = TyFunc (rename f param) (rename f body)

  -- Base Values
  rename f True  = True
  rename f False = False

namespace Substitution
  public export
  weakens : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> STLC new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> Types.Elem (old += type') type
                   -> STLC (new += type') type)
  weakens f Here = Var Here
  weakens f (There rest) = rename There (f rest)

  -- general substitute
  namespace General
    public export
    subst : (f : {level : Level}
              -> {type  : MTy level}
                       -> Types.Elem old type
                       -> STLC new type)
         -> ({level : Level}
          -> {type  : MTy level}
                   -> STLC old type
                   -> STLC new type)

    -- STLC
    subst f (Var idx) = f idx

    subst f (Func type body prf)
      = Func (subst f type)
             (subst (weakens f) body)
             prf

    subst f (App func var)
      = App (subst f func) (subst f var)

    -- Types
    subst f TyBool = TyBool
    subst f (TyFunc param return)
      = TyFunc (subst f param) (subst f return)

    -- Base Values
    subst f True  = True
    subst f False = False

  namespace Single
    public export
    apply : {levelA : Level}
         -> {typeA  : MTy levelA}
         -> (this   : STLC ctxt typeB)
         -> (idx    : Elem (ctxt += typeB) typeA)
                   -> STLC ctxt typeA
    apply this Here = this
    apply this (There rest) = Var rest

    public export
    subst : {levelA,levelB : Level}
         -> {typeA         : MTy levelA}
         -> {typeB         : MTy levelB}
         -> (this          : STLC  ctxt           typeB)
         -> (inThis        : STLC (ctxt += typeB) typeA)
                          -> STLC  ctxt           typeA
    subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
      = General.subst (apply this) inThis


namespace Values

  public export
  data Value : STLC ctxt type -> Type where
    TrueV  : Value True
    FalseV : Value False
    FuncV : {body : STLC (ctxt += paramTy) bodyTy}
                 -> Value (Func type body prf)

    TyBoolV : Value TyBool
    TyFuncV : {param : STLC ctxt pty}
           -> {return : STLC ctxt rty}
           -> Value param
           -> Value return
           -> Value (TyFunc param return)

namespace Reduction

  public export
  data Redux : (this : STLC ctxt type)
            -> (that : STLC ctxt type)
            -> Type
    where
      -- Functions reduce
      SimplifyFuncAppFunc : (func : Redux this that)
                                 -> Redux (App this var)
                                          (App that var)

      SimplifyFuncAppVar : {this, that : STLC ctxt type}
                        -> {func       : STLC ctxt (FuncTy type return)}
                        -> (value      : Value func)
                        -> (var        : Redux this that)
                                      -> Redux (App func this)
                                               (App func that)

      ReduceFuncApp : (value : Value var)
                            -> Redux (App (Func type body prf) var)
                                     (subst var body)

      -- Simplify Function Types
      SimplifyTyFuncParam : (param : Redux this that)
                                  -> Redux (TyFunc this body)
                                           (TyFunc that body)

      SimplifyTyFuncBody : {this, that : STLC ctxt type}
                        -> {param      : STLC ctxt paramTy}
                        -> (value      : Value param)
                        -> (body       : Redux this that)
                                      -> Redux (TyFunc param this)
                                               (TyFunc param that)


namespace Progress
  public export
  data Progress : (term : STLC Nil type)
                       -> Type
    where
      Done : forall mty . {term : STLC Nil mty}
                        -> Value term
                        -> Progress term
      Step : {this, that : STLC Nil type}
          -> (prf        : Redux this that)
                        -> Progress this

  public export
  progress : (term : STLC Nil type)
          -> Progress term
  -- STLC
  progress {type} (Var _) impossible

  progress (Func type body prf) = Done FuncV

  progress (App func var) with (progress func)
    progress (App func var) | (Done prfF) with (progress var)
      progress (App (Func ty b prf) var) | (Done prfF) | (Done prfV)
        = Step (ReduceFuncApp prfV {body=b})
      progress (App func var) | (Done prfF) | (Step prfV)
        = Step (SimplifyFuncAppVar prfF prfV)
    progress (App func var) | (Step prfF)
      = Step (SimplifyFuncAppFunc prfF)

  -- Type Constructors
  progress TyBool = Done TyBoolV

  progress (TyFunc param return) with (progress param)
    progress (TyFunc param return) | (Done valueP) with (progress return)
      progress (TyFunc param return) | (Done valueP) | (Done valueR)
        = Done (TyFuncV valueP valueR)
      progress (TyFunc param return) | (Done valueP) | (Step prfR)
        = Step (SimplifyTyFuncBody valueP prfR)
    progress (TyFunc param return) | (Step prfP)
      = Step (SimplifyTyFuncParam prfP)

  -- Base Values
  progress True  = Done TrueV
  progress False = Done FalseV

namespace Evaluation

  public export
  data Reduces : (this : STLC ctxt type)
              -> (that : STLC ctxt type)
              -> Type
    where
      Refl  : {this : STLC ctxt type}
                   -> Reduces this this
      Trans : {this, that, end : STLC ctxt type}
           -> Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : STLC ctxt type)
                       -> Type
    where
      Normalised : {term : STLC ctxt type}
                        -> Value term
                        -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : STLC Nil type) -> Type where
    RunEval : {this, that : STLC Nil type}
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
         -> (term : STLC Nil type)
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
    . (this : STLC Nil type)
           -> Maybe (Subset (STLC Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

namespace Example

  export
  example0 : STLC Nil BoolTy
  example0 = App (Func TyBool (Var Here) ChkBool) True

  export
  example1 : STLC Nil (FuncTy BoolTy BoolTy)
  example1 = (Func TyBool True ChkBool)

-- --------------------------------------------------------------------- [ EOF ]
