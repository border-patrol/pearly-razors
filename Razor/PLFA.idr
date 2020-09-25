||| An expression language with mechanical proof of type-safety.
|||
||| `PLFA` is an expression language supporting Let-bindings,
||| Products, and Sums.  Standard constructions are used to represent
||| the language as an EDSL, together with proof of progress taken
||| from PLFA Part 2.
|||
||| This module corresponds to Section 2 of the Functional Pearl.
|||
module Razor.PLFA

import Razor.Common

%default total

namespace Types

  public export
  data Ty = TyInt
          | TyChar
          | TyProd Ty Ty
          | TySum Ty Ty

namespace Terms

  public export
  data PLFA : List Ty -> Ty -> Type where
    -- Let-Bindings & Variables
    Var : Elem ty g -> PLFA g ty
    Let : (this     : PLFA        g  expr)
       -> (beInThis : PLFA (expr::g) body)
                   -> PLFA        g  body

    -- Base Values
    I : Int  -> PLFA g TyInt
    C : Char -> PLFA g TyChar

    -- Products and accessors
    MkPair : (left  : PLFA g l)
          -> (right : PLFA g r)
                   -> PLFA g (TyProd l r)

    First  : (pair : PLFA g (TyProd l r))
                  -> PLFA g l

    Second : (pair : PLFA g (TyProd l r))
                  -> PLFA g r

    Split : (pair : PLFA g         (TyProd l r))
         -> (body : PLFA (r::l::g) b)
                 -> PLFA g         b

    -- Sums and accessors
    Left : (left : PLFA g        l)
                -> PLFA g (TySum l r)

    Right : (right : PLFA g          r)
                  -> PLFA g (TySum l r)

    Match : (variant   : PLFA g      (TySum l r))
         -> (whenLeft  : PLFA (l::g) b)
         -> (whenRight : PLFA (r::g) b)
                      -> PLFA g      b

namespace Renaming

  public export
  weaken : (Contains  old           type -> Contains  new           type)
        -> (Contains (old += type') type -> Contains (new += type') type)

  weaken func Here         = Here
  weaken func (There rest) = There (func rest)

  public export
  rename : (forall type . Contains old type -> Contains new type)
        -> (forall type . PLFA     old type -> PLFA     new type)
  -- Let Bindings & Variables
  rename f (Var x) = Var (f x)
  rename f (Let this beInThis) = Let (rename f this)
                                     (rename (weaken f) beInThis)

  -- Base Values
  rename f (I x) = I x
  rename f (C x) = C x

  -- Products & Accessors
  rename f (MkPair left right) = MkPair (rename f left) (rename f right)
  rename f (First pair) = First (rename f pair)
  rename f (Second pair) = Second (rename f pair)
  rename f (Split pair body) = Split (rename f pair)
                                     (rename ((weaken (weaken f))) body)

  -- Sums & Accessors
  rename f (Left left) = Left (rename f left)
  rename f (Right right) = Right (rename f right)
  rename f (Match variant whenLeft whenRight) = Match (rename f variant)
                                                      (rename (weaken f) whenLeft)
                                                      (rename (weaken f) whenRight)

namespace Substitution

  public export
  weakens : (forall type. Contains  old           type -> PLFA  new           type)
         -> (forall type. Contains (old += type') type -> PLFA (new += type') type)
  weakens f Here         = Var Here
  weakens f (There rest) = rename There (f rest)

  -- general substitute
  namespace General
    public export
    subst : (forall type . Contains old type -> PLFA new type)
         -> (forall type . PLFA     old type -> PLFA new type)

    -- Let-Bindings & Variables
    subst f (Var x) = (f x)
    subst f (Let this beInThis) = Let (subst f this)
                                      (subst (weakens f) beInThis)

    -- Base Values
    subst f (I x) = I x
    subst f (C x) = C x

    -- Products & Accessors
    subst f (MkPair left right) = MkPair (subst f left) (subst f right)
    subst f (First pair) = First (subst f pair)
    subst f (Second pair) = Second (subst f pair)
    subst f (Split pair body) = Split (subst f pair)
                                      (subst ((weakens (weakens f))) body)

    -- Sums & Accessors
    subst f (Left left) = Left (subst f left)
    subst f (Right right) = Right (subst f right)
    subst f (Match variant whenLeft whenRight) = Match (subst f variant)
                                                       (subst (weakens f) whenLeft)
                                                       (subst (weakens f) whenRight)
  namespace Single
    public export
    apply : (this   : PLFA ctxt typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> PLFA ctxt typeA
    apply this Here         = this
    apply this (There rest) = Var rest

    public export
    subst : (this   : PLFA  ctxt           typeB)
         -> (inThis : PLFA (ctxt += typeB) typeA)
                   -> PLFA  ctxt           typeA
    subst {ctxt} {typeA} {typeB} this inThis = General.subst (apply this) inThis

  namespace Double

    public export
    apply : (this    : PLFA       ctxt                     typeA)
         -> (andThis : PLFA       ctxt                     typeB)
         -> (idx     : Contains ((ctxt += typeA) += typeB) typeC)
                    -> PLFA       ctxt                     typeC
    apply this andThis Here              = andThis
    apply this andThis (There Here)      = this
    apply this andThis (There (There x)) = Var x

    public export
    subst : (this    : PLFA  ctxt                     typeA)
         -> (andThis : PLFA  ctxt                     typeB)
         -> (inThis : PLFA ((ctxt += typeA) += typeB) typeC)
                   -> PLFA   ctxt                     typeC
    subst {ctxt} {typeA} {typeB} {typeC} this andThis inThis = General.subst (apply this andThis) inThis


namespace Values

  public export
  data Value : PLFA ctxt type -> Type where
    IV : Value (I i)
    CV : Value (C c)
    MkPairV : Value left
           -> Value right
           -> Value (MkPair left right)

    LeftV : Value value
         -> Value (Left value)

    RightV : Value value
          -> Value (Right value)

namespace Reduction
  public export
  data Redux : (this, that : PLFA ctxt type) -> Type where
    -- Let Bindings
    SimplifyLetValue : Redux this that
                    -> Redux (Let this body)
                             (Let that body)
    ReduceLetBody : Value value
                 -> Redux (Let value body)
                          (subst value body)

    -- MkPairs
    SimplifyPairFirst : Redux this that
                    -> Redux (MkPair this right)
                             (MkPair that right)
    SimplifyPairSecond : Value left
                      -> Redux this that
                      -> Redux (MkPair left this)
                               (MkPair left that)

    -- Accessors
    SimplifyFirst : Redux this that
                 -> Redux (First this) (First that)

    ReduceFirst : Value left -> Value right -> Redux (First (MkPair left right)) left

    SimplifySecond : Redux this that
                  -> Redux (Second this) (Second that)

    ReduceSecond : Value left -> Value right -> Redux (Second (MkPair left right)) right

    -- Split Pairs
    SimplifySplitPair : Redux this that
                     -> Redux (Split this body) (Split that body)

    ReduceSplitPair : {right : PLFA g r}
                   -> {left  : PLFA g l}
                   -> {body : PLFA (r::l::g) b}
                   -> Value left
                   -> Value right
                   -> Redux (Split (MkPair left right) body)
                            (subst left right body)

    -- Variants
    SimplifyLeft : Redux this that
                -> Redux (Left this) (Left that)

    SimplifyRight : Redux this that
                 -> Redux (Right this) (Right that)

    SimplifyMatchCase : Redux this that
                     -> Redux (Match this whenleft whenright)
                              (Match that whenleft whenright)

    ReduceMatchBodyWhenLeft : Value value
                           -> Redux (Match (Left value) whenleft whenright)
                                    (subst value whenleft)

    ReduceMatchBodyWhenRight : Value value
                            -> Redux (Match (Right value) whenleft whenright)
                                     (subst value whenright)

namespace Progress
  public export
  data Progress : (term : PLFA Nil type)
                       -> Type
    where
      Done : {term : PLFA Nil mty} -> Value term -> Progress term
      Step : {this, that : PLFA Nil type}
          -> (prf  : Redux this that)
                  -> Progress this

  public export
  progress : (term : PLFA Nil type) -> Progress term

  -- Let-Bindings & Variables
  progress (Var _) impossible
  progress (Let this beInThis) with (progress this)
    progress (Let this beInThis) | (Done x) = Step (ReduceLetBody x)
    progress (Let this beInThis) | (Step prf) = Step (SimplifyLetValue prf)

  -- Base Values
  progress (I x) = Done IV
  progress (C x) = Done CV

  -- Products & Accessors
  progress (MkPair left right) with (progress left)
    progress (MkPair left right) | (Done vl) with (progress right)
      progress (MkPair left right) | (Done vl) | (Done vr) = Done (MkPairV vl vr)
      progress (MkPair left right) | (Done vl) | (Step pr) = Step (SimplifyPairSecond vl pr)

    progress (MkPair left right) | (Step pl) = Step (SimplifyPairFirst pl)

  progress (First pair) with (progress pair)
    progress (First (MkPair left right)) | (Done (MkPairV l r)) = Step (ReduceFirst l r)
    progress (First pair) | (Step pp) = Step (SimplifyFirst pp)

  progress (Second pair) with (progress pair)
    progress (Second (MkPair left right)) | (Done (MkPairV l r)) = Step (ReduceSecond l r)
    progress (Second pair) | (Step pp) = Step (SimplifySecond pp)

  progress (Split pair body) with (progress pair)
    progress (Split (MkPair left right) body) | (Done (MkPairV l r)) = Step (ReduceSplitPair l r)
    progress (Split pair body) | (Step pp) = Step (SimplifySplitPair pp)

  -- Sums & Accessors
  progress (Left left) with (progress left)
    progress (Left left) | (Done lv) = Done (LeftV lv)
    progress (Left left) | (Step lp) = Step (SimplifyLeft lp)


  progress (Right right)  with (progress right)
    progress (Right right) | (Done rv) = Done (RightV rv)
    progress (Right right) | (Step rp) = Step (SimplifyRight rp)

  progress (Match variant whenLeft whenRight) with (progress variant)
    progress (Match (Left left)   whenLeft whenRight) | (Done (LeftV  lv)) = Step (ReduceMatchBodyWhenLeft  lv)
    progress (Match (Right right) whenLeft whenRight) | (Done (RightV rv)) = Step (ReduceMatchBodyWhenRight rv)
    progress (Match variant whenLeft whenRight) | (Step vp) = Step (SimplifyMatchCase vp)


namespace Evaluation

  public export
  data Reduces : (this : PLFA ctxt type)
              -> (that : PLFA ctxt type)
              -> Type
    where
      Refl  : Reduces this this
      Trans : Redux this that
           -> Reduces that end
           -> Reduces this end

  public export
  data Finished : (term : PLFA ctxt type)
                       -> Type
    where
      Normalised : {term : PLFA ctxt type} -> Value term -> Finished term
      OOF : Finished term

  public export
  data Evaluate : (term : PLFA Nil type) -> Type where
    RunEval : (steps  : Inf (Reduces this that))
           -> (result : Finished that)
           -> Evaluate this

  public export
  data Fuel = Empty | More (Lazy Fuel)

  public export
  covering
  forever : Fuel
  forever = More forever

  public export
  compute : (fuel : Fuel)
         -> (term : PLFA Nil type)
                 -> Evaluate term
  compute Empty term = RunEval Refl OOF
  compute (More fuel) term with (progress term)
    compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)
    compute (More fuel) term | (Step step {that}) with (compute fuel that)
      compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
        = RunEval (Trans step steps) result

public export
covering
run : (this : PLFA Nil type)
           -> Maybe (Subset (PLFA Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x)) = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

namespace Examples
  public export
  ab : PLFA Nil (TyProd TyInt TyChar)
  ab = MkPair (I 1) (C 'c')

  public export
  a : PLFA Nil TyInt
  a = First ab

  public export
  b : PLFA Nil TyChar
  b = Second ab

  public export
  ba : PLFA Nil (TyProd TyChar TyInt)
  ba = Split ab (MkPair (Var Here) (Var $ There Here))

  public export
  l : PLFA Nil (TySum TyChar TyInt)
  l = Left (C 'c')

  public export
  r : PLFA Nil (TySum TyChar TyInt)
  r = Right (I 1)

  public export
  lp : PLFA Nil (TyProd TyInt TyChar)
  lp = Match l (MkPair (I 2) (Var Here)) (MkPair (Var Here) (C 'w'))

  public export
  rp : PLFA Nil (TyProd TyInt TyChar)
  rp = Match r (MkPair (I 2) (Var Here)) (MkPair (Var Here) (C 'w'))

--  snip : PLFA Nil TyInt
--  snip = Match (Left (I 1)) (Var Here) (Split (Var Here) (Var Here))
