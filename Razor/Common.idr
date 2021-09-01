||| A collection of utlities shared accross the Razors.
|||
||| This consists of:
|||
|||  + some syntactic sugar to make functions detailing renaming,
|||    weakening, and substitution more like those seen in PLFA.
|||
|||  + Some data structures to make working with collections of
|||    dependent types easier.
module Razor.Common

import public Decidable.Equality

import public Data.List.Elem
import public Data.Vect
import public Data.Vect.Elem
import public Data.Fin
import public Data.DPair

%default total

-- A reverse cons operator.
infixr 6 +=

namespace List

  ||| Proof that the given list (`xs`) contains the given element
  ||| (`x`).
  |||
  |||
  public export
  Contains : List a -> a -> Type
  Contains xs x = Elem x xs

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs

namespace Vect

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : (xs : Vect n a) -> (x : a) -> Vect (S n) a
  (+=) xs x = x :: xs

namespace DList

  ||| A list construct for dependent types.
  |||
  ||| @a  The type of the value contained within the list element type.
  ||| @e  The type of the elements within the list
  ||| @vs The List used to contain the different values within the type.
  public export
  data DList : (a : Type)
            -> (e : a -> Type)
            -> (vs : List a)
            -> Type
    where
      Nil  : DList a e Nil
      (::) : forall v
           .  (head : (e v))
           -> (tail : DList a e vs)
                   -> DList a e (v::vs)

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : forall v
       . (xs : DList a e vs)
      -> (x  : e v)
            -> DList a e (v::vs)
  (+=) xs x = x :: xs

  ||| A proof that some element (`x`) is found in the given list (`xs`).
  public export
  data Elem : (a : Type)
           -> (e : a -> Type)
           -> forall i, is
            . (x      : e i)
           -> (xs     : DList a e is)
           -> Type
      where
        ||| The element is at the head of the list.
        Here : Elem a e x (x :: xs)

        ||| The element is found in the tail of the list.
        There : (rest : Elem a e x        xs)
                     -> Elem a e x (x' :: xs)

namespace Index
  public export
  data AtIndex : (idx : Fin n)
              -> (xs  : Vect n type)
              -> (x   : type)
                     -> Type
    where
      Here : AtIndex FZ (x::xs) x

      There : (later : AtIndex     rest      xs  x)
                    -> AtIndex (FS rest) (y::xs) x

  namespace Check
    public export
    elemDiffers : (y = x -> Void)
                -> AtIndex FZ (y :: xs) x
                -> Void
    elemDiffers f Here
      = f Refl

    public export
    elemNotInRest : (AtIndex z xs x -> Void)
                 ->  AtIndex (FS z) (y :: xs) x
                 ->  Void
    elemNotInRest f (There later)
      = f later

    ||| Is the element at the given index?
    |||
    public export
    index : DecEq type
         => (idx : Fin n)
         -> (x   : type)
         -> (xs  : Vect n type)
                -> Dec (AtIndex idx xs x)

    index FZ _ [] impossible
    index (FS y) _ [] impossible

    index FZ x (y :: xs) with (decEq y x)
      index FZ x (x :: xs) | (Yes Refl)
        = Yes Here
      index FZ x (y :: xs) | (No contra)
        = No (elemDiffers contra)

    index (FS z) x (y :: xs) with (Check.index z x xs)
      index (FS z) x (y :: xs) | (Yes prf)
        = Yes (There prf)
      index (FS z) x (y :: xs) | (No contra)
        = No (elemNotInRest contra)

  namespace Find
    public export
    elemNotInRest : (DPair type (AtIndex     x        xs)  -> Void)
                 ->  DPair type (AtIndex (FS x) (y :: xs)) -> Void

    elemNotInRest f (MkDPair i (There later))
      = f (MkDPair i later)

    ||| What is the element at the given index?
    |||
    public export
    index : DecEq type
         => (idx : Fin n)
         -> (xs  : Vect n type)
                -> Dec (DPair type (AtIndex idx xs))
    index FZ (x :: xs)
      = Yes (MkDPair x Here)

    index (FS x) (y :: xs) with (Find.index x xs)
      index (FS x) (y :: xs) | (Yes (MkDPair i idx))
        = Yes (MkDPair i (There idx))
      index (FS x) (y :: xs) | (No contra) = No (elemNotInRest contra)


-- [ EOF ]
