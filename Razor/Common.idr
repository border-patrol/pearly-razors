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
        H : Elem a e x (x :: xs)

        ||| The element is found in the tail of the list.
        T : (rest : Elem a e x        xs)
                 -> Elem a e x (x' :: xs)


-- --------------------------------------------------------------------- [ EOF ]
