module Exercises1

-- Ways to get help:
-- 1. Ask David
-- 2. #idris on Freenode
-- 3. Idris mailing list


-- This tells Idris to reject programs that it can't tell are
-- total. Totality means that there are no missing type-correct
-- patterns and that each call will halt.
%default total
-- If your program isn't total, you can tell Idris to allow it with
-- the "partial" modifier. For example:
||| Infinite loops inhabit every type, even the empty ones!
partial
forever : Void
forever = forever


-- We don't import Data.Vect because namespace conflicts are
-- irritating. Thus:

data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a
%name Vect xs,ys,zs

-- * Warmup: Implement some familiar utilities
head : Vect (S n) a -> a
head (x::_) = x

tail : Vect (S n) a -> Vect n a
tail (_::xs) = xs

repeat : (n : Nat) -> a -> Vect n a
repeat Z x = []
repeat (S k) x = x :: repeat k x

-- * Implement Functor, Applicative, and Monad for Vect.
instance Functor (Vect n) where
  map _ [] = []
  map f (x :: xs) = f x :: map f xs

instance Applicative (Vect n) where
    pure = repeat _
    (<*>) x [] = []
    (<*>) (f :: fs) (x :: xs) = f x :: (fs <*> xs)

instance Monad (Vect n) where



-- * Define takeWhile for Vect.  takeWhile p xs should return the
-- longest prefix of xs for which p holds. What should the return type
-- be?
takeWhile : (a -> Bool) -> Vect n a -> (m ** Vect m a)
takeWhile p [] = (_ ** [])
takeWhile p (x :: xs) with (takeWhile p xs)
  | (len ** xs')= if p x then (S len ** x :: xs')
                         else (_ ** [])

-- * Define an analogous function dropWhile that returns the elements
-- following the longest prefix that satisfies p.
dropWhile : (a -> Bool) -> Vect n a -> (m ** Vect m a)
dropWhile p [] = (_ ** [])
dropWhile p (x :: xs) with (dropWhile p xs)
  | (len ** xs')= if p x then (len ** xs')
                         else (_ ** x :: xs)

(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) [] [] = []
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

-- ** Prove that the list versions of takeWhile and dropWhile split the
-- list at the same point
takeDropOk : (p : a -> Bool) -> (xs : List a) -> takeWhile p xs ++ dropWhile p xs = xs
takeDropOk p [] = Refl
takeDropOk p (x :: xs) = let ind = takeDropOk p xs in ?takeDropOk_rhs_2

-- * Implement reverse for vectors
-- Hint: use an accumulator, and be prepared to rewrite the Nats
reverseV : Vect n a -> Vect n a
reverseV [] = []
reverseV xs ?= reverseV' xs []
  where
  reverseV' : Vect n a -> Vect m a -> Vect (n + m) a
  reverseV' [] acc = acc
  reverseV' (x :: xs) acc ?= reverseV' xs (x :: acc)

-- List membership
||| Member x xs is a proof that x is contained in xs.
|||
||| It also tells you specifically _where_ x is in xs.
data Member : a -> List a -> Type where
  ||| The element we want is at the head
  ||| @ x The element
  ||| @ xs the tail
  Here  : Member x (x :: xs)
  ||| The element we want is contained in the tail somewhere
  There : Member x xs -> Member x (y :: xs)

||| The empty list has no members
nilIsEmpty : Member x [] -> Void
nilIsEmpty Here impossible
-- impossible states that the pattern doesn't type-check. This
-- distinguishes between not-implemented-yet. We only need one pattern
-- because the system automatically checks the rest.

instance Uninhabited (Member x []) where
  uninhabited = nilIsEmpty

-- (*) Use DecEq to construct a proof that an element is present, if eossible
findMember : DecEq a => (x : a) -> (xs : List a) -> Maybe $ Member x xs
findMember x [] = Nothing
findMember x (y :: xs) with (decEq x y, findMember x xs)
  findMember x (x :: xs) | (Yes Refl, _) = Just Here
  | (No _, Just prf) = Just $ There prf
  | (_, Nothing) = Nothing

notThereButHereThenEqual : (Member x xs -> Void) -> (Member x (y :: xs)) -> x = y
notThereButHereThenEqual f Here = Refl
notThereButHereThenEqual f (There p) = void $ f p

-- (**) Show that list membership is decidable.
-- Hint: think about the auxiliary lemmas needed in case of "No".
decMember : DecEq a => (x : a) -> (xs : List a) -> Dec $ Member x xs
decMember x [] = No nilIsEmpty
decMember x (y :: xs) with (decEq x y, decMember x xs)
  decMember x (x :: xs) | (Yes Refl, _) = Yes Here
  | (No _, Yes prf) = Yes $ There prf
  | (No neq, No nm) = No $ neq . notThereButHereThenEqual nm

emptyAppendIsMember : (x : a) -> (ys : List a) -> Member x ([] ++ ys) -> Member x ys
emptyAppendIsMember x ys x1 = ?emptyAppendMember_rhs

appendEmptyIsMember : (x : a) -> (xs : List a) -> Member x (xs ++ []) -> Member x xs
appendEmptyIsMember x xs x1 = ?appendEmptyMember_rhs1

-- (**) Show that if x is an element of a concatenation, it comes from
-- at least one input list. You may need to explicitly match some patterns.
listElt : (x : a) -> (xs, ys : List a) -> Member x (xs ++ ys) -> Either (Member x xs) (Member x ys)

-- *** write a program that reads lines of input until the user
-- somehow signals that it should stop. Then, it should read a natural
-- number. If the number is n less than the number of strings read,
-- then the nth string (0-indexed) should be displayed. Otherwise, an
-- error should be displayed. Use the type system to guarantee the
-- relationship between n and the number of strings - the lookup must
-- be statically bounds-checked. Don't bother checking IO actions for
-- totality.
-- Hints: :doc LTE ; :doc LT ; :search LTE m n
-- Feel free to use "cast" to read n
namespace Main
  partial
  main : IO ()
  main = ?main_impl

---------- Proofs ----------
Exercises1.appendEmptyMember_rhs1 = proof
  intros
  rewrite (appendNilRightNeutral xs)
  trivial


Exercises1.takeDropOk_rhs_2 = proof
  intros
  case (p x)
  compute
  trivial
  compute
  rewrite ind
  trivial



Exercises1.emptyAppendMember_rhs = proof
  intros
  trivial


Exercises1.reverseV_lemma_1 = proof
  intros
  trivial



Exercises1.reverseV'_lemma_1 = proof
  intros
  rewrite sym (plusSuccRightSucc n1 m)
  trivial


