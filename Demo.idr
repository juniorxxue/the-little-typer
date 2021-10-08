module Main

data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect n a -> Vect (S n) a

head : Vect (S n) a -> a
head (x::xs) = x

tail : Vect (S n) a -> Vect n a
tail (x::xs) = xs

firstOfOne : (a : Type) -> Vect 1 a -> a
firstOfOne a es = head es

firstOfTwo : (a : Type) -> Vect 2 a -> a
firstOfTwo a es = head es

first : (a : Type)  -> (n : Nat) -> Vect (S n) a -> a
first a n es = head es
