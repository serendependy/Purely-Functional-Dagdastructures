module PFD-2 where

open import Coinduction
open import Data.Nat
open import Function

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) → (∞xs : ∞ (Colist A)) → Colist A


-- incremental
take : ∀ {A : Set} → ℕ → Colist A → Colist A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ ∞xs) = x ∷ ♯ take n (♭ ∞xs)

-- incremental
_++_ : ∀ {A : Set} → (xs ys : Colist A) → Colist A
[] ++ ys = ys
(x ∷ ∞xs) ++ ys = x ∷ ♯ (♭ ∞xs ++ ys)

-- monolithic
drop : ∀ {A : Set} → ℕ → Colist A → Colist A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (x ∷ ∞xs) = drop n (♭ ∞xs)

-- monolithic *and* non-terminating
{-# NON_TERMINATING #-}
reverse : ∀ {A : Set} → Colist A → Colist A
reverse xs = reverse' xs []
  where
  reverse' : ∀ {A : Set} → (orig accum : Colist A) → Colist A
  reverse' [] accum = accum
  reverse' (x ∷ ∞xs) accum = reverse' (♭ ∞xs) (x ∷ ∞xs)

-- not in the text
map : ∀ {A B : Set} → (A → B) → Colist A → Colist B
map f [] = []
map f (x ∷ ∞xs) = (f x) ∷ ♯ map f (♭ ∞xs)

iterate : ∀ {A : Set} → (A → A) → A → Colist A
iterate f a = f a ∷ ♯ iterate f (f a)

private
  test : Colist ℕ
  test = iterate suc 0
