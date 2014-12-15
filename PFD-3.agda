module PFD-3 where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Vec as Vec hiding (head ; tail)
open import Data.Empty

open import Relation.Binary.PropositionalEquality

open import Function

-- TODO This is chapter 3 material
record Queue (Q : Set → ℕ → Set) : Set₁ where
  field
    empty : ∀ {A : Set} → Q A 0
    enqueue : ∀ {A : Set} {n} → Q A n → A → Q A (suc n)
    head : ∀ {A : Set} {n} → Q A (suc n) → A
    tail : ∀ {A : Set} {n} → Q A (suc n) → Q A n
open Queue ⦃ ... ⦄ public

record DQueue (A : Set) (k : ℕ) : Set where
  constructor queue
  field
    {m} : ℕ
    {n} : ℕ
    f : Vec A m
    r : Vec A n
    m+n≡k : m + n ≡ k
    invariant : m ≡ 0 → n ≡ 0

-- helper for when the invariant is obviously true
queue' : ∀ {A : Set} {k m n} → (f : Vec A (suc m)) → (r : Vec A n) → suc m + n ≡ k → DQueue A k
queue' f r m+n=k = queue f r m+n=k (λ {()})

private
  test2 : DQueue ℕ 1
  test2 =
    record { f = 1 ∷ []
           ; r = []
           ; m+n≡k = refl
           ; invariant = λ {()} }

Dempty : ∀ {A : Set} → DQueue A 0
Dempty = queue [] [] refl id

Dhead : ∀ {A : Set} {n} → DQueue A (suc n) → A
Dhead (queue [] r refl invariant) with invariant refl
... | ()
Dhead (queue (x ∷ f) _ _ _) = x

-- TODO BUG AFTER LET EXPRESSION!
Dtail : ∀ {A : Set} {k} → DQueue A (suc k) → DQueue A k
Dtail (queue [] r refl invariant) with invariant refl
...  | ()
Dtail (queue (x ∷ []) r m+n≡k invariant)
  = queue (Vec.reverse r) [] (trans (+-right-identity _) (cong pred m+n≡k)) (const refl)
Dtail (queue (x ∷ x₁ ∷ f) r m+n≡k invariant)
  = queue' (x₁ ∷ f) r (cong pred m+n≡k)

Denqueue : ∀ {A : Set} {k} → DQueue A k → A → DQueue A (suc k)
Denqueue (queue [] r m+n≡k invariant) a
  = queue' (a ∷ []) r (cong suc m+n≡k)
Denqueue (queue .{m = suc m'} (_∷_ {n = m'} x f) r m+n≡k invariant) a
  = queue' (x ∷ f) (a ∷ r) (trans (+-suc (suc m') _) (cong suc m+n≡k))

instance
  DQ-Queue : Queue DQueue
  DQ-Queue =
    record { empty = Dempty
           ; enqueue = Denqueue
           ; head = Dhead
           ; tail = Dtail }

  vecQueue : Queue Vec
  vecQueue =
    record { empty = []
           ; enqueue = _∷ʳ_
           ; head = Vec.head
           ; tail = Vec.tail }

private
  open import Data.Fin
  test3 : DQueue ℕ 10
  test3 = foldl (DQueue ℕ) enqueue empty (tabulate toℕ)
