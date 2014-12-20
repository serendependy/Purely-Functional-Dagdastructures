module PFD-3 where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Vec as Vec hiding (head ; tail)
open import Data.Empty

open import Relation.Binary.PropositionalEquality

open import Function

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
  open import Data.Fin using (toℕ)
  test3 : DQueue ℕ 10
  test3 = foldl (DQueue ℕ) enqueue empty (tabulate toℕ)

record BankerQueue (A : Set) (k : ℕ) : Set where
  constructor queue
  field
    {m n} : ℕ
    f : Vec A m
    r : Vec A n
    m+n=k : m + n ≡ k
    invariant : n ≤′ m

private
  test4 : BankerQueue ℕ 4
  test4 = queue (0 ∷ 1 ∷ []) (2 ∷ 3 ∷ []) refl ≤′-refl

open import Data.Nat.Properties

open ≡-Reasoning

banker-queue : ∀ {A : Set} {m n k} → Vec A m → Vec A n → m + n ≡ k → BankerQueue A k
banker-queue {m = m} {n = n} f r m+n=k with compare n m
banker-queue f r m+n=k | less m k = queue f r m+n=k (≤′-step (m≤′m+n m k))
banker-queue f r m+n=k | equal m = queue f r m+n=k ≤′-refl
banker-queue {k = k'} f r m+n=k | greater m k =
  queue (f ++ reverse r) [] m+n=k' (≤⇒≤′ z≤n)
  where
  m+n=k' = begin m + suc (m + k) + zero ≡⟨ +-right-identity _ ⟩
                 m + suc (m + k)        ≡⟨ m+n=k ⟩
                 k' ∎

Bempty : ∀ {A : Set} → BankerQueue A 0
Bempty = queue [] [] refl ≤′-refl

Benqueue : ∀ {A : Set} {k} → BankerQueue A k → A → BankerQueue A (suc k)
Benqueue {k = k} (queue {m} {n} f r m+n=k invariant) a
  = banker-queue f (a ∷ r) m+n=k'
  where
  m+n=k' = begin m + suc n ≡⟨ +-suc m n ⟩
                 suc m + n ≡⟨ cong suc m+n=k ⟩
                 suc k ∎

Bhead : ∀ {A : Set} {k} → BankerQueue A (suc k) → A
Bhead (queue {n = n} [] _ m+n=k invariant) with n | m+n=k
Bhead (queue         [] _ _     ()) | ._ | refl --invariant violation
Bhead (queue (x ∷ f) r m+n=k invariant) = x

Btail : ∀ {A : Set} {k} → BankerQueue A (suc k) → BankerQueue A k
Btail (queue {n = n} [] _ m+n=k invariant) with n | m+n=k
Btail (queue         [] _ _     ()) | ._ | refl --invariant violation
Btail (queue (x ∷ f) r m+n=k invariant)
  = banker-queue f r (cong pred m+n=k)

instance
  BankQueue : Queue BankerQueue
  BankQueue
    = record { empty = Bempty
             ; enqueue = Benqueue
             ; head = Bhead
             ; tail = Btail }
