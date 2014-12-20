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

open import Data.Bool
open import Data.List

record Sortable (Sort : Set → Set) : Set₁ where
  field
    new : ∀ {A : Set} → (A → A → Bool) → Sort A
    add : ∀ {A : Set} → A → Sort A → Sort A
    sort : ∀ {A : Set} → Sort A → List A


-- bunch of stuff for PowTree not required by PFD
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

pow₂ : ℕ → ℕ
pow₂ zero = 1
pow₂ (suc n) = double (pow₂ n)

double-lem : ∀ n → n + n ≡ double n
double-lem zero = refl
double-lem (suc n)
  = begin suc (n + suc n)   ≡⟨ cong suc $ 
          begin n + suc n   ≡⟨ +-suc n n ⟩
                suc (n + n) ∎ ⟩
          suc (suc (n + n)) ≡⟨ cong (suc ∘ suc) (double-lem n) ⟩
          (suc (suc (double n))) ∎

-- wrap the invariant in a data structure
data PowTree (A : Set) : (width : ℕ) → Set where
  []  : ∀ {w} → PowTree A w
  _∷_ : ∀ {w₁ w₂} → w₁ ≤′ w₂ → (xs : Vec A (pow₂ w₁)) → PowTree A w₂ → PowTree A w₁

-- actual data structure from PFD
record BOMSort (w : ℕ) (A : Set) : Set where
  constructor sortable
  field
    le : A → A → Bool
    segments : PowTree A w

-- summon the implicit argument from the nether
len : ∀ {A : Set} {n} → Vec A n → ℕ
len {n = n} xs = n

-- for merging arbitrary vecs
merge : ∀ {A : Set} {m n} → (A → A → Bool) → Vec A m → Vec A n → Vec A (m + n)
merge {A} le = λ xs ys → mrg xs ys
  where
  mrg : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
  mrg [] ys = ys
  mrg {m} xs [] rewrite +-right-identity m = xs
  mrg (x ∷ xs) (y ∷ ys)
    = if le x y then x ∷ mrg xs (y ∷ ys)
                else y ∷ subst (Vec A) (sym (+-suc (len xs) _)) (mrg (x ∷ xs) ys)

-- for merging vecs in the PowTree
mergePow : ∀ {A : Set} {n} → (A → A → Bool) → (xs ys : Vec A (pow₂ n)) → Vec A (pow₂ $ suc n)
mergePow {n = n} le xs ys with merge le xs ys
...  | res rewrite double-lem $ pow₂ n = res

instance
  BOMSortable : {w : ℕ} → Sortable (BOMSort w)
  BOMSortable {w}
    = record { new = λ le → sortable le $ [] {w = w}
             ; add = {!!}
             ; sort = {!!} }
