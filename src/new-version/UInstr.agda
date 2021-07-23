open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (index)
open import Data.Nat

open import Relation.Binary.PropositionalEquality

module UInstr where
    open import Type
    open import Instr
    open import Subtyping

    -- list indexing view

    index : ∀ {A : Set}{t : A}{Γ : List A} → t ∈ Γ → ℕ
    index (here px) = zero
    index (there p) = suc (index p)


    data Lookup {A : Set}(xs : List A) : ℕ → Set where
      inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
      outside : ∀ {n} → Lookup xs n

    lookup-var : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
    lookup-var [] n = outside
    lookup-var (x ∷ xs) zero = inside x (here refl)
    lookup-var (x ∷ xs) (suc n) with lookup-var xs n
    lookup-var (x ∷ xs) (suc .(index p)) | inside y p = inside y (there p)
    lookup-var (x ∷ xs) (suc _) | outside = outside

    data UInstr (n : ℕ) : Set where
      jump          : (x : ℕ) → Label n → UInstr n
      branch-if-nil : (v : ℕ) → Label n → UInstr n
      fetch-field-0 : (v : ℕ) → (v′ : ℕ) → UInstr n
      fetch-field-1 : (v : ℕ) → (v′ : ℕ) → UInstr n
      get-label     : (v : ℕ) → Label n → UInstr n
      cons          : (v₀ : ℕ) → (v₁ : ℕ) → (v′ : ℕ) → UInstr n
      halt          : UInstr n
      seq           : UInstr n → UInstr n → UInstr n

    forget-types-instr : ∀ {n}{Π : PCtx n}{Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr n
    forget-types-instr (instr-seq p p₁) = seq (forget-types-instr p) (forget-types-instr p₁)
    forget-types-instr (instr-branch-list {l = l} idx x x₁) = branch-if-nil (index idx) l
    forget-types-instr (instr-branch-listcons {l = l} idx x x₁) = branch-if-nil (index idx) l
    forget-types-instr (instr-branch-nil {l = l} x x₁ x₂) = branch-if-nil (index x) l
    forget-types-instr (instr-fetch-0-new {v' = v'} x) = fetch-field-0 (index x) v'
    forget-types-instr (instr-fetch-0-upd x idx) = fetch-field-0 (index x) (index idx)
    forget-types-instr (instr-fetch-1-new {v' = v'} x) = fetch-field-1 (index x) v'
    forget-types-instr (instr-fetch-1-upd x idx) = fetch-field-1 (index x) (index idx)
    forget-types-instr (instr-cons-new {v' = v'} x x₁ x₂) = cons (index x) (index x₁) v'
    forget-types-instr (instr-cons-upd x x₁ idx x₂) = cons (index x) (index x₁) (index idx)
    forget-types-instr (instr-getlabel-0 {l = l} idx) = get-label (index idx) l
    forget-types-instr (instr-getlabel {l = l} idx x) = get-label (index idx) l

    forget-types : ∀ {n}{Π : PCtx n}{Γ Γ'} → Block Π Γ Γ' → UInstr n
    forget-types block-halt = halt
    forget-types (block-seq i b) = seq (forget-types-instr i) (forget-types b)
    forget-types (block-jump {l = l} k p) = jump (index k) l
