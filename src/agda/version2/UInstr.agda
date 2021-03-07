open import Data.Nat

module UInstr (blocks : ℕ) where

open import Instr blocks

data UInstr : Set where
  jump          : Label → UInstr
  branch-if-nil : Label → UInstr
  fetch-field-0 : (v : ℕ) → (v′ : ℕ) → UInstr
  fetch-field-1 : (v : ℕ) → (v′ : ℕ) → UInstr
  get-label     : (v : ℕ) → Label → UInstr
  cons          : (v₀ : ℕ) → (v₁ : ℕ) → (v′ : ℕ) → UInstr
  halt          : UInstr
  seq           : UInstr → UInstr → UInstr

forget-types-instr : ∀ {Π Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr
forget-types-instr (instr-seq p p₁) = seq (forget-types-instr p) (forget-types-instr p₁)
forget-types-instr (instr-branch-list {l = l} idx x x₁) = branch-if-nil l
forget-types-instr (instr-branch-listcons {l = l} idx x x₁) = branch-if-nil l
forget-types-instr (instr-branch-nil {l = l} x x₁ x₂) = branch-if-nil l
forget-types-instr (instr-fetch-0-new x) = fetch-field-0 {!!} {!!}
forget-types-instr (instr-fetch-0-upd x idx) = fetch-field-0 {!!} {!!}
forget-types-instr (instr-fetch-1-new x) = {!fetch-field-1 !}
forget-types-instr (instr-fetch-1-upd x idx) = {!!}
forget-types-instr (instr-cons-new x x₁ x₂) = {!!}
forget-types-instr (instr-cons-upd x x₁ idx x₂) = {!!}
forget-types-instr (instr-getlabel-0 idx) = {!!}
forget-types-instr (instr-getlabel idx x) = {!!}

forget-types : ∀ {Π Γ Γ'} → Block Π Γ Γ' → UInstr
forget-types = {!!}
