open import Data.Nat
open import Data.String

module UInstr (blocks : ℕ) where

open import Instr blocks

data UInstr : Set where
  jump          : Label → UInstr
  branch-if-nil : (v : String) → Label → UInstr
  fetch-field-0 : (v : String) → (v′ : String) → UInstr
  fetch-field-1 : (v : String) → (v′ : String) → UInstr
  cons          : (v₀ : String) → (v₁ : String) → (v′ : String) → UInstr
  halt          : UInstr
  seq           : UInstr → UInstr → UInstr

forget-types-instr : ∀ {Π Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr
forget-types-instr (instr-seq i₁ i₂) = seq (forget-types-instr i₁) (forget-types-instr i₂)
forget-types-instr (instr-branch-list {l = l} {x = x} v i s) = branch-if-nil x l
forget-types-instr (instr-branch-listcons {l = l} {x = x} v i s) = branch-if-nil x l
forget-types-instr (instr-branch-nil {l = l} {x = x} v i s) = branch-if-nil x l
forget-types-instr (instr-fetch-0-new {x = x} {x' = x'} v) = fetch-field-0 x x'
forget-types-instr (instr-fetch-0-upd {x = x} {x' = x'} v v') = fetch-field-0 x x'
forget-types-instr (instr-fetch-1-new {x = x} {x' = x'} v) = fetch-field-1 x x'
forget-types-instr (instr-fetch-1-upd {x = x} {x' = x'} v v') = fetch-field-1 x x'
forget-types-instr (instr-cons-new {x₀ = x₀} {x₁ = x₁} {x' = x'} v₀ v₁ s) = cons x₀ x₁ x'
forget-types-instr (instr-cons-upd {x₀ = x₀} {x₁ = x₁} {x' = x'} v₀ v₁ v' s) = cons x₀ x₁ x'

forget-types : ∀ {Π Γ Γ'} → Block Π Γ Γ' → UInstr
forget-types block-halt = halt
forget-types (block-seq i b) = seq (forget-types-instr i) (forget-types b)
forget-types (block-jump {l} x p) = jump l
