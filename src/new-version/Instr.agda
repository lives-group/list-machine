open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional hiding (_∷=_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_ ; any?)
open import Data.Nat
open import Data.Vec
open import Data.Vec.Relation.Unary.All

module Instr where

    open import Type
    open import Subtyping
    open import LeastSuperType


    Label : ℕ → Set
    Label n = Fin n

    -- program typing

    PCtx : ℕ → Set
    PCtx n = Vec Ctx n

    -- intrinsically typed instructions

    infix 0 _⊢_⇒_

    data _⊢_⇒_ {n}(Π : PCtx n)(Γ : Ctx) : Ctx → Set where
      instr-seq : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ' → Π ⊢ Γ' ⇒ Γ'' → Π ⊢ Γ ⇒ Γ''
      instr-branch-list : ∀ {τ l Γ'} → (idx : list τ ∈ Γ) → Π [ l ]= Γ' → (idx ∷= nil) ⊂ Γ' → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
      instr-branch-listcons : ∀ {τ l Γ₁} → (idx : listcons τ ∈ Γ) → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
      instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
      instr-fetch-0-new     : ∀ {τ}{v' : ℕ} → listcons τ ∈ Γ → Π ⊢ Γ ⇒ τ ∷ Γ
      instr-fetch-0-upd     : ∀ {τ τ'} → listcons τ ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= τ)
      instr-fetch-1-new     : ∀ {τ}{v' : ℕ} → listcons τ ∈ Γ → Π ⊢ Γ ⇒ (list τ ∷ Γ)
      instr-fetch-1-upd     : ∀ {τ τ'} → listcons τ ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= list τ)
      instr-cons-new        : ∀ {τ τ₀ τ₁}{v' : ℕ} → τ₀ ∈ Γ → τ₁ ∈ Γ → (list τ₀ ⊔ τ₁ ~ list τ) → Π ⊢ Γ ⇒ listcons τ ∷ Γ
      instr-cons-upd        : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ →  τ₁ ∈ Γ → (idx :  τ₂ ∈ Γ) → list τ₀ ⊔ τ₁ ~ list τ → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
      instr-getlabel-0      : ∀ {τ}{l : Label n} → (idx : τ ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= nil)
      instr-getlabel        : ∀ {l τ Γ₁} → (idx : τ ∈ Γ) → Π [ l ]= Γ₁ → Π ⊢ Γ ⇒ (idx ∷= cont Γ₁)

    -- programs

    data Block {n}(Π : PCtx n) (Γ : Ctx) : Ctx →  Set where
      block-halt            : Block Π Γ Γ
      block-seq             : ∀ {Γ′ Γ''} → Π ⊢ Γ ⇒ Γ′ → Block Π Γ′ Γ'' → Block Π Γ Γ''
      block-jump            : ∀ {Γ₁ l}{idx : Π [ l ]= Γ₁} → cont Γ₁ ∈ Γ → Γ ⊂ Γ₁ → Block Π Γ Γ₁

    Program : ∀ {n} → PCtx n → Set
    Program Π = ∀ {Γ'} → All (λ Γ → Block Π Γ Γ') Π
