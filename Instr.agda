open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there) renaming (_∷_ to _∷v_)

open import Function

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_ ; _⊢_ ; _∈_)

open import Ctx
open import LeastSuperType
open import Subtyping
open import Type

module Instr (blocks : ℕ) where


-- block labels

Label : Set
Label = Fin blocks

-- program typing

PCtx : Set
PCtx = Vec Ctx blocks

-- intrinsically typed instructions

infix 0 _⊢_⇒_

data _⊢_⇒_ (Π : PCtx)(Γ : Ctx) : Ctx → Set where
  instr-seq : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ' → Π ⊢ Γ' ⇒ Γ'' → Π ⊢ Γ ⇒ Γ''
  instr-branch-list : ∀ {τ l Γ₁} → (idx : (list τ) ∈ Γ) → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁ → Π ⊢ Γ ⇒ (idx ∷= nil)  
  instr-branch-listcons : ∀ {τ l Γ₁} → (idx : (listcons τ) ∈ Γ) → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-fetch-0-new     : ∀ {τ} → (listcons τ) ∈ Γ → Π ⊢ Γ ⇒ (τ ∷ Γ)
  instr-fetch-0-upd     : ∀ {τ τ′} → (listcons τ) ∈ Γ → (idx : τ′ ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= list τ)
  instr-fetch-1-new     : ∀ {τ} → (listcons τ) ∈ Γ → Π ⊢ Γ ⇒ (list τ ∷ Γ)
  instr-fetch-1-upd     : ∀ {τ τ′} → (listcons τ) ∈ Γ → (idx : τ′ ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= list τ)
  instr-cons-new        : ∀ {τ τ₀ τ₁} → τ₀ ∈ Γ → τ₁ ∈ Γ → list τ₀ ⊓ τ₁ ~ list τ → Π ⊢ Γ ⇒ (listcons τ ∷ Γ)
  instr-cons-upd        : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ → τ₁ ∈ Γ → (idx : τ₂ ∈ Γ) → list τ₀ ⊓ τ₁ ~ list τ → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
  

-- blocks

data Block (Π : PCtx) (Γ : Ctx) : Set where
  block-halt            : Block Π Γ
  block-seq             : ∀ {Γ′} → Π ⊢ Γ ⇒ Γ′ → Block Π Γ′ → Block Π Γ
  block-jump            : ∀ {l Γ₁} → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Block Π Γ

data Program (Π : PCtx) : Set where
  blocks-label : ∀ {l Γ} → Π [ l ]= Γ → Block Π Γ → Program Π → Program Π
  blocks-empty : Program Π


