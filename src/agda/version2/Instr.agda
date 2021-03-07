open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there) renaming (_∷_ to _∷v_)
open import Data.Vec.Relation.Unary.All using (All)
open import Data.String
open import Data.Product

open import Function

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_ ; _⊢_ ; _∈_)

open import LeastSuperType
open import Subtyping
open import Type

module Instr (n : ℕ) where

-- block labels

Label = Fin n

-- program typing

PCtx : Set
PCtx = Vec Ctx n

-- intrinsically typed instructions

infix 0 _⊢_⇒_

data _⊢_⇒_ (Π : PCtx)(Γ : Ctx) : Ctx → Set where
  instr-seq : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ' → Π ⊢ Γ' ⇒ Γ'' → Π ⊢ Γ ⇒ Γ''
  instr-branch-list : ∀ {τ l Γ'} → (idx : list τ ∈ Γ) → Π [ l ]= Γ' → (idx ∷= nil) ⊂ Γ' → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
  instr-branch-listcons : ∀ {τ l Γ₁} → (idx : listcons τ ∈ Γ) → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-fetch-0-new     : ∀ {τ} → listcons τ ∈ Γ → Π ⊢ Γ ⇒ (τ ∷ Γ)
  instr-fetch-0-upd     : ∀ {τ τ'} → listcons τ ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= τ)
  instr-fetch-1-new     : ∀ {τ} → (listcons τ) ∈ Γ → Π ⊢ Γ ⇒ ((list τ) ∷ Γ)
  instr-fetch-1-upd     : ∀ {τ τ'} → (listcons τ) ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= list τ)
  instr-cons-new        : ∀ {τ τ₀ τ₁} → τ₀ ∈ Γ → τ₁ ∈ Γ → (list τ₀ ⊓ τ₁ ~ list τ) → Π ⊢ Γ ⇒ (listcons τ ∷ Γ)
  instr-cons-upd        : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ → τ₁ ∈ Γ → (idx :  τ₂ ∈ Γ) → list τ₀ ⊓ τ₁ ~ list τ → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
  instr-getlabel-0      : ∀ {τ}(idx : τ ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= nil)
  instr-getlabel        : ∀ {l τ Γ₁}(idx : τ ∈ Γ) → Π [ l ]= Γ₁ → Π ⊢ Γ ⇒ (idx ∷= (cont Γ₁))

-- programs

data Block (Π : PCtx) (Γ : Ctx) : Ctx →  Set where
  block-halt            : Block Π Γ Γ
  block-seq             : ∀ {Γ′ Γ''} → Π ⊢ Γ ⇒ Γ′ → Block Π Γ′ Γ'' → Block Π Γ Γ''
  block-jump            : ∀ {l Γ₁} → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Block Π Γ Γ₁

Program : PCtx → Set
Program Π = ∀ {Γ'} → All (λ Γ → Block Π Γ Γ') Π
