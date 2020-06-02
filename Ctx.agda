open import Data.List
open import Data.Product

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_)

open import Subtyping
open import Type

module Ctx where

-- typing contexts

Ctx : Set
Ctx = List Ty

-- subtyping between contexts

data _⊂_ : Ctx → Ctx → Set where
  env-sub1 : ∀ {Γ Γ'' Γ' t t'} →
               Γ ≡ (t' ∷ Γ'')  →
               t' <: t         →
               Γ'' ⊂ Γ'        →
               Γ ⊂ (t ∷ Γ')
  env-sub2 : ∀ {Γ} → Γ ⊂ []


-- context subtyping inversions lemmas

⊂-[]-left : ∀ {t Γ} → ¬ ([] ⊂ (t ∷ Γ))
⊂-[]-left (env-sub1 () x₁ p)

⊂-∷-inv : ∀ {t t' Γ Γ'} → (t ∷ Γ) ⊂ (t' ∷ Γ') → (t <: t') × (Γ ⊂ Γ')
⊂-∷-inv (env-sub1 refl x₁ p) = x₁ , p

-- decidability of subtyping between contexts

_⊂?_ : Decidable {A = Ctx} _⊂_
Γ ⊂? [] = yes env-sub2
[] ⊂? (t ∷ Γ') = no ⊂-[]-left
(t ∷ Γ) ⊂? (t' ∷ Γ') with t <:? t' | Γ ⊂? Γ'
...| yes t<:t' | yes Γ⊂Γ' = yes (env-sub1 refl t<:t' Γ⊂Γ')
...| no  neq   | _        = no (neq ∘ proj₁ ∘ ⊂-∷-inv)
...| _         | no neq   = no (neq ∘ proj₂ ∘ ⊂-∷-inv)
