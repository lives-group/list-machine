open import Data.List
open import Data.Product
open import Data.String

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
Ctx = List (String × Ty)

-- subtyping between contexts

data _⊂_ : Ctx → Ctx → Set where
  env-sub1 : ∀ {Γ Γ'' Γ' t t' x} →
               Γ ≡ ((x , t') ∷ Γ'')  →
               t' <: t         →
               Γ'' ⊂ Γ'        →
               Γ ⊂ ((x , t) ∷ Γ')
  env-sub2 : ∀ {Γ} → Γ ⊂ []


-- context subtyping inversions lemmas

⊂-[]-left : ∀ {t Γ} → ¬ ([] ⊂ (t ∷ Γ))
⊂-[]-left (env-sub1 () x₁ p)

⊂-∷-inv : ∀ {t t' Γ Γ' x} → ((x , t) ∷ Γ) ⊂ ((x , t') ∷ Γ') → (t <: t') × (Γ ⊂ Γ')
⊂-∷-inv (env-sub1 refl x₁ p) = x₁ , p

-- decidability of subtyping between contexts

open import Data.String.Properties

postulate 
  _⊂?_ : Decidable {A = Ctx} _⊂_

{-
Γ ⊂? [] = yes env-sub2
[] ⊂? ((x , t) ∷ Γ') = no ⊂-[]-left
((x , t) ∷ Γ) ⊂? ((x' , t') ∷ Γ') with x Data.String.≟ x' | t <:? t' | Γ ⊂? Γ'
... | yes refl | yes t<:t' | yes Γ⊂Γ' = yes (env-sub1 refl t<:t' Γ⊂Γ')
... | no neq | _ | _ = no (neq ∘ {!!})
... | _ | no neq | _ = no (neq ∘ proj₁ ∘ {!!})
... | _ | _ | no neq = no (neq ∘ proj₂ ∘ {!⊂-∷-inv!})
-}

{-
...| yes t<:t' | yes Γ⊂Γ' = yes (env-sub1 refl t<:t' Γ⊂Γ')
...| no  neq   | _        = no (neq ∘ proj₁ ∘ ⊂-∷-inv)
...| _         | no neq   = no (neq ∘ proj₂ ∘ ⊂-∷-inv)
-}

{-
_⊂?_ : Decidable {A = Ctx} _⊂_
Γ ⊂? [] = yes env-sub2
[] ⊂? ((x , t) ∷ Γ') = no ⊂-[]-left
((x , t) ∷ Γ) ⊂? ((x' , t') ∷ Γ') with t <:? t' | Γ ⊂? Γ'
...| yes t<:t' | yes Γ⊂Γ' = yes (env-sub1 refl t<:t' Γ⊂Γ')
...| no  neq   | _        = no (neq ∘ proj₁ ∘ ⊂-∷-inv)
...| _         | no neq   = no (neq ∘ proj₂ ∘ ⊂-∷-inv)
-}
