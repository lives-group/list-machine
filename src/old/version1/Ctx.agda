open import Data.List
open import Data.Product
open import Data.String renaming (_≟_ to _≟s_)

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

⊂-∷-inv : ∀ {t t' Γ Γ' x x'} → ((x , t) ∷ Γ) ⊂ ((x' , t') ∷ Γ') → (x ≡ x') × (t <: t') × (Γ ⊂ Γ')
⊂-∷-inv (env-sub1 refl x₁ p) = refl , x₁ , p

-- decidability of subtyping between contexts

_⊂?_ : Decidable {A = Ctx} _⊂_
Γ ⊂? [] = yes env-sub2
[] ⊂? ((s , t) ∷ Γ') = no ⊂-[]-left
((s , t) ∷ Γ) ⊂? ((s' , t') ∷ Γ') with s ≟s s' | t <:? t' | Γ ⊂? Γ' 
...| yes refl | yes p    | yes q    = yes (env-sub1 refl p q)
...| yes refl | yes p    | no neq   = no (neq ∘ proj₂ ∘ proj₂ ∘ ⊂-∷-inv)
...| yes refl | no  neq  | _        = no (neq ∘ proj₁ ∘ proj₂ ∘ ⊂-∷-inv)
...| no  neq  | _        | _        = no (neq ∘ proj₁ ∘ ⊂-∷-inv)
