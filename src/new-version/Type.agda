open import Data.List
open import Data.List.Properties
open import Data.Product

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Type where

 -- types and contexts

 Ctx : Set

 data Ty : Set where
   nil      : Ty
   list     : Ty  → Ty
   listcons : Ty  → Ty
   top      : Ty
   bot      : Ty
   cont     : Ctx → Ty

 Ctx = List Ty

 -- decidable equality for types

 list-≡-inv : ∀ {t t' : Ty} → (list t) ≡ (list t') → t ≡ t'
 list-≡-inv refl = refl

 listcons-≡-inv : ∀ {t t' : Ty} → (listcons t) ≡ (listcons t') → t ≡ t'
 listcons-≡-inv refl = refl

 cont-≡-inv : ∀ {ts ts' : Ctx} →
              (cont ts) ≡ (cont ts') → ts ≡ ts'
 cont-≡-inv refl = refl

 ×-≡-inv : ∀ {A B : Set}{x x' : A}{y y' : B} →
             (x , y) ≡ (x' , y') → x ≡ x' × y ≡ y'
 ×-≡-inv refl = refl , refl


 dec : ∀ {l l'}{A : Set l}{B : Set l'} →
       Dec A → (A → B) → (¬ A → B) → B
 dec (yes p) f g = f p
 dec (no q) f g = g q


 _≟T_ : Decidable {A = Ty} _≡_
 _≟C_ : Decidable {A = Ctx} _≡_

 nil ≟T nil = yes refl
 nil ≟T list t' = no (λ ())
 nil ≟T listcons t' = no (λ ())
 nil ≟T top = no (λ ())
 nil ≟T bot = no (λ ())
 nil ≟T cont x = no (λ ())
 list t ≟T nil = no (λ ())
 list t ≟T list t' = dec (t ≟T t')
                         (yes ∘ cong list)
                         (λ neq → no (neq ∘ list-≡-inv))
 list t ≟T listcons t' = no (λ ())
 list t ≟T top = no (λ ())
 list t ≟T bot = no (λ ())
 list t ≟T cont x = no (λ ())
 listcons t ≟T nil = no (λ ())
 listcons t ≟T list t' = no (λ ())
 listcons t ≟T listcons t' = dec (t ≟T t')
                                 (yes ∘ cong listcons)
                                 (λ neq → no (neq ∘ listcons-≡-inv))
 listcons t ≟T top = no (λ ())
 listcons t ≟T bot = no (λ ())
 listcons t ≟T cont x = no (λ ())
 top ≟T nil = no (λ ())
 top ≟T list t' = no (λ ())
 top ≟T listcons t' = no (λ ())
 top ≟T top = yes refl
 top ≟T bot = no (λ ())
 top ≟T cont x = no (λ ())
 bot ≟T nil = no (λ ())
 bot ≟T list t' = no (λ ())
 bot ≟T listcons t' = no (λ ())
 bot ≟T top = no (λ ())
 bot ≟T bot = yes refl
 bot ≟T cont x = no (λ ())
 cont x ≟T nil = no (λ ())
 cont x ≟T list t' = no (λ ())
 cont x ≟T listcons t' = no (λ ())
 cont x ≟T top = no (λ ())
 cont x ≟T bot = no (λ ())
 (cont Γ) ≟T (cont Γ') = dec (Γ ≟C Γ')
                             (yes ∘ cong cont)
                             (λ neq → no (neq ∘ cont-≡-inv))


 [] ≟C [] = yes refl
 [] ≟C (y ∷ ys) = no (λ ())
 (x ∷ xs) ≟C [] = no (λ ())
 (t ∷ Γ) ≟C (t' ∷ Γ') with t ≟T t' | Γ ≟C Γ'
 ...| yes eq | yes eq' rewrite eq | eq' = yes refl
 ...| no neq | _ = no (neq ∘ proj₁ ∘ ∷-injective)
 ...| _      | no neq' = no (neq' ∘ proj₂ ∘ ∷-injective)
