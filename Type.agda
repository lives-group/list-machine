open import Function 

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)

module Type where

-- type definitions

data Ty : Set where
  nil      : Ty
  list     : Ty → Ty
  listcons : Ty → Ty

-- syntatic type equality test

list-≡-inv : ∀ {t t'} → (list t) ≡ (list t') → t ≡ t'
list-≡-inv refl = refl

listcons-≡-inv : ∀ {t t'} → (listcons t) ≡ (listcons t') → t ≡ t'
listcons-≡-inv refl = refl

_≟_ : Decidable {A = Ty} _≡_
nil ≟ nil = yes refl
nil ≟ list t' = no (λ ())
nil ≟ listcons t' = no (λ ())
list t ≟ nil = no (λ ())
list t ≟ list t' with t ≟ t'
...| yes refl = yes refl
...| no neq   = no (neq ∘ list-≡-inv)
list t ≟ listcons t' = no (λ ())
listcons t ≟ nil = no (λ ())
listcons t ≟ list t' = no (λ ())
listcons t ≟ listcons t' with t ≟ t'
...| yes refl = yes refl
...| no neq   = no (neq ∘ listcons-≡-inv)
