open import Data.Nat renaming (_≟_ to _≟n_)
open import Data.List
open import Data.Product
open import Data.String renaming (_≟_ to _≟s_)

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)

module Type where

-- type definitions

Ctx : Set

data Ty : Set where
  nil      : Ty
  list     : Ty → Ty
  listcons : Ty → Ty
  top      : Ty
  bot      : Ty
  cont     : Ctx → Ty

-- we define contexts here

Ctx = List (ℕ × Ty)

-- syntatic type equality test

list-≡-inv : ∀ {t t'} → (list t) ≡ (list t') → t ≡ t'
list-≡-inv refl = refl

listcons-≡-inv : ∀ {t t'} → (listcons t) ≡ (listcons t') → t ≡ t'
listcons-≡-inv refl = refl

cont-≡-inv : ∀ {ts ts'} → (cont ts) ≡ (cont ts') → ts ≡ ts'
cont-≡-inv refl = refl

∷-≡-inv : ∀ {A : Set}{x y : A}{xs ys : List A} →
          x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-≡-inv refl = refl , refl

×-≡-inv : ∀ {A B : Set}{x x' : A}{y y' : B} → (x , y) ≡ (x' , y') → x ≡ x' × y ≡ y'
×-≡-inv refl = refl , refl

dec : ∀ {l l'}{A : Set l}{B : Set l'} →
      Dec A → (A → B) → (¬ A → B) → B
dec (yes p) f g = f p
dec (no q) f g = g q

_≟_ : Decidable {A = Ty} _≡_

postulate 
  _≟L_ : Decidable {A = Ctx} _≡_

nil ≟ nil = yes refl
nil ≟ list t' = no (λ ())
nil ≟ listcons t' = no (λ ())
nil ≟ top = no (λ ())
nil ≟ bot = no (λ ())
nil ≟ cont x = no (λ ())
list t ≟ nil = no (λ ())
list t ≟ list t' = dec (t ≟ t')
                       (yes ∘ cong list)
                       (λ n → no (λ q → n (list-≡-inv q)))
list t ≟ listcons t' = no (λ ())
list t ≟ top = no (λ ())
list t ≟ bot = no (λ ())
list t ≟ cont x = no (λ ())
listcons t ≟ nil = no (λ ())
listcons t ≟ list t' = no (λ ())
listcons t ≟ listcons t' = dec (t ≟ t')
                               (yes ∘ cong listcons)
                               (λ n → no (λ q → n (listcons-≡-inv q)))
listcons t ≟ top = no (λ ())
listcons t ≟ bot = no (λ ())
listcons t ≟ cont x = no (λ ())
top ≟ nil = no (λ ())
top ≟ list t' = no (λ ())
top ≟ listcons t' = no (λ ())
top ≟ top = yes refl
top ≟ bot = no (λ ())
top ≟ cont x = no (λ ())
bot ≟ nil = no (λ ())
bot ≟ list t' = no (λ ())
bot ≟ listcons t' = no (λ ())
bot ≟ top = no (λ ())
bot ≟ bot = yes refl
bot ≟ cont ts = no (λ ())
cont ts ≟ nil = no (λ ())
cont ts ≟ list t' = no (λ ())
cont ts ≟ listcons t' = no (λ ())
cont ts ≟ top = no (λ ())
cont ts ≟ bot = no (λ ())
cont ts ≟ cont ts' = dec (ts ≟L ts')
                         (yes ∘ cong cont)
                         (λ q → no λ p → q (cont-≡-inv p))

{-
[] ≟L [] = yes refl
[] ≟L (x ∷ ts') = no (λ ())
(x ∷ ts) ≟L [] = no (λ ())
((x , t) ∷ ts) ≟L ((x' , t') ∷ ts') with x ≟n x' | t ≟ t' | ts ≟L ts'
... | yes p | yes q | yes r rewrite p | q | r  = yes refl
... | yes p | yes q | no r rewrite p | q = no (r ∘ proj₂ ∘ ∷-≡-inv)
... | yes p | no  q | _ = no {!!}
... | no  p | _     | _ = no {!!}
-}

-- ...| yes p | yes k rewrite p | k = yes refl
-- ...| yes p | no k  rewrite p = no (k ∘ proj₂ ∘ ∷-≡-inv)
-- ...| no  p | _ = no (p ∘ proj₁ ∘ ∷-≡-inv)
