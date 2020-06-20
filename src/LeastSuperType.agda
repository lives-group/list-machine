open import Data.Product

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)

open import Subtyping
open import Type

module LeastSuperType where

-- least subtype relation

data _⊓_~_ : Ty → Ty → Ty → Set where
  lub-0 : ∀ {t} → t ⊓ t ~ t
  lub-1 : ∀ {t} → (list t) ⊓ nil ~ (list t)
  lub-4 : ∀ {t} → nil ⊓ (list t) ~ (list t)
  lub-2 : ∀ {t t1 t'} →
            (list t) ⊓ (list t1) ~ t' →
            (list t) ⊓ (listcons t1) ~ t'
  lub-2b : ∀ {t t1 t'} →
              (list t) ⊓ (list t1) ~ t' →
              (listcons t) ⊓ (list t1) ~ t'
  lub-3 : ∀ {t t1 t'} →
             t ⊓ t1 ~ t' →
             (list t) ⊓ (list t1) ~ (list t')
  lub-5 : ∀ {t} → (listcons t) ⊓ nil ~ (list t)
  lub-6 : ∀ {t} → nil ⊓ (listcons t) ~ (list t)
  lub-7 : ∀ {t t1 t'} →
            t ⊓ t1 ~ t' →
            (listcons t) ⊓ (listcons t1) ~ (listcons t')

-- relating subtyping and least types

lub-subtype : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → (t1 <: t3) × (t2 <: t3)
lub-subtype {nil} {nil} {.nil} lub-0 = <:-refl , <:-refl
lub-subtype {nil} {list t2} {.(list t2)} lub-4 = <:-nil , <:-refl
lub-subtype {nil} {listcons t2} {.(list t2)} lub-6 = <:-nil , <:-listcons <:-refl
lub-subtype {list t1} {nil} {.(list t1)} lub-1 = <:-refl , <:-nil
lub-subtype {list t1} {list .t1} {.(list t1)} lub-0 = <:-refl , <:-refl
lub-subtype {list t1} {list t2} {.(list _)} (lub-3 p) with lub-subtype p
...| p1 , p2 = <:-list p1 , <:-list p2
lub-subtype {list t1} {listcons t2} {nil} (lub-2 ())
lub-subtype {list t1} {listcons t2} {list t3} (lub-2 p) with lub-subtype p
...| p1 , p2 = p1 , <:-trans (<:-listcons (list-<:-inv p2)) <:-refl
lub-subtype {list t1} {listcons t2} {listcons t3} (lub-2 p) with lub-subtype p
... | () , _
lub-subtype {listcons t1} {nil} {.(list t1)} lub-5 = <:-listcons <:-refl , <:-nil
lub-subtype {listcons t1} {list t2} {list t3} (lub-2b p) with lub-subtype p
...| p1 , p2 = <:-trans (<:-listcons <:-refl) p1 , p2
lub-subtype {listcons t1} {listcons .t1} {.(listcons t1)} lub-0 = <:-refl , <:-refl
lub-subtype {listcons t1} {listcons t2} {.(listcons _)} (lub-7 p) with lub-subtype p
...| p1 , p2 = <:-listmixed p1 , <:-listmixed p2


-- lub is commutative

lub-comm : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → t2 ⊓ t1 ~ t3
lub-comm lub-0 = lub-0
lub-comm lub-1 = lub-4
lub-comm lub-4 = lub-1
lub-comm (lub-2 p) = lub-2b (lub-comm p)
lub-comm (lub-2b p) = lub-2 (lub-comm p)
lub-comm (lub-3 p) = lub-3 (lub-comm p)
lub-comm lub-5 = lub-6
lub-comm lub-6 = lub-5
lub-comm (lub-7 p) = lub-7 (lub-comm p)


lub-of-subtype : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → τ₁ ⊓ τ₂ ~ τ₂
lub-of-subtype <:-refl = lub-0
lub-of-subtype <:-nil = lub-4
lub-of-subtype (<:-list p) = lub-3 (lub-of-subtype p)
lub-of-subtype (<:-listcons p) = lub-2b (lub-3 (lub-of-subtype p))
lub-of-subtype (<:-listmixed p) = lub-7 (lub-of-subtype p)

lub-subtype-left  : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ~ τ₃ → τ₁ <: τ₃
lub-subtype-left lub-0 = <:-refl
lub-subtype-left lub-1 = <:-refl
lub-subtype-left lub-4 = <:-nil
lub-subtype-left (lub-2 p) = lub-subtype-left p
lub-subtype-left (lub-2b lub-0) = lub-subtype-left lub-5
lub-subtype-left (lub-2b (lub-3 p)) = <:-listcons (lub-subtype-left p)
lub-subtype-left (lub-3 p) = <:-list (lub-subtype-left p)
lub-subtype-left lub-5 = <:-listcons <:-refl
lub-subtype-left lub-6 = <:-nil
lub-subtype-left (lub-7 p) = <:-listmixed (lub-subtype-left p)

lub-subtype-right : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ~ τ₃ → τ₂ <: τ₃
lub-subtype-right lub-0 = <:-refl
lub-subtype-right lub-1 = <:-nil
lub-subtype-right lub-4 = <:-refl
lub-subtype-right (lub-2 lub-0) = lub-subtype-right lub-6
lub-subtype-right (lub-2 (lub-3 p)) = <:-listcons (lub-subtype-right p)
lub-subtype-right (lub-2b lub-0) = <:-refl
lub-subtype-right (lub-2b (lub-3 p)) = <:-list (lub-subtype-right p)
lub-subtype-right (lub-3 p) = <:-list (lub-subtype-right p)
lub-subtype-right lub-5 = <:-nil
lub-subtype-right lub-6 = <:-listcons <:-refl
lub-subtype-right (lub-7 p) = <:-listmixed (lub-subtype-right p)

lub-least : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⊓ τ₂ ~ τ₃ → τ₁ <: τ₄ → τ₂ <: τ₄ → τ₃ <: τ₄
lub-least lub-0 p1 p2 = p2
lub-least lub-1 p1 p2 = p1
lub-least lub-4 p1 p2 = p2
lub-least (lub-2 lub-0) <:-refl (<:-listcons p2) = <:-refl
lub-least (lub-2 (lub-3 p)) <:-refl (<:-listcons p2) = <:-list (lub-least p <:-refl p2)
lub-least (lub-2 p) (<:-list p1) (<:-listcons p2) = lub-least p (<:-list p1) (<:-list p2)
lub-least (lub-2b p) (<:-listcons p1) <:-refl = lub-least p (<:-list p1) <:-refl
lub-least (lub-2b p) (<:-listcons p1) (<:-list p2) = lub-least p (<:-list p1) (<:-list p2)
lub-least (lub-3 p) <:-refl <:-refl = <:-list (lub-least p <:-refl <:-refl)
lub-least (lub-3 p) <:-refl (<:-list p2) = <:-list (lub-least p <:-refl p2)
lub-least (lub-3 p) (<:-list p1) <:-refl = <:-list (lub-least p p1 <:-refl)
lub-least (lub-3 p) (<:-list p1) (<:-list p2) = <:-list (lub-least p p1 p2)
lub-least lub-5 (<:-listcons p1) <:-nil = <:-list p1
lub-least lub-6 <:-nil (<:-listcons p2) = <:-list p2
lub-least (lub-7 p) <:-refl <:-refl = <:-listmixed (lub-least p <:-refl <:-refl)
lub-least (lub-7 p) <:-refl (<:-listmixed p2) = <:-listmixed (lub-least p <:-refl p2)
lub-least (lub-7 p) (<:-listcons p1) (<:-listcons p2) = <:-listcons (lub-least p p1 p2)
lub-least (lub-7 p) (<:-listmixed p1) <:-refl = <:-listmixed (lub-least p p1 <:-refl)
lub-least (lub-7 p) (<:-listmixed p1) (<:-listmixed p2) = <:-listmixed (lub-least p p1 p2)

-- calculating the least subtype

lub : (t1 t2 : Ty) → ∃ (λ t → t1 ⊓ t2 ~ t)
lub nil nil = nil , lub-0
lub nil (list t2) = list t2 , lub-4
lub nil (listcons t2) = list t2 , lub-6
lub (list t1) nil = list t1 , lub-1
lub (list t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-3 p 
lub (list t1) (listcons t2) with lub t1 t2
...| t3 , p = list t3 , lub-2 (lub-3 p)
lub (listcons t1) nil = list t1 , lub-5
lub (listcons t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-2b (lub-3 p)
lub (listcons t1) (listcons t2) with lub t1 t2
...| t3 , p = listcons t3 , lub-7 p
