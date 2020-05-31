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
lub-subtype {nil} {nil} {t3} p = <:-nil , <:-nil
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

