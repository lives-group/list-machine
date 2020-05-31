open import Function 

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)

open import Type

module Subtyping where

-- subtype definition

data _<:_ : Ty → Ty → Set where
  <:-refl : ∀ {t} → t <: t
  <:-nil  : ∀ {t} → nil <: t
  <:-list : ∀ {t t'} →
            t <: t'  →
            (list t) <: (list t')
  <:-listcons : ∀ {t t'} →
                t <: t'  →
                (listcons t) <: list t'
  <:-listmixed : ∀ {t t'} →
                 t <: t'  →
                 (listcons t) <: (listcons t')

-- inversion lemmas

list-<:-inv : ∀ {t t'} → (list t) <: (list t') → t <: t'
list-<:-inv <:-refl = <:-refl
list-<:-inv (<:-list p) = p

list-cons-<:-inv : ∀ {t t'} → (listcons t) <: (list t') → t <: t'
list-cons-<:-inv (<:-listcons p) = p

list-mixed-<:-inv : ∀ {t t'} → (listcons t) <: (listcons t') → t <: t'
list-mixed-<:-inv <:-refl = <:-refl
list-mixed-<:-inv (<:-listmixed p) = p

-- subtyping test

_<:?_ : Decidable {A = Ty} _<:_
nil <:? t' = yes <:-nil
list t <:? nil = no (λ ())
list t <:? list t' with t <:? t'
...| yes t<:t' = yes (<:-list t<:t')
...| no  n<:   = no (n<: ∘ list-<:-inv)
list t <:? listcons t' = no (λ ())
listcons t <:? nil = no (λ ())
listcons t <:? list t' with t <:? t'
...| yes t<:t' = yes (<:-listcons t<:t')
...| no n<: = no (n<: ∘ list-cons-<:-inv)
listcons t <:? listcons t' with t <:? t'
...| yes t<:t' = yes (<:-listmixed t<:t')
...| no n<: = no (n<: ∘ list-mixed-<:-inv)


-- properties of subtyping

<:-trans : ∀ {t1 t2 t3} → t1 <: t2 → t2 <: t3 → t1 <: t3
<:-trans {nil} {t2} {t3} p1 p2 = <:-nil
<:-trans {list t1} {list .t1} {t3} <:-refl p2 = p2
<:-trans {list t1} {list t2} {.(list t2)} (<:-list p1) <:-refl = <:-list p1
<:-trans {list t1} {list t2} {.(list _)} (<:-list p1) (<:-list p2) = <:-list (<:-trans p1 p2)
<:-trans {listcons t1} {list t2} {.(list t2)} (<:-listcons p1) <:-refl = <:-listcons p1
<:-trans {listcons t1} {list t2} {.(list _)} (<:-listcons p1) (<:-list p2) = <:-listcons (<:-trans p1 p2)
<:-trans {listcons t1} {listcons .t1} {t3} <:-refl p2 = p2
<:-trans {listcons t1} {listcons t2} {.(listcons t2)} (<:-listmixed p1) <:-refl = <:-listmixed p1
<:-trans {listcons t1} {listcons t2} {.(list _)} (<:-listmixed p1) (<:-listcons p2) = <:-listcons (<:-trans p1 p2)
<:-trans {listcons t1} {listcons t2} {.(listcons _)} (<:-listmixed p1) (<:-listmixed p2) = <:-listmixed (<:-trans p1 p2)
