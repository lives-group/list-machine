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
