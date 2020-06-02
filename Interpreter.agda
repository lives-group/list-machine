open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_)
open import Data.List.Relation.Unary.All
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there) renaming (_∷_ to _∷v_)
open import Data.Vec.Relation.Unary.All using () renaming (All to Allv)

open import Function

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_ ; _⊢_ ; _∈_)

open import Ctx
open import LeastSuperType
open import Subtyping
open import Type


module Interpreter (blocks : ℕ) where

open import Instr blocks


-- value definition

data Val : Ty → Set where
  nil : Val nil
  _∷_ : ∀ {t} → Val t → Val (list t) → Val (listcons t)

-- execution environments

Env : Ctx → Set
Env Γ = All Val Γ

PEnv : PCtx → Set
PEnv Π = Allv Env Π


-- small step evaluation

step : ∀ {Π Γ Γ'} → Program Π → Env Γ → Π ⊢ Γ ⇒ Γ' → Env Γ'
step p env (instr-seq i i') = {!!}
step p env (instr-branch-list idx x x₁) = {!!}
step p env (instr-branch-listcons idx x x₁) = {!!}
step p env (instr-branch-nil x x₁ x₂) = {!!}
step p env (instr-fetch-0-new x) = {!!}
step p env (instr-fetch-0-upd x idx) = {!!}
step p env (instr-fetch-1-new x) = {!!}
step p env (instr-fetch-1-upd x idx) = {!!}
step p env (instr-cons-new x x₁ x₂) = {!!}
step p env (instr-cons-upd x x₁ idx x₂) = {!!}
