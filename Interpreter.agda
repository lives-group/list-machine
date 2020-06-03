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
  []v : ∀ {t} → Val (list t)
  _∷_ : ∀ {t} → Val t → Val (list t) → Val (listcons t)
  _∷v_ :  ∀ {t} → Val t → Val (list t) → Val (list t)

-- subsumption for values

<:-val : ∀ {t t' : Ty} → t <: t' → Val t → Val t'
<:-val <:-refl v = v
<:-val {t' = nil} <:-nil v = v
<:-val {t' = list t'} <:-nil v = []v
<:-val {t' = listcons t'} <:-nil v = <:-val <:-nil v ∷ []v
<:-val (<:-list p) []v = []v
<:-val (<:-list p) (v ∷v v') = <:-val p v ∷v <:-val (<:-list p) v'
<:-val (<:-listcons p) (v ∷ v') = <:-val p v ∷v <:-val (<:-list p) v'
<:-val (<:-listmixed p) (v ∷ v') = <:-val p v ∷ <:-val (<:-list p) v'

-- execution environments

Env : Ctx → Set
Env Γ = All Val Γ

-- subsumption for contexts

⊂-Ctx : ∀ {Γ Γ'} → Γ ⊂ Γ' → Env Γ → Env Γ'
⊂-Ctx (env-sub1 refl x₁ p) (px ∷ env) = <:-val x₁ px ∷ (⊂-Ctx p env)
⊂-Ctx env-sub2 env = []

PEnv : PCtx → Set
PEnv Π = Allv Env Π


-- defining the interpreter


