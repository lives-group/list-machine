open import Data.Fin
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_)
open import Data.List.Relation.Unary.All
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there) renaming (_∷_ to _∷v_ ; lookup to lookupv)
open import Data.Vec.Properties using ([]=⇒lookup)
open import Data.Vec.Relation.Unary.All using () renaming (All to Allv ; lookup to lookupA)

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
<:-val {t' = list t'} <:-nil v = []v
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

-- updating the environment

update-env : ∀ {τ τ′ Γ} → Env Γ → (i : τ′ ∈ Γ) → Val τ → Env (i ∷= τ)
update-env (x All.∷ xs) (here px₁) v = v All.∷ xs
update-env (x All.∷ xs) (there i) v = x All.∷ update-env xs i v

-- defining the interpreter

Fuel = ℕ

run-step : ∀ {Π Γ Γ′} → Fuel → Program Π → Env Γ → Block Π Γ Γ′ → Maybe (Env Γ′)
run-step zero p env b = nothing
run-step (suc n) p env block-halt = just env
run-step (suc n) p env (block-seq (instr-seq i₁ i₂) b) = run-step n p env (block-seq i₁ (block-seq i₂ b))
run-step {Π} (suc n) p env (block-seq (instr-branch-list {τ} {i} v l s) b) with lookup env v 
... | []v rewrite sym ([]=⇒lookup l) = run-step n p (⊂-Ctx s (update-env env v nil)) (lookupA i p)
... | v₁ ∷v v₂ = run-step n p (update-env env v (v₁ ∷ v₂)) b
run-step (suc n) p env (block-seq (instr-branch-listcons v l s) b) = run-step n p env b
run-step (suc n) p env (block-seq (instr-branch-nil {l = i} v l s) b) rewrite sym ([]=⇒lookup l)
  = run-step n p (⊂-Ctx s env) (lookupA i p)
run-step (suc n) p env (block-seq (instr-fetch-0-new v) b) with lookup env v
...| v₁ ∷ v₂ = run-step n p (v₁ ∷ env) b
run-step (suc n) p env (block-seq (instr-fetch-0-upd {τ} v v') b) with lookup env v
...| v₁ ∷ v₂ = run-step n p (update-env env v' v₂) b
run-step (suc n) p env (block-seq (instr-fetch-1-new v) b) with lookup env v
...| v₁ ∷ v₂ = run-step n p (v₂ ∷ env) b
run-step (suc n) p env (block-seq (instr-fetch-1-upd v v') b) with lookup env v
...| v₁ ∷ v₂ = run-step n p (update-env env v' v₂) b
run-step (suc n) p env (block-seq (instr-cons-new v₀ v₁ s) b)
  = run-step n p ((<:-val (list-<:-inv (lub-subtype-left (lub-of-subtype (lub-subtype-left s)))) (lookup env v₀)
                   ∷ <:-val (lub-subtype-right s) (lookup env v₁)) ∷ env) b
run-step (suc n) p env (block-seq (instr-cons-upd {τ = τ} v₀ v₁ v' s) b)
  = run-step n p (update-env env v' (<:-val (list-<:-inv (lub-subtype-left (lub-of-subtype (lub-subtype-left s)))) (lookup env v₀)
                  ∷ <:-val (lub-subtype-right s) (lookup env v₁))) b
run-step (suc n) p env (block-jump {l = i} l s) rewrite sym ([]=⇒lookup l) = run-step n p (⊂-Ctx s env) (lookupA i p)
