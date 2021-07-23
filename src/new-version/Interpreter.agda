open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional hiding (_∷=_)
open import Data.List.Relation.Unary.All renaming (All to All-list ; lookup to lookupL)
open import Data.List.Relation.Unary.All.Properties hiding ([]=⇒lookup)
open import Data.List.Relation.Unary.Any

open import Data.Vec renaming (lookup to lookupv)
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.All renaming (lookup to lookupA)
open import Data.Vec.Relation.Unary.All.Properties

open import Relation.Binary.PropositionalEquality

module Interpreter where

    open import Type
    open import Instr
    open import UInstr
    open import Subtyping
    open import LeastSuperType

    Env : Ctx → Set

    data Val : Ty → Set where
      nil : Val nil
      []v : ∀ {t} → Val (list t)
      _∷_ : ∀ {t} → Val t → Val (list t) → Val (listcons t)
      _∷v_ : ∀ {t} → Val t → Val (list t) → Val (list t)
      cont : ∀ {Γ} → Env Γ → Val (cont Γ)
      top  : ∀ {t} → Val t → Val top

    -- execution environments

    Env Γ = All-list Val Γ

    PEnv : ∀ {n} → PCtx n → Set
    PEnv Π = All Env Π

    -- subsumption

    postulate sub-env : ∀ {Γ Γ'} → Γ' ⊂ Γ → Env Γ → Env Γ'

    ⊂-Env : ∀ {Γ Γ'} → Γ ⊂ Γ' → Env Γ → Env Γ'

    <:-val : ∀ {t t' : Ty} → t <: t' → Val t → Val t'
    <:-val <:-top v = top v
    <:-val (<:-cont p) (cont env)
      = cont (sub-env p env)
    <:-val <:-refl v = v
    <:-val <:-nil v = []v
    <:-val (<:-list p) []v = []v
    <:-val (<:-list p) (v ∷v vs) = <:-val p v ∷v <:-val (<:-list p) vs
    <:-val (<:-listcons p) (v ∷ vs) = <:-val p v ∷v <:-val (<:-list p) vs
    <:-val (<:-listmixed p) (v ∷ vs) = <:-val p v ∷ <:-val (<:-list p) vs


    ⊂-Env (env-sub1 refl x₁ p) (v ∷ env) = <:-val x₁ v ∷ ⊂-Env p env
    ⊂-Env env-sub2 env = []


    -- updating the environment

    update-env : ∀ {τ τ′ Γ} → Env Γ → (i : τ′ ∈ Γ) → Val τ → Env (i ∷= τ)
    update-env (x ∷ xs) (here px₁) v = v ∷ xs
    update-env (x ∷ xs) (there i) v = x ∷ update-env xs i v

    Fuel = ℕ

    run-step : ∀ {n}{Π : PCtx n}{Γ Γ′} → Fuel → PEnv Π → Program Π → Env Γ → Block Π Γ Γ′ → Maybe (Env Γ′)
    run-step zero Π prog env b = nothing
    run-step (suc n) Π prog env block-halt = just env
    run-step (suc n) Π prog env (block-jump {l = l} x x₁)
      = run-step n Π prog (lookupA l Π) (lookupA l prog)
    run-step (suc n) Π prog env (block-seq (instr-seq x x₁) b) = run-step n Π prog env (block-seq x (block-seq x₁ b))
    run-step (suc n) Π prog env (block-seq (instr-branch-list {l = l} idx x x₁) b) with lookupL env idx
    ... | []v rewrite sym ([]=⇒lookup x)
      = run-step n Π prog (⊂-Env x₁ (update-env env idx nil)) (lookupA l prog)
    ... | v ∷v vs = run-step n Π prog (update-env env idx (v ∷ vs)) b
    run-step (suc n) Π prog env (block-seq (instr-branch-listcons idx x x₁) b)
      = run-step n Π prog env b
    run-step (suc n) Π prog env (block-seq (instr-branch-nil {l = i} x x₁ x₂) b) rewrite sym ([]=⇒lookup x₁)
      = run-step n Π prog (⊂-Env x₂ env) (lookupA i prog)
    run-step (suc n) Π prog env (block-seq (instr-fetch-0-new x) b) with lookupL env x
    ...| v ∷ vs = run-step n Π prog (v ∷ env) b
    run-step (suc n) Π prog env (block-seq (instr-fetch-0-upd x idx) b) with lookupL env x
    ...| v ∷ vs = run-step n Π prog (update-env env idx v) b
    run-step (suc n) Π prog env (block-seq (instr-fetch-1-new x) b) with lookupL env x
    ...| v ∷ vs = run-step n Π prog (vs ∷ env) b
    run-step (suc n) Π prog env (block-seq (instr-fetch-1-upd x idx) b) with lookupL env x
    ...| v ∷ vs = run-step n Π prog (update-env env idx vs) b
    run-step (suc n) Π prog env (block-seq (instr-cons-new x x₁ x₂) b)
      = run-step n Π prog ((<:-val (list-<:-inv (lub-subtype-left x₂)) (lookupL env x) ∷
                            <:-val (lub-subtype-right x₂) (lookupL env x₁)) ∷ env) b
    run-step (suc n) Π prog env (block-seq (instr-cons-upd x x₁ idx x₂) b)
      = run-step n Π prog (update-env env idx ((<:-val (list-<:-inv (lub-subtype-left x₂)) (lookupL env x)) ∷ (<:-val (lub-subtype-right x₂) (lookupL env x₁)))) b
    run-step (suc n) Π prog env (block-seq (instr-getlabel-0 idx) b) = run-step n Π prog (update-env env idx nil) b
    run-step (suc n) Π prog env (block-seq (instr-getlabel {l = l} idx x) b) rewrite sym ([]=⇒lookup x)
      = run-step n Π prog (update-env env idx (cont (lookupA l Π))) b
