open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Vec
open import Data.Vec.Relation.Unary.All

open import Relation.Binary.PropositionalEquality

module Sample where

open import Type
open import Instr
open import UInstr


-- number of blocks in the sample program


blocks = 3


-- definining the labels of the sample program

L₀ : Label blocks
L₀ = zero

L₁ : Label blocks
L₁ = suc zero

L₂ : Label blocks
L₂ = suc (suc zero)

-- initial typing context information

Γ₀ : Ctx
Γ₀ = nil ∷ []

Γ₁ : Ctx
Γ₁ = nil ∷ list nil ∷ []

Γ₂ : Ctx
Γ₂ = []

-- variable definitions

v00 : nil ∈ Γ₀
v00 = here refl

v10 : nil ∈ Γ₁
v10 = here refl

v11 : list nil ∈ Γ₁
v11 = there (here refl)

-- initial program context

Π-sample : PCtx blocks
Π-sample = Γ₀ ∷ Γ₁ ∷ Γ₂ ∷ []


-- program blocks definitions

p-sample : UInstr blocks
p-sample = seq (cons 0 0 1)
               (seq (cons 0 1 1)
               (seq (cons 0 1 1)
               (seq (jump zero L₁)
               (seq (branch-if-nil 1 L₂)
               (seq (fetch-field-1 1 1)
               (seq (branch-if-nil 0 L₁)
               (seq (jump 0 L₂) halt)))))))
