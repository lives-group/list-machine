open import Data.List using ([] ; _∷_)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Sum renaming (_⊎_ to Either ; inj₁ to left ; inj₂ to right)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality using (refl ; _≡_)
open import Relation.Nullary

module TypeChecker (blocks : ℕ) where

open import Instr blocks
open import UInstr blocks
open import Ctx
open import Type
open import LeastSuperType

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

TypeError : Set
TypeError = String

TC : Set → Set
TC i = Either TypeError i

type-error : ∀ {i} → TypeError → TC i
type-error = left

data Checked (Π : PCtx) (Γ : Ctx) : UInstr → Set where
  ok : ∀ {Γ'} → (b : Block Π Γ Γ') → Checked Π Γ (forget-types b)

data CheckedInstr (Π : PCtx) (Γ : Ctx) : UInstr → Set where
  ok : ∀ {Γ'} → (i : Π ⊢ Γ ⇒ Γ') → CheckedInstr Π Γ (forget-types-instr i)

lookup-var : (Γ : Ctx) → (x : String) → Maybe (∃ λ τ → (x , τ) ∈ Γ)
lookup-var [] x = nothing
lookup-var ((y , τ) ∷ Γ) x with x Data.String.≟ y
... | yes refl = just (τ , here refl)
... | (no ¬p) = Data.Maybe.map (λ v → proj₁ v , there (proj₂ v)) (lookup-var Γ x)

check-fetch-field-0 : (Π : PCtx) → (Γ : Ctx) → (v : String) → (v' : String) → TC (CheckedInstr Π Γ (fetch-field-0 v v'))
check-fetch-field-0 Π Γ v v' with lookup-var Γ v , lookup-var Γ v'
... | nothing , _ = type-error ("check-fetch-field-0: variable out of scope: " ++ v)
... | just (nil , _) , _ = type-error "check-fetch-field-0: type error"
... | just (list τ , _) , _ = type-error "check-fetch-field-0: type error"
... | just (listcons τ , idx) , nothing = right (ok (instr-fetch-0-new idx))
... | just (listcons τ , idx) , just (τ' , idx') = right (ok (instr-fetch-0-upd idx idx'))

check-fetch-field-1 : (Π : PCtx) → (Γ : Ctx) → (v : String) → (v' : String) → TC (CheckedInstr Π Γ (fetch-field-1 v v'))
check-fetch-field-1 Π Γ v v' with lookup-var Γ v , lookup-var Γ v'
... | nothing , _ = type-error ("check-fetch-field-1: variable out of scope: " ++ v)
... | just (nil , _) , _ = type-error "check-fetch-field-1: type error"
... | just (list τ , _) , _ = type-error "check-fetch-field-1: type error"
... | just (listcons τ , idx) , nothing = right (ok (instr-fetch-1-new idx))
... | just (listcons τ , idx) , just (τ' , idx') = right (ok (instr-fetch-1-upd idx idx'))

check-cons : (Π : PCtx) → (Γ : Ctx) → (v₀ : String) → (v₁ : String) → (v' : String) → TC (CheckedInstr Π Γ (cons v₀ v₁ v'))
check-cons Π Γ v₀ v₁ v' with lookup-var Γ v₀ , lookup-var Γ v₁ , lookup-var Γ v'
... | nothing , _ , _ = type-error ("check-cons: variable out of scope: " ++ v₀)
... | just v₀' , nothing , _ = type-error ("check-cons: variable out of scope: " ++ v₁)
... | just (τ₀ , idx₀) , just (τ₁ , idx₁) , nothing with lub (list τ₀) τ₁
...   | nil , ls = type-error ("check-cons: error calculating least supertype.")
...   | list τ , ls = right (ok (instr-cons-new idx₀ idx₁ ls))
...   | listcons τ , ls = type-error ("check-cons: error calculating least supertype.")
check-cons Π Γ v₀ v₁ v' | just (τ₀ , idx₀) , just (τ₁ , idx₁) , just (τ' , idx') with lub (list τ₀) τ₁
...   | nil , ls = type-error ("check-cons: error calculating least supertype.")
...   | list τ , ls = right (ok (instr-cons-upd idx₀ idx₁ idx' ls))
...   | listcons τ , ls = type-error ("check-cons: error calculating least supertype.")

check-branch-if-nil : (Π : PCtx) → (Γ : Ctx) → (v : String) → (l : Label) → TC (CheckedInstr Π Γ (branch-if-nil v l))
check-branch-if-nil Π Γ v l with inspect (Data.Vec.lookup Π l)
check-branch-if-nil Π Γ v l | Γ₁ with≡ p with lookup-var Γ v
check-branch-if-nil Π Γ v l | Γ₁ with≡ p | nothing = type-error "check-branch-if-nil: variable out of scope."
check-branch-if-nil Π Γ v l | Γ₁ with≡ p | just (nil , idx) with Γ ⊂? Γ₁
... | no ¬p = type-error "check-branch-if-nil[nil]: context subtyping error."
... | yes Γ⊂Γ₁ = right (ok (instr-branch-nil idx (lookup⇒[]= l Π p) Γ⊂Γ₁))
check-branch-if-nil Π Γ v l | Γ₁ with≡ p | just (list τ , idx) with (idx ∷= (v , nil)) ⊂? Γ₁
... | no ¬p = type-error "check-branch-if-nil[list τ]: context subtyping error."
... | yes Γ⊂Γ₁ = right (ok (instr-branch-list idx (lookup⇒[]= l Π p) Γ⊂Γ₁))
check-branch-if-nil Π Γ v l | Γ₁ with≡ p | just (listcons τ , idx) with (idx ∷= (v , nil)) ⊂? Γ₁
... | no ¬p = type-error "check-branch-if-nil[listcons τ]: context subtyping error."
... | yes Γ⊂Γ₁ = right (ok (instr-branch-listcons idx (lookup⇒[]= l Π p) Γ⊂Γ₁))

check-jump : (Π : PCtx) → (Γ : Ctx) → (l : Label) → TC (Checked Π Γ (jump l))
check-jump Π Γ l with inspect (Data.Vec.lookup Π l)
... | Γ₁ with≡ p with Γ ⊂? Γ₁
...   | no ¬p = type-error "check-jump: context subtyping error."
...   | yes Γ⊂Γ₁ = right (ok (block-jump (lookup⇒[]= l Π p) Γ⊂Γ₁))

type-check-instr : (Π : PCtx) → (Γ : Ctx) → (i : UInstr) → TC (CheckedInstr Π Γ i)
type-check-instr Π Γ (branch-if-nil v l) = check-branch-if-nil Π Γ v l
type-check-instr Π Γ (fetch-field-0 v v') = check-fetch-field-0 Π Γ v v'
type-check-instr Π Γ (fetch-field-1 v v') = check-fetch-field-1 Π Γ v v'
type-check-instr Π Γ (cons v₀ v₁ v') = check-cons Π Γ v₀ v₁ v'
type-check-instr Π Γ (seq i₁ i₂) with type-check-instr Π Γ i₁
... | left e = type-error ("type-check-instr[seq]: " ++ e)
... | right (ok {Γ'} i₁') with type-check-instr Π Γ' i₂
...   | left e = type-error ("type-check-instr[seq]" ++ e)
...   | right (ok i₂') = right (ok (instr-seq i₁' i₂'))
type-check-instr Π Γ i = type-error "type-check-instr: invalid instruction."

type-check-block : (Π : PCtx) → (Γ : Ctx) → (i : UInstr) → TC (Checked Π Γ i)
type-check-block Π Γ (jump l) = check-jump Π Γ l
type-check-block Π Γ halt = right (ok block-halt)
type-check-block Π Γ (seq i₁ i₂) with type-check-instr Π Γ i₁
... | left e = type-error ("type-check-block[seq]: " ++ e)
... | right (ok {Γ'} i₁') with type-check-block Π Γ' i₂
...   | left e = type-error ("type-check-block[seq]: " ++ e)
...   | right (ok i₂') = right (ok (block-seq i₁' i₂'))
type-check-block Π Γ b = type-error "type-check-block: invalid instruction."
