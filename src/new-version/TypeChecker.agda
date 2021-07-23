open import Data.List
open import Data.List.Properties using  (≡-dec ; ∷-injective)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_ ; any?)
open import Data.Nat
open import Data.Product
open import Data.Sum renaming (_⊎_ to Either ; inj₁ to left ; inj₂ to right)
open import Data.Vec
open import Data.Vec.Properties hiding (≡-dec)

open import Function

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary

module TypeChecker where

    open import Type
    open import Subtyping
    open import Instr
    open import UInstr
    open import LeastSuperType

    data Singleton {a} {A : Set a} (x : A) : Set a where
      _with≡_ : (y : A) → x ≡ y → Singleton x

    inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
    inspect x = x with≡ refl

    data TypeError : Set where
      UnexpectedTy : Ty → TypeError
      UndefinedVar : ℕ  → TypeError
      UndefinedLabel : ∀ {n} → Label n → TypeError
      ContextSubtyping : ∀ {Γ Γ'} → ¬ (Γ ⊂ Γ') → TypeError
      InvalidContext : Ctx → TypeError
      InvalidInstr : ∀ {n} → UInstr n → TypeError

    TC : Set → Set
    TC i = Either TypeError i

    type-error : ∀ {i} → Ty → TC i
    type-error = left ∘ UnexpectedTy

    undefined-var : ∀ {i} → ℕ → TC i
    undefined-var = left ∘ UndefinedVar

    undefined-label : ∀ {i n} → Label n → TC i
    undefined-label = left ∘ UndefinedLabel

    context-subtyping : ∀ {i Γ Γ'} → ¬ (Γ ⊂ Γ') → TC i
    context-subtyping = left ∘ ContextSubtyping

    invalid-context : ∀ {i} → Ctx → TC i
    invalid-context = left ∘ InvalidContext

    invalid-instr : ∀ {i n} → UInstr n → TC i
    invalid-instr = left ∘ InvalidInstr

    data Checked {n}(Π : PCtx n) (Γ : Ctx) : UInstr n → Set where
      ok : ∀ {Γ'} → (b : Block Π Γ Γ') → Checked Π Γ (forget-types b)

    data CheckedInstr {n}(Π : PCtx n) (Γ : Ctx) : UInstr n → Set where
      ok : ∀ {Γ'} → (i : Π ⊢ Γ ⇒ Γ') → CheckedInstr Π Γ (forget-types-instr i)

    check-fetch-field-0 : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v : ℕ) → (v' : ℕ) → TC (CheckedInstr Π Γ (fetch-field-0 v v'))
    check-fetch-field-0 Π Γ v v' with lookup-var Γ v | lookup-var Γ v'
    ... | inside nil p | q = type-error nil
    ... | inside (list x) p | q = type-error (list x)
    ... | inside (listcons x) p | inside x₁ p₁ = right (ok (instr-fetch-0-upd p p₁))
    ... | inside (listcons x) p | outside = right (ok (instr-fetch-0-new p))
    ... | inside top p | q = type-error top
    ... | inside bot p | q = type-error bot
    ... | inside (cont x) p | q = type-error (cont x)
    ... | outside | _ = undefined-var v

    check-fetch-field-1 : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v : ℕ) → (v' : ℕ) → TC (CheckedInstr Π Γ (fetch-field-1 v v'))
    check-fetch-field-1 Π Γ v v' with lookup-var Γ v | lookup-var Γ v'
    ... | inside nil p | q = type-error nil
    ... | inside (list x) p | q = type-error (list x)
    ... | inside (listcons x) p | inside x₁ p₁ = right (ok (instr-fetch-1-upd p p₁))
    ... | inside (listcons x) p | outside = right (ok (instr-fetch-1-new p))
    ... | inside top p | q = type-error top
    ... | inside bot p | q = type-error bot
    ... | inside (cont x) p | q = type-error (cont x)
    ... | outside | q = undefined-var v


    check-cons : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v₀ : ℕ) → (v₁ : ℕ) → (v' : ℕ) → TC (CheckedInstr Π Γ (cons v₀ v₁ v'))
    check-cons Π Γ v₀ v₁ v' with lookup-var Γ v₀ | lookup-var Γ v₁ | lookup-var Γ v'
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ with lub (list x) x₁
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | nil , ts = type-error nil
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | list t , ts
      = right (ok (instr-cons-upd p p₁ p₂ ts))
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | listcons t , ts = type-error (listcons t)
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | top , ts = type-error top
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | bot , ts = type-error bot
    check-cons Π Γ .(index p) .(index p₁) .(index p₂) | inside x p | inside x₁ p₁ | inside x₂ p₂ | cont x₃ , ts = type-error (cont x₃)
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside with lub (list x) x₁
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | nil , ts = type-error nil
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | list t , ts
      = right (ok (instr-cons-new p p₁ ts) )
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | listcons t , ts = type-error (listcons t)
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | top , ts = type-error top
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | bot , ts = type-error bot
    check-cons Π Γ .(index p) .(index p₁) v' | inside x p | inside x₁ p₁ | outside | cont x₂ , ts = type-error (cont x₂)
    check-cons Π Γ .(index p) v₁ v' | inside x p | outside | _ = undefined-var v₁
    check-cons Π Γ v₀ v₁ v' | outside | _ | _ = undefined-var v₀


    check-branch-if-nil : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v : ℕ) → (l : Label n) → TC (CheckedInstr Π Γ (branch-if-nil v l))
    check-branch-if-nil Π Γ v l with inspect (Data.Vec.lookup Π l)
    check-branch-if-nil Π Γ v l |  Γ₁ with≡ p with lookup-var Γ v
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside nil p₁ with Γ ⊂? Γ₁
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside nil p₁ | no np = context-subtyping np
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside nil p₁ | yes Γ⊂Γ₁
      = right (ok (instr-branch-nil p₁ (lookup⇒[]= l Π p) Γ⊂Γ₁))
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (list x) p₁ with (p₁ ∷= nil) ⊂? Γ₁
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (list x) p₁ | no np = context-subtyping np
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (list x) p₁ | yes Γ⊂Γ₁
      = right (ok (instr-branch-list p₁ (lookup⇒[]= l Π p) Γ⊂Γ₁))
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (listcons x) p₁ with (p₁ ∷= nil) ⊂? Γ₁
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (listcons x) p₁ | no np = context-subtyping np
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (listcons x) p₁ | yes Γ⊂Γ₁
      = right (ok (instr-branch-listcons p₁ (lookup⇒[]= l Π p) Γ⊂Γ₁))
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside top p₁ = type-error top
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside bot p₁ = type-error bot
    check-branch-if-nil Π Γ .(index p₁) l | Γ₁ with≡ p | inside (cont x) p₁ = type-error (cont x)
    check-branch-if-nil Π Γ v l | Γ₁ with≡ p | outside = undefined-var v

    check-get-label : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v : ℕ) → (l : Label n) → TC (CheckedInstr Π Γ (get-label v l))
    check-get-label Π Γ v l with inspect (Data.Vec.lookup Π l)
    check-get-label Π Γ v l |  Γ₁ with≡ p with lookup-var Γ v
    check-get-label Π Γ .(index p₁) l | Γ₁ with≡ p | inside x p₁ = right (ok (instr-getlabel p₁ (lookup⇒[]= l Π p)))
    check-get-label Π Γ v l | Γ₁ with≡ p | outside = undefined-var v


    check-jump : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (v : ℕ) → (l : Label n) → TC (Checked Π Γ (jump v l))
    check-jump Π Γ n l with inspect (Data.Vec.lookup Π l)
    check-jump Π Γ n l | Γ₁ with≡ p with Γ ⊂? Γ₁
    check-jump Π Γ n l | Γ₁ with≡ p | no np = context-subtyping np
    check-jump Π Γ n l | Γ₁ with≡ p | yes Γ⊂Γ₁ with lookup-var Γ n
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside nil p₁ = type-error nil
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (list x) p₁ = type-error (list x)
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (listcons x) p₁ = type-error (listcons x)
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside top p₁ = type-error top
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside bot p₁ = type-error bot
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (cont x) p₁ with Γ ⊂? x
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (cont x) p₁ | no np1 = context-subtyping np1
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (cont x) p₁ | yes Γ⊂x with ≡-dec _≟T_ Γ₁ x
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (cont x) p₁ | yes Γ⊂x | yes eq rewrite eq
      = right (ok (block-jump {idx = lookup⇒[]= l Π p} p₁ Γ⊂x))
    check-jump Π Γ .(index p₁) l | Γ₁ with≡ p | yes Γ⊂Γ₁ | inside (cont x) p₁ | yes Γ⊂x | no neq = invalid-context x
    check-jump Π Γ n l | Γ₁ with≡ p | yes Γ⊂Γ₁ | outside = undefined-var n

    type-check-instr : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (i : UInstr n) → TC (CheckedInstr Π Γ i)
    type-check-instr Π Γ (branch-if-nil v l) = check-branch-if-nil Π Γ v l
    type-check-instr Π Γ (fetch-field-0 v v') = check-fetch-field-0 Π Γ v v'
    type-check-instr Π Γ (fetch-field-1 v v') = check-fetch-field-1 Π Γ v v'
    type-check-instr Π Γ (get-label v l) =  check-get-label Π Γ v l
    type-check-instr Π Γ (cons v₀ v₁ v') = check-cons Π Γ v₀ v₁ v'
    type-check-instr Π Γ (seq i₁ i₂) with type-check-instr Π Γ i₁
    ... | left e = invalid-instr i₁
    ... | right (ok {Γ'} i₁') with type-check-instr Π Γ' i₂
    ...   | left e = invalid-instr i₂
    ...   | right (ok i₂') = right (ok (instr-seq i₁' i₂'))
    type-check-instr Π Γ i = invalid-instr i

    type-check-block : ∀ {n}(Π : PCtx n) → (Γ : Ctx) → (i : UInstr n) → TC (Checked Π Γ i)
    type-check-block Π Γ (jump n l) = check-jump Π Γ n l
    type-check-block Π Γ halt = right (ok block-halt)
    type-check-block Π Γ (seq i₁ i₂) with type-check-instr Π Γ i₁
    ... | left e = invalid-instr i₁
    ... | right (ok {Γ'} i₁') with type-check-block Π Γ' i₂
    ...   | left e = invalid-instr i₂
    ...   | right (ok i₂') = right (ok (block-seq i₁' i₂'))
    type-check-block Π Γ b = invalid-instr b
