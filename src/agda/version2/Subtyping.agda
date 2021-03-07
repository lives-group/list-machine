open import Data.Empty
open import Data.List
open import Data.Product
open import Data.String renaming (_≟_ to _≟s_)


open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_)

open import Type

module Subtyping where

-- subtype definition

data _⊂_ : Ctx → Ctx → Set

data _<:_ : Ty → Ty → Set where
  <:-top  : ∀ {t} → t <: top
  <:-bot  : ∀ {t} → bot <: t
  <:-cont : ∀ {Γ Γ'} → Γ' ⊂ Γ → (cont Γ) <: (cont Γ')
  <:-refl : ∀ {t} → t <: t
  <:-nil  : ∀ {t} → nil <: list t
  <:-list : ∀ {t t'} →
            t <: t'  →
            (list t) <: (list t')
  <:-listcons : ∀ {t t'} →
                t <: t'  →
                (listcons t) <: list t'
  <:-listmixed : ∀ {t t'} →
                 t <: t'  →
                 (listcons t) <: (listcons t')

-- subtype for contexts

data _⊂_ where
  env-sub1 : ∀ {Γ Γ'' Γ' t t'} →
               Γ ≡ t' ∷ Γ''    →
               t' <: t         →
               Γ'' ⊂ Γ'        →
               Γ ⊂ (t ∷ Γ')
  env-sub2 : ∀ {Γ} → Γ ⊂ []

⊂-refl : ∀ {Γ} → Γ ⊂ Γ
⊂-refl {[]} = env-sub2
⊂-refl {x ∷ Γ} = env-sub1 refl <:-refl (⊂-refl {Γ})


⊂-[]-left : ∀ {t Γ} → ¬ ([] ⊂ (t ∷ Γ))
⊂-[]-left (env-sub1 () x₁ p)

⊂-∷-inv : ∀ {t t' Γ Γ'} → (t ∷ Γ) ⊂ (t' ∷ Γ') → (t <: t') × (Γ ⊂ Γ')
⊂-∷-inv (env-sub1 refl x₁ p) = x₁ , p

-- inversion lemmas

list-<:-inv : ∀ {t t'} → (list t) <: (list t') → t <: t'
list-<:-inv <:-refl = <:-refl
list-<:-inv (<:-list p) = p

list-cons-<:-inv : ∀ {t t'} → (listcons t) <: (list t') → t <: t'
list-cons-<:-inv (<:-listcons p) = p

list-mixed-<:-inv : ∀ {t t'} → (listcons t) <: (listcons t') → t <: t'
list-mixed-<:-inv <:-refl = <:-refl
list-mixed-<:-inv (<:-listmixed p) = p

cont-<:-inv : ∀ {Γ Γ'} → (cont Γ) <: (cont Γ') → Γ' ⊂ Γ
cont-<:-inv (<:-cont x) = x
cont-<:-inv <:-refl = ⊂-refl

-- lemmas about top

top-<: : ∀ {t} → top <: t → t ≡ top
top-<: <:-top = refl
top-<: <:-refl = refl

bot-<: : ∀ {t} → t <: bot → t ≡ bot
bot-<: <:-bot = refl
bot-<: <:-refl = refl

-- subtyping tests

_⊂?_ : Decidable {A = Ctx} _⊂_

_<:?_ : Decidable {A = Ty} _<:_
nil <:? nil = yes <:-refl
nil <:? list t' = yes <:-nil
nil <:? listcons t' = no (λ ())
nil <:? top = yes <:-top
nil <:? bot = no (λ ())
nil <:? cont x = no (λ ())
list t <:? nil = no (λ ())
list t <:? list t' = dec (t <:? t')
                         (yes ∘ <:-list)
                         (λ q → no (λ p → q (list-<:-inv p)))
list t <:? listcons t' = no (λ ())
list t <:? top = yes <:-top
list t <:? bot = no (λ ())
list t <:? cont x = no (λ ())
listcons t <:? nil = no (λ ())
listcons t <:? list t' = dec (t <:? t')
                             (yes ∘ <:-listcons)
                             (λ q → no (λ k → q (list-cons-<:-inv k)))
listcons t <:? listcons t' = dec (t <:? t')
                                 (yes ∘ <:-listmixed)
                                 (λ q → no (λ k → q (list-mixed-<:-inv k)))
listcons t <:? top = yes <:-top
listcons t <:? bot = no (λ ())
listcons t <:? cont x = no (λ ())
top <:? nil = no (λ ())
top <:? list t' = no (λ ())
top <:? listcons t' = no (λ ())
top <:? top = yes <:-top
top <:? bot = no (λ ())
top <:? cont x = no (λ ())
bot <:? t' = yes <:-bot
cont ts <:? nil = no (λ ())
cont ts <:? list t' = no (λ ())
cont ts <:? listcons t' = no (λ ())
cont ts <:? top = yes <:-top
cont ts <:? bot = no (λ ())
cont ts <:? cont ts' = dec (ts' ⊂? ts)
                           (yes ∘ <:-cont)
                           (λ q → no (λ k → q (cont-<:-inv k)))


ts ⊂? [] = yes env-sub2
[] ⊂? (t' ∷ ts') = no ⊂-[]-left
(t ∷ ts) ⊂? (t' ∷ ts') with t <:? t' | ts ⊂? ts'
...| yes p | yes q = yes (env-sub1 refl p q)
...| yes p | no  q = no (λ n → q (proj₂ (⊂-∷-inv n)))
...| no  p | _     = no (λ n → (p (proj₁ (⊂-∷-inv n))))

-- properties of subtyping

⊂-trans : ∀ {Γ1 Γ2 Γ3} → Γ1 ⊂ Γ2 → Γ2 ⊂ Γ3 → Γ1 ⊂ Γ3

<:-trans : ∀ {t1 t2 t3} → t1 <: t2 → t2 <: t3 → t1 <: t3
<:-trans {.bot} {nil} {t3} <:-bot q = <:-bot
<:-trans {.nil} {nil} {t3} <:-refl q = q
<:-trans {.bot} {list t2} {t3} <:-bot q = <:-bot
<:-trans {.(list t2)} {list t2} {t3} <:-refl q = q
<:-trans {.nil} {list t2} {.top} <:-nil <:-top = <:-top
<:-trans {.nil} {list t2} {.(list t2)} <:-nil <:-refl = <:-nil
<:-trans {.nil} {list t2} {.(list _)} <:-nil (<:-list q) = <:-nil
<:-trans {.(list _)} {list t2} {.top} (<:-list p) <:-top = <:-top
<:-trans {.(list _)} {list t2} {.(list t2)} (<:-list p) <:-refl = <:-list p
<:-trans {.(list _)} {list t2} {.(list _)} (<:-list p) (<:-list q) = <:-list (<:-trans p q)
<:-trans {.(listcons _)} {list t2} {.top} (<:-listcons p) <:-top = <:-top
<:-trans {.(listcons _)} {list t2} {.(list t2)} (<:-listcons p) <:-refl = <:-listcons p
<:-trans {.(listcons _)} {list t2} {.(list _)} (<:-listcons p) (<:-list q) = <:-listcons (<:-trans p q)
<:-trans {.bot} {listcons t2} {t3} <:-bot q = <:-bot
<:-trans {.(listcons t2)} {listcons t2} {t3} <:-refl q = q
<:-trans {.(listcons _)} {listcons t2} {.top} (<:-listmixed p) <:-top = <:-top
<:-trans {.(listcons _)} {listcons t2} {.(listcons t2)} (<:-listmixed p) <:-refl = <:-listmixed p
<:-trans {.(listcons _)} {listcons t2} {.(list _)} (<:-listmixed p) (<:-listcons q) = <:-listcons (<:-trans p q)
<:-trans {.(listcons _)} {listcons t2} {.(listcons _)} (<:-listmixed p) (<:-listmixed q) = <:-listmixed (<:-trans p q)
<:-trans {t1} {top} {t3} p q rewrite top-<: q = p
<:-trans {t1} {bot} {t3} p q rewrite bot-<: p = q
<:-trans {.bot} {cont x} {t3} <:-bot q = <:-bot
<:-trans {.(cont _)} {cont x} {.top} (<:-cont x₁) <:-top = <:-top
<:-trans {.(cont _)} {cont x} {.(cont _)} (<:-cont x₁) (<:-cont x₂) = <:-cont (⊂-trans x₂ x₁)
<:-trans {.(cont _)} {cont x} {.(cont x)} (<:-cont x₁) <:-refl = <:-cont x₁
<:-trans {.(cont x)} {cont x} {t3} <:-refl q = q


⊂-trans (env-sub1 refl x₁ p) (env-sub1 refl x₃ q) = env-sub1 refl (<:-trans x₁ x₃) (⊂-trans p q)
⊂-trans (env-sub1 refl x₁ p) env-sub2 = env-sub2
⊂-trans env-sub2 env-sub2 = env-sub2
