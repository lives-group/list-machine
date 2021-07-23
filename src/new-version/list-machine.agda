open import Data.Fin
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using  (≡-dec ; ∷-injective)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_ ; any?)
open import Data.List.Relation.Unary.All renaming (All to All-list ; _[_]=_ to list-ref)
open import Data.Maybe
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Nat.Properties renaming (_≟_ to _≟N_)
open import Data.Product
open import Data.String hiding (length)
open import Data.Sum renaming (_⊎_ to Either ; inj₁ to left ; inj₂ to right)
open import Data.Vec renaming ([] to []v ; _∷_ to _∷v_ ; length to vlength ; lookup to vlookup)
open import Data.Vec.Properties hiding (≡-dec ; ∷-injective)
open import Data.Vec.Relation.Unary.All using (All) renaming (lookup to lookupA)

open import Function hiding (_⇔_)

open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_ ; _⇒_ ; _⊢_ ; _∈_)


module list-machine where

  module Type where
    -- types and contexts

    Ctx : Set

    data Ty : Set where
      nil      : Ty
      list     : Ty  → Ty
      listcons : Ty  → Ty
      top      : Ty
      bot      : Ty
      cont     : Ctx → Ty

    Ctx = List Ty

    -- decidable equality for types

    list-≡-inv : ∀ {t t' : Ty} → (list t) ≡ (list t') → t ≡ t'
    list-≡-inv refl = refl

    listcons-≡-inv : ∀ {t t' : Ty} → (listcons t) ≡ (listcons t') → t ≡ t'
    listcons-≡-inv refl = refl

    cont-≡-inv : ∀ {ts ts' : Ctx} →
                   (cont ts) ≡ (cont ts') → ts ≡ ts'
    cont-≡-inv refl = refl

    ×-≡-inv : ∀ {A B : Set}{x x' : A}{y y' : B} →
                (x , y) ≡ (x' , y') → x ≡ x' × y ≡ y'
    ×-≡-inv refl = refl , refl


    dec : ∀ {l l'}{A : Set l}{B : Set l'} →
          Dec A → (A → B) → (¬ A → B) → B
    dec (yes p) f g = f p
    dec (no q) f g = g q


    _≟T_ : Decidable {A = Ty} _≡_
    _≟C_ : Decidable {A = Ctx} _≡_

    nil ≟T nil = yes refl
    nil ≟T list t' = no (λ ())
    nil ≟T listcons t' = no (λ ())
    nil ≟T top = no (λ ())
    nil ≟T bot = no (λ ())
    nil ≟T cont x = no (λ ())
    list t ≟T nil = no (λ ())
    list t ≟T list t' = dec (t ≟T t')
                            (yes ∘ cong list)
                            (λ neq → no (neq ∘ list-≡-inv))
    list t ≟T listcons t' = no (λ ())
    list t ≟T top = no (λ ())
    list t ≟T bot = no (λ ())
    list t ≟T cont x = no (λ ())
    listcons t ≟T nil = no (λ ())
    listcons t ≟T list t' = no (λ ())
    listcons t ≟T listcons t' = dec (t ≟T t')
                                    (yes ∘ cong listcons)
                                    (λ neq → no (neq ∘ listcons-≡-inv))
    listcons t ≟T top = no (λ ())
    listcons t ≟T bot = no (λ ())
    listcons t ≟T cont x = no (λ ())
    top ≟T nil = no (λ ())
    top ≟T list t' = no (λ ())
    top ≟T listcons t' = no (λ ())
    top ≟T top = yes refl
    top ≟T bot = no (λ ())
    top ≟T cont x = no (λ ())
    bot ≟T nil = no (λ ())
    bot ≟T list t' = no (λ ())
    bot ≟T listcons t' = no (λ ())
    bot ≟T top = no (λ ())
    bot ≟T bot = yes refl
    bot ≟T cont x = no (λ ())
    cont x ≟T nil = no (λ ())
    cont x ≟T list t' = no (λ ())
    cont x ≟T listcons t' = no (λ ())
    cont x ≟T top = no (λ ())
    cont x ≟T bot = no (λ ())
    (cont Γ) ≟T (cont Γ') = dec (Γ ≟C Γ')
                                (yes ∘ cong cont)
                                (λ neq → no (neq ∘ cont-≡-inv))


    [] ≟C [] = yes refl
    [] ≟C (y ∷ ys) = no (λ ())
    (x ∷ xs) ≟C [] = no (λ ())
    (t ∷ Γ) ≟C (t' ∷ Γ') with t ≟T t' | Γ ≟C Γ'
    ...| yes eq | yes eq' rewrite eq | eq' = yes refl
    ...| no neq | _ = no (neq ∘ proj₁ ∘ ∷-injective)
    ...| _      | no neq' = no (neq' ∘ proj₂ ∘ ∷-injective)


-----------------------------

  module Subtyping where

    open Type

    data _⊂_ : Ctx → Ctx → Set

    data _<:_ : Ty → Ty → Set where
      <:-top  : ∀ {t} → t <: top
      <:-bot  : ∀ {t} → bot <: t
      <:-cont : ∀ {Γ Γ' : Ctx} →
                   Γ' ⊂ Γ → (cont Γ) <: (cont Γ')
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
      env-sub1 : ∀ {Γ'' : Ctx}{Γ Γ' t t'} →
                 Γ ≡ (t' ∷ Γ'')    →
                 t' <: t         →
                 Γ'' ⊂ Γ'        →
                 Γ ⊂ (t ∷ Γ')
      env-sub2 : ∀ {Γ} → Γ ⊂ []

    ⊂-refl : ∀ {Γ} → Γ ⊂ Γ
    ⊂-refl {[]} = env-sub2
    ⊂-refl {x ∷ Γ} = env-sub1 refl <:-refl (⊂-refl {Γ})


    ⊂-[]-left : ∀ {t Γ} → ¬ ([] ⊂ (t ∷ Γ))
    ⊂-[]-left (env-sub1 () x₁ p)

    ⊂-∷-inv : ∀ {t t' Γ Γ'} →
              (t ∷ Γ) ⊂ (t' ∷ Γ') →
              (t <: t') × (Γ ⊂ Γ')
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

    -- decidability tests

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

    [] ⊂? [] = yes env-sub2
    [] ⊂? (x ∷ Γ') = no ⊂-[]-left 
    (t ∷ Γ) ⊂? [] = yes env-sub2
    (t ∷ Γ) ⊂? (t' ∷ Γ') with t <:? t' | Γ ⊂? Γ'
    ...| yes p | yes q = yes (env-sub1 refl p q)
    ...| no  p | _     = no (p ∘ proj₁ ∘ ⊂-∷-inv)
    ...| _     | no q  = no (q ∘ proj₂ ∘ ⊂-∷-inv)


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

------------------------------------------------

  module LeastSuperType where

    open Type
    open Subtyping


    -- definition of least subtype relation

    data _∩_~_ : Ctx → Ctx → Ctx → Set
    data _⊓_~_ : Ty → Ty → Ty → Set

    data _⊔_~_ : Ty → Ty → Ty → Set
    data _∪_~_ : Ctx → Ctx → Ctx → Set

    data _∩_~_  where
      lub-ctx-1 : ∀ {Γ'} → [] ∩ Γ' ~ []
      lub-ctx-2 : ∀ {Γ}  → Γ ∩ [] ~ []
      lub-ctx-3 : ∀ {t t' t'' Γ Γ' Γ''} →
                  t ⊓ t' ~ t'' →
                  Γ ∩ Γ' ~ Γ'' →
                  (t ∷ Γ) ∩ (t' ∷ Γ') ~ (t'' ∷ Γ'')

    data _⊓_~_ where
      lub-bot-r : ∀ {t} → t ⊓ bot ~ t
      lub-bot-l : ∀ {t} → bot ⊓ t ~ t
      lub-0 : ∀ {t} → t ⊓ t ~ t
      lub-1 : ∀ {t} → (list t) ⊓ nil ~ (list t)
      lub-4 : ∀ {t} → nil ⊓ (list t) ~ (list t)
      lub-2 : ∀ {t t1 t'} →
              (list t) ⊓ (list t1) ~ t' →
              (list t) ⊓ (listcons t1) ~ t'
      lub-2b : ∀ {t t1 t'} →
               (list t) ⊓ (list t1) ~ t' →
               (listcons t) ⊓ (list t1) ~ t'
      lub-3 : ∀ {t t1 t'} →
                t ⊓ t1 ~ t' →
                (list t) ⊓ (list t1) ~ (list t')
      lub-5 : ∀ {t} → (listcons t) ⊓ nil ~ (list t)
      lub-6 : ∀ {t} → nil ⊓ (listcons t) ~ (list t)
      lub-7 : ∀ {t t1 t'} →
                t ⊓ t1 ~ t' →
                (listcons t) ⊓ (listcons t1) ~ (listcons t')
      lub-cont-nil1 : ∀ {Γ} → nil ⊓ (cont Γ) ~ top
      lub-cont-nil2 : ∀ {Γ} → (cont Γ) ⊓ nil ~ top
      lub-cont-list1 : ∀ {t Γ} → (list t) ⊓ (cont Γ) ~ top
      lub-cont-list2 : ∀ {t Γ} → (cont Γ) ⊓ (list t) ~ top
      lub-cont-listcons1 : ∀ {t Γ} → (listcons t) ⊓ (cont Γ) ~ top
      lub-cont-listcons2 : ∀ {t Γ} → (cont Γ) ⊓ (listcons t) ~ top
      lub-cont : ∀ {Γ Γ' Γ''}   →
                   Γ ∪ Γ' ~ Γ'' →
                   (cont Γ) ⊓ (cont Γ') ~ (cont Γ'')
      lub-top1 : ∀ {t} → t ⊓ top ~ top
      lub-top2 : ∀ {t} → top ⊓ t ~ top

    -- greatest subtype relation

    data _∪_~_  where
      glb-ctx-1 : ∀ {Γ'} → [] ∪ Γ' ~ Γ'
      glb-ctx-2 : ∀ {Γ}  → Γ ∪ [] ~ Γ
      glb-ctx-3 : ∀ {t t' t'' Γ Γ' Γ''} →
                    t ⊔ t' ~ t'' →
                    Γ ∪ Γ' ~ Γ'' →
                    (t ∷ Γ) ∪ (t' ∷ Γ') ~ (t'' ∷ Γ'')


    data _⊔_~_ where
      glb-refl : ∀ {t} → t ⊔ t ~ t
      glb-top-l : ∀ {t} → top ⊔ t ~ t
      glb-top-r : ∀ {t} → t ⊔ top ~ t
      glb-nil : nil ⊔ nil ~ nil
      glb-listnil-l : ∀ {t} → nil ⊔ (list t) ~ nil
      glb-listnil-r : ∀ {t} → (list t) ⊔ nil ~ nil
      glb-listcons-nil : ∀ {t} → nil ⊔ (listcons t) ~ bot
      glb-listcons-nil1 : ∀ {t} → (listcons t) ⊔ nil ~ bot
      glb-list : ∀ {t1 t2 t3} →
                 t1 ⊔ t2 ~ t3 →
                 (list t1) ⊔ (list t2) ~ (list t3)
      glb-listcons1 : ∀ {t1 t2 t3} →
                      t1 ⊔ t2 ~ t3 →
                      (list t1) ⊔ (listcons t2) ~ (listcons t3)
      glb-listcons2 : ∀ {t1 t2 t3} →
                      t1 ⊔ t2 ~ t3 →
                      (listcons t1) ⊔ (list t2) ~ (listcons t3)
      glb-listcons3 : ∀ {t1 t2 t3} →
                      t1 ⊔ t2 ~ t3 →
                      (listcons t1) ⊔ (listcons t2) ~ (listcons t3)
      glb-cont-nil : ∀ {Γ} → nil ⊔ (cont Γ) ~ bot
      glb-cont-nil1 : ∀ {Γ} → (cont Γ) ⊔ nil ~ bot
      glb-list-cont : ∀ {t Γ} → (list t) ⊔ (cont Γ) ~ bot
      glb-cont-list : ∀ {t Γ} → (cont Γ) ⊔ (list t) ~ bot
      glb-listcons-cont : ∀ {t Γ} → (listcons t) ⊔ (cont Γ) ~ bot
      glb-cont-listcons : ∀ {t Γ} → (cont Γ) ⊔ (listcons t) ~ bot
      glb-cont : ∀ {Γ Γ' Γ''}   →
                   Γ ∩ Γ' ~ Γ'' →
                   (cont Γ) ⊔ (cont Γ') ~ (cont Γ'')
      glb-top1 : ∀ {t} → t ⊔ bot ~ bot
      glb-top2 : ∀ {t} → bot ⊔ t ~ bot


    -- calculating lub and glb

    lub : ∀ t1 t2 → ∃ (λ t3 → t1 ⊓ t2 ~ t3)


    lubCtx : ∀ Γ Γ' → ∃ (λ Γ'' → Γ ∩ Γ' ~ Γ'')
    lubCtx [] Γ' = [] , lub-ctx-1
    lubCtx (t ∷ Γ) [] = [] , lub-ctx-2
    lubCtx (t ∷ Γ) (t' ∷ Γ') with lub t t' | lubCtx Γ Γ'
    ...| t'' , p | Γ'' , q = t'' ∷ Γ'' , lub-ctx-3 p q

    glb : ∀ t1 t2 → ∃ (λ t3 → t1 ⊔ t2 ~ t3)


    glbCtx : ∀ Γ Γ' → ∃ (λ Γ'' → Γ ∪ Γ' ~ Γ'')


    lub nil nil = nil , lub-0
    lub nil (list t2) = list t2 , lub-4
    lub nil (listcons t2) = list t2 , lub-6
    lub nil top = top , lub-top1
    lub nil bot = nil , lub-bot-r
    lub nil (cont x) = top , lub-cont-nil1
    lub (list t1) nil = list t1 , lub-1
    lub (list t1) (list t2) with lub t1 t2
    ...| t3 , p = list t3 , lub-3 p
    lub (list t1) (listcons t2) with lub t1 t2
    ...| t3 , p = list t3 , lub-2 (lub-3 p)
    lub (list t1) top = top , lub-top1
    lub (list t1) bot = list t1 , lub-bot-r
    lub (list t1) (cont x) = top , lub-cont-list1
    lub (listcons t1) nil = list t1 , lub-5
    lub (listcons t1) (list t2) with lub t1 t2
    ...| t3 , p = list t3 , lub-2b (lub-3 p)
    lub (listcons t1) (listcons t2) with lub t1 t2
    ...| t3 , p = listcons t3 , lub-7 p
    lub (listcons t1) top = top , lub-top1
    lub (listcons t1) bot = listcons t1 , lub-bot-r
    lub (listcons t1) (cont x) = top , lub-cont-listcons1
    lub top t2 = top , lub-top2
    lub bot t2 = t2 , lub-bot-l
    lub (cont x) nil = top , lub-cont-nil2
    lub (cont x) (list t2) = top , lub-cont-list2
    lub (cont x) (listcons t2) = top , lub-cont-listcons2
    lub (cont x) top = top , lub-top1
    lub (cont x) bot = cont x , lub-bot-r
    lub (cont x) (cont x₁) with glbCtx x x₁
    ...| k , k'  = cont k , lub-cont k'


    glb nil nil = nil , glb-refl
    glb nil (list t') = nil , glb-listnil-l
    glb nil (listcons t') = bot , glb-listcons-nil
    glb nil top = nil , glb-top-r
    glb nil bot = bot , glb-top1
    glb nil (cont Γ) = bot , glb-cont-nil
    glb (list t) nil = nil , glb-listnil-r
    glb (list t) (list t') with glb t t'
    ...| k , k1 = list k , glb-list k1
    glb (list t) (listcons t') with glb t t'
    ...| k , k1 = listcons k , glb-listcons1 k1
    glb (list t) top = list t , glb-top-r
    glb (list t) bot = bot , glb-top1
    glb (list t) (cont x) = bot , glb-list-cont
    glb (listcons t) nil = bot , glb-listcons-nil1
    glb (listcons t) (list t') with glb t t'
    ...| k , k1 = listcons k , glb-listcons2 k1
    glb (listcons t) (listcons t') with glb t t'
    ...| k , k1 = listcons k , glb-listcons3 k1
    glb (listcons t) top = listcons t , glb-top-r
    glb (listcons t) bot = bot , glb-top1
    glb (listcons t) (cont Γ) = bot , glb-listcons-cont
    glb top t' = t' , glb-top-l
    glb bot t' = bot , glb-top2
    glb (cont x) nil = bot , glb-cont-nil1
    glb (cont x) (list t') = bot , glb-cont-list
    glb (cont x) (listcons t') = bot , glb-cont-listcons
    glb (cont x) top = cont x , glb-top-r
    glb (cont x) bot = bot , glb-top1
    glb (cont Γ) (cont Γ') with lubCtx Γ Γ'
    ...| Γ'' , p = cont Γ'' , glb-cont p


    glbCtx [] [] = [] , glb-ctx-1
    glbCtx [] (t' ∷ Γ') = t' ∷ Γ' , glb-ctx-1
    glbCtx (t ∷ Γ) [] = t ∷ Γ , glb-ctx-2
    glbCtx (t ∷ Γ) (t' ∷ Γ') with glb t t' | glbCtx Γ Γ'
    ...| t3 , p3 | Γ'' , p4 = t3 ∷ Γ'' , glb-ctx-3 p3 p4


    -- relating subtyping and lub , glb

    lub-subtype : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → (t1 <: t3) × (t2 <: t3)


    lubCtx-subtype : ∀ {Γ Γ' Γ''} → Γ ∩ Γ' ~ Γ'' → (Γ ⊂ Γ'') × (Γ' ⊂ Γ'')

    glb-supertype : ∀ {t1 t2 t3} → t1 ⊔ t2 ~ t3 → (t3 <: t1) × (t3 <: t2)
    glbCtx-supertype : ∀ {Γ Γ' Γ''} → Γ ∪ Γ' ~ Γ'' → (Γ'' ⊂ Γ) × (Γ'' ⊂ Γ')

    lub-subtype {nil} lub-bot-r = <:-refl , <:-bot
    lub-subtype {nil} lub-0 = <:-refl , <:-refl
    lub-subtype {nil} lub-4 = <:-nil , <:-refl
    lub-subtype {nil} lub-6 = <:-nil , <:-listcons <:-refl
    lub-subtype {nil} lub-cont-nil1 = <:-top , <:-top
    lub-subtype {nil} lub-top1 = <:-top , <:-top
    lub-subtype {list t1} lub-bot-r = <:-refl , <:-bot
    lub-subtype {list t1} lub-0 = <:-refl , <:-refl
    lub-subtype {list t1} lub-1 = <:-refl , <:-nil
    lub-subtype {list t1} (lub-2 lub-0) = <:-refl , proj₁ (lub-subtype lub-5)
    lub-subtype {list t1} (lub-2 (lub-3 p)) with lub-subtype p
    ...| k1 , k2 = <:-list k1 , <:-listcons k2
    lub-subtype {list t1} (lub-3 p) with lub-subtype p
    ...| k1 , k2 = <:-list k1 , <:-list k2
    lub-subtype {list t1} lub-cont-list1 = <:-top , <:-top
    lub-subtype {list t1} lub-top1 = <:-top , <:-top
    lub-subtype {listcons t1} lub-bot-r = <:-refl , <:-bot
    lub-subtype {listcons t1} lub-0 = <:-refl , <:-refl
    lub-subtype {listcons t1} (lub-2b lub-0) = <:-listcons <:-refl , <:-refl
    lub-subtype {listcons t1} (lub-2b (lub-3 p)) with lub-subtype p
    ...| k1 , k2 = <:-listcons k1 , <:-list k2
    lub-subtype {listcons t1} lub-5 = <:-listcons <:-refl , <:-nil
    lub-subtype {listcons t1} (lub-7 p) with lub-subtype p
    ...| k1 , k2 = <:-listmixed k1 , <:-listmixed k2
    lub-subtype {listcons t1} lub-cont-listcons1 = <:-top , <:-top
    lub-subtype {listcons t1} lub-top1 = <:-top , <:-top
    lub-subtype {top} lub-bot-r = <:-top , <:-top
    lub-subtype {top} lub-0 = <:-top , <:-top
    lub-subtype {top} lub-top1 = <:-top , <:-top
    lub-subtype {top} lub-top2 = <:-top , <:-top
    lub-subtype {bot} lub-bot-r = <:-bot , <:-bot
    lub-subtype {bot} lub-bot-l = <:-bot , <:-refl
    lub-subtype {bot} lub-0 = <:-bot , <:-bot
    lub-subtype {bot} lub-top1 = <:-top , <:-top
    lub-subtype {cont Γ} lub-bot-r = <:-refl , <:-bot
    lub-subtype {cont Γ} lub-0 = <:-refl , <:-refl
    lub-subtype {cont Γ} lub-cont-nil2 = <:-top , <:-top
    lub-subtype {cont Γ} lub-cont-list2 = <:-top , <:-top
    lub-subtype {cont Γ} lub-cont-listcons2 = <:-top , <:-top
    lub-subtype {cont Γ} (lub-cont p) with glbCtx-supertype p
    ...| k1 , k2 = (<:-cont k1) , <:-cont k2
    lub-subtype {cont Γ} lub-top1 = <:-top , <:-top

    lubCtx-subtype lub-ctx-1 = env-sub2 , env-sub2
    lubCtx-subtype lub-ctx-2 = env-sub2 , env-sub2
    lubCtx-subtype (lub-ctx-3 x p) with lub-subtype x | lubCtx-subtype p
    ...| p1 , p1' | q1 , q1' = env-sub1 refl p1 q1 , env-sub1 refl p1' q1'

    glb-supertype {t1} glb-refl = <:-refl , <:-refl
    glb-supertype {.top} glb-top-l = <:-top , <:-refl
    glb-supertype {t1} glb-top-r = <:-refl , <:-top
    glb-supertype {.nil} glb-nil = <:-refl , <:-refl
    glb-supertype {.nil} glb-listnil-l = <:-refl , <:-nil
    glb-supertype {.(list _)} glb-listnil-r = <:-nil , <:-refl
    glb-supertype {.nil} glb-listcons-nil = <:-bot , <:-bot
    glb-supertype {.(listcons _)} glb-listcons-nil1 = <:-bot , <:-bot
    glb-supertype {.(list _)} (glb-list p) with glb-supertype p
    ...| k1 , k2 = <:-list k1 , <:-list k2
    glb-supertype {.(list _)} (glb-listcons1 p) with glb-supertype p
    ...| k1 , k2 = <:-listcons k1 , <:-listmixed k2
    glb-supertype {.(listcons _)} (glb-listcons2 p) with glb-supertype p
    ...| k1 , k2 = <:-listmixed k1 , <:-listcons k2
    glb-supertype {.(listcons _)} (glb-listcons3 p) with glb-supertype p
    ...| k1 , k2 = <:-listmixed k1 , <:-listmixed k2
    glb-supertype {.nil} glb-cont-nil = <:-bot , <:-bot
    glb-supertype {.(cont _)} glb-cont-nil1 = <:-bot , <:-bot
    glb-supertype {.(list _)} glb-list-cont = <:-bot , <:-bot
    glb-supertype {.(cont _)} glb-cont-list = <:-bot , <:-bot
    glb-supertype {.(listcons _)} glb-listcons-cont = <:-bot , <:-bot
    glb-supertype {.(cont _)} glb-cont-listcons = <:-bot , <:-bot
    glb-supertype {.(cont _)} (glb-cont x) with lubCtx-subtype x
    ...| k1 , k2 = <:-cont k1 , <:-cont k2
    glb-supertype {t1} glb-top1 = <:-bot , <:-bot
    glb-supertype {.bot} glb-top2 = <:-bot , <:-bot

    glbCtx-supertype glb-ctx-1 = env-sub2 , ⊂-refl
    glbCtx-supertype glb-ctx-2 = ⊂-refl , env-sub2
    glbCtx-supertype (glb-ctx-3 x p) with glb-supertype x | glbCtx-supertype p
    ...| p1 , p1' | q1 , q1' = env-sub1 refl p1 q1 , env-sub1 refl p1' q1'


    -- projection lemmas

    lub-subtype-left : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → (t1 <: t3)
    lub-subtype-left = proj₁ ∘ lub-subtype

    lub-subtype-right : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → (t2 <: t3)
    lub-subtype-right = proj₂ ∘ lub-subtype


    lubCtx-subtype-left : ∀ {Γ Γ' Γ''} → Γ ∩ Γ' ~ Γ'' → (Γ ⊂ Γ'')
    lubCtx-subtype-left = proj₁ ∘ lubCtx-subtype

    lubCtx-subtype-right : ∀ {Γ Γ' Γ''} → Γ ∩ Γ' ~ Γ'' → (Γ' ⊂ Γ'')
    lubCtx-subtype-right = proj₂ ∘ lubCtx-subtype

    glb-supertype-left : ∀ {t1 t2 t3} → t1 ⊔ t2 ~ t3 → (t3 <: t1)
    glb-supertype-left = proj₁ ∘ glb-supertype

    glb-supertype-right : ∀ {t1 t2 t3} → t1 ⊔ t2 ~ t3 → (t3 <: t2)
    glb-supertype-right = proj₂ ∘ glb-supertype

    glbCtx-supertype-left : ∀ {Γ Γ' Γ''} → Γ ∪ Γ' ~ Γ'' → (Γ'' ⊂ Γ)
    glbCtx-supertype-left = proj₁ ∘ glbCtx-supertype

    glbCtx-supertype-right : ∀ {Γ Γ' Γ''} → Γ ∪ Γ' ~ Γ'' → (Γ'' ⊂ Γ')
    glbCtx-supertype-right = proj₂ ∘ glbCtx-supertype

    -- commutativity lemmas

    lub-comm : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → t2 ⊓ t1 ~ t3
    glb-comm : ∀ {t1 t2 t3} → t1 ⊔ t2 ~ t3 → t2 ⊔ t1 ~ t3


    lubCtx-comm : ∀ {Γ Γ' Γ''} → Γ ∩ Γ' ~ Γ'' → Γ' ∩ Γ ~ Γ''
    glbCtx-comm : ∀ {Γ Γ' Γ''} → Γ ∪ Γ' ~ Γ'' → Γ' ∪ Γ ~ Γ''

    lub-comm lub-bot-r = lub-bot-l
    lub-comm lub-bot-l = lub-bot-r
    lub-comm lub-0 = lub-0
    lub-comm lub-1 = lub-4
    lub-comm lub-4 = lub-1
    lub-comm (lub-2 p) = lub-2b (lub-comm p)
    lub-comm (lub-2b p) = lub-2 (lub-comm p)
    lub-comm (lub-3 p) = lub-3 (lub-comm p)
    lub-comm lub-5 = lub-6
    lub-comm lub-6 = lub-5
    lub-comm (lub-7 p) = lub-7 (lub-comm p)
    lub-comm lub-cont-nil1 = lub-cont-nil2
    lub-comm lub-cont-nil2 = lub-cont-nil1
    lub-comm lub-cont-list1 = lub-cont-list2
    lub-comm lub-cont-list2 = lub-cont-list1
    lub-comm lub-cont-listcons1 = lub-cont-listcons2
    lub-comm lub-cont-listcons2 = lub-cont-listcons1
    lub-comm (lub-cont x) = lub-cont (glbCtx-comm x)
    lub-comm lub-top1 = lub-top2
    lub-comm lub-top2 = lub-top1

    glb-comm glb-refl = glb-refl
    glb-comm glb-top-l = glb-top-r
    glb-comm glb-top-r = glb-top-l
    glb-comm glb-nil = glb-refl
    glb-comm glb-listnil-l = glb-listnil-r
    glb-comm glb-listnil-r = glb-listnil-l
    glb-comm glb-listcons-nil = glb-listcons-nil1
    glb-comm glb-listcons-nil1 = glb-listcons-nil
    glb-comm (glb-list p) = glb-list (glb-comm p)
    glb-comm (glb-listcons1 p) = glb-listcons2 (glb-comm p)
    glb-comm (glb-listcons2 p) = glb-listcons1 (glb-comm p)
    glb-comm (glb-listcons3 p) = glb-listcons3 (glb-comm p)
    glb-comm glb-cont-nil = glb-cont-nil1
    glb-comm glb-cont-nil1 = glb-cont-nil
    glb-comm glb-list-cont = glb-cont-list
    glb-comm glb-cont-list = glb-list-cont
    glb-comm glb-listcons-cont = glb-cont-listcons
    glb-comm glb-cont-listcons = glb-listcons-cont
    glb-comm (glb-cont x) = glb-cont (lubCtx-comm x)
    glb-comm glb-top1 = glb-top2
    glb-comm glb-top2 = glb-top1


    lubCtx-comm lub-ctx-1 = lub-ctx-2
    lubCtx-comm lub-ctx-2 = lub-ctx-1
    lubCtx-comm (lub-ctx-3 x p) with lub-comm x | lubCtx-comm p
    ...| q | q' = lub-ctx-3 q q'

    glbCtx-comm glb-ctx-1 = glb-ctx-2
    glbCtx-comm glb-ctx-2 = glb-ctx-1
    glbCtx-comm (glb-ctx-3 x p) = glb-ctx-3 (glb-comm x) (glbCtx-comm p)


    -- correctness lemmas

    lub-least : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⊓ τ₂ ~ τ₃ → τ₁ <: τ₄ → τ₂ <: τ₄ → τ₃ <: τ₄
    glb-greatest : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⊔ τ₂ ~ τ₃ → τ₄ <: τ₁ → τ₄ <: τ₂ → τ₄ <: τ₃


    glbCtx-greatest : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → Γ₁ ∪ Γ₂ ~ Γ₃ → Γ₄ ⊂ Γ₁  → Γ₄ ⊂ Γ₂ → Γ₄ ⊂ Γ₃
    lubCtx-least : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → Γ₁ ∩ Γ₂ ~ Γ₃ → Γ₁ ⊂ Γ₄  → Γ₂ ⊂ Γ₄ → Γ₃ ⊂ Γ₄

    lub-least lub-bot-r p1 p2 = p1
    lub-least lub-bot-l p1 p2 = p2
    lub-least lub-0 p1 p2 = p2
    lub-least lub-1 p1 p2 = p1
    lub-least lub-4 p1 p2 = p2
    lub-least (lub-2 lub-0) p1 p2 = p1
    lub-least (lub-2 (lub-3 p)) <:-top p2 = <:-top
    lub-least (lub-2 (lub-3 p)) <:-refl (<:-listcons p2) = <:-list (lub-least p <:-refl p2)
    lub-least (lub-2 (lub-3 p)) (<:-list p1) (<:-listcons p2) = <:-list (lub-least p p1 p2)
    lub-least (lub-2b p) <:-top p2 = <:-top
    lub-least (lub-2b p) (<:-listcons p1) <:-refl = lub-least p (<:-list p1) <:-refl
    lub-least (lub-2b p) (<:-listcons p1) (<:-list p2) = lub-least p (<:-list p1) (<:-list p2)
    lub-least (lub-3 p) <:-top p2 = <:-top
    lub-least (lub-3 p) <:-refl <:-refl = <:-list (lub-least p <:-refl <:-refl)
    lub-least (lub-3 p) <:-refl (<:-list p2) = <:-list (lub-least p <:-refl p2)
    lub-least (lub-3 p) (<:-list p1) <:-refl = <:-list (lub-least p p1 <:-refl)
    lub-least (lub-3 p) (<:-list p1) (<:-list p2) = <:-list (lub-least p p1 p2)
    lub-least lub-5 <:-top p2 = <:-top
    lub-least lub-5 (<:-listcons p1) <:-nil = <:-list p1
    lub-least lub-6 <:-top p2 = <:-top
    lub-least lub-6 <:-nil (<:-listcons p2) = <:-list p2
    lub-least (lub-7 p) <:-top p2 = <:-top
    lub-least (lub-7 p) <:-refl <:-refl = <:-listmixed (lub-least p <:-refl <:-refl)
    lub-least (lub-7 p) <:-refl (<:-listmixed p2) = <:-listmixed (lub-least p <:-refl p2)
    lub-least (lub-7 p) (<:-listcons p1) (<:-listcons p2) = <:-listcons (lub-least p p1 p2)
    lub-least (lub-7 p) (<:-listmixed p1) <:-refl = <:-listmixed (lub-least p p1 <:-refl)
    lub-least (lub-7 p) (<:-listmixed p1) (<:-listmixed p2) = <:-listmixed (lub-least p p1 p2)
    lub-least lub-cont-nil1 <:-top p2 = <:-top
    lub-least lub-cont-nil2 <:-top p2 = <:-top
    lub-least lub-cont-list1 <:-top p2 = <:-top
    lub-least lub-cont-list2 <:-top <:-top = <:-top
    lub-least lub-cont-listcons1 <:-top <:-top = <:-top
    lub-least lub-cont-listcons2 <:-top p2 = <:-top
    lub-least (lub-cont x) <:-top p2 = <:-top
    lub-least (lub-cont x) (<:-cont x₁) (<:-cont x₂) = <:-cont (glbCtx-greatest x x₁ x₂)
    lub-least (lub-cont x) (<:-cont x₁) <:-refl = <:-cont (glbCtx-greatest x x₁ ⊂-refl)
    lub-least (lub-cont x) <:-refl (<:-cont x₁) = <:-cont (glbCtx-greatest x ⊂-refl x₁)
    lub-least (lub-cont x) <:-refl <:-refl = <:-cont (glbCtx-greatest x ⊂-refl ⊂-refl)
    lub-least lub-top1 <:-top p2 = p2
    lub-least lub-top1 <:-bot p2 = p2
    lub-least lub-top1 <:-refl p2 = p2
    lub-least lub-top2 <:-top p2 = <:-top
    lub-least lub-top2 <:-refl p2 = <:-top

    glb-greatest glb-refl p1 p2 = p2
    glb-greatest glb-top-l p1 p2 = p2
    glb-greatest glb-top-r p1 p2 = p1
    glb-greatest glb-nil p1 p2 = p2
    glb-greatest glb-listnil-l p1 p2 = p1
    glb-greatest glb-listnil-r p1 p2 = p2
    glb-greatest glb-listcons-nil <:-bot p2 = <:-bot
    glb-greatest glb-listcons-nil1 <:-bot p2 = <:-bot
    glb-greatest (glb-list p) <:-bot p2 = <:-bot
    glb-greatest (glb-list p) <:-refl <:-refl = <:-list (glb-greatest p <:-refl <:-refl)
    glb-greatest (glb-list p) <:-refl (<:-list p2) = <:-list (glb-greatest p <:-refl p2)
    glb-greatest (glb-list p) <:-nil p2 = <:-nil
    glb-greatest (glb-list p) (<:-list p1) <:-refl = <:-list (glb-greatest p p1 <:-refl)
    glb-greatest (glb-list p) (<:-list p1) (<:-list p2) = <:-list (glb-greatest p p1 p2)
    glb-greatest (glb-list p) (<:-listcons p1) (<:-listcons p2) = <:-listcons (glb-greatest p p1 p2)
    glb-greatest (glb-listcons1 p) <:-bot p2 = <:-bot
    glb-greatest (glb-listcons1 p) (<:-listcons p1) <:-refl = <:-listmixed (glb-greatest p p1 <:-refl)
    glb-greatest (glb-listcons1 p) (<:-listcons p1) (<:-listmixed p2) = <:-listmixed (glb-greatest p p1 p2)
    glb-greatest (glb-listcons2 p) <:-bot p2 = <:-bot
    glb-greatest (glb-listcons2 p) <:-refl (<:-listcons p2) = <:-listmixed (glb-greatest p <:-refl p2)
    glb-greatest (glb-listcons2 p) (<:-listmixed p1) (<:-listcons p2) = <:-listmixed (glb-greatest p p1 p2)
    glb-greatest (glb-listcons3 p) <:-bot p2 = <:-bot
    glb-greatest (glb-listcons3 p) <:-refl <:-refl = <:-listmixed (glb-greatest p <:-refl <:-refl)
    glb-greatest (glb-listcons3 p) <:-refl (<:-listmixed p2) = <:-listmixed (glb-greatest p <:-refl p2)
    glb-greatest (glb-listcons3 p) (<:-listmixed p1) <:-refl = <:-listmixed (glb-greatest p p1 <:-refl)
    glb-greatest (glb-listcons3 p) (<:-listmixed p1) (<:-listmixed p2) = <:-listmixed (glb-greatest p p1 p2)
    glb-greatest glb-cont-nil <:-bot <:-bot = <:-bot
    glb-greatest glb-cont-nil1 <:-bot <:-bot = <:-bot
    glb-greatest glb-list-cont <:-bot <:-bot = <:-bot
    glb-greatest glb-cont-list <:-bot <:-bot = <:-bot
    glb-greatest glb-listcons-cont <:-bot <:-bot = <:-bot
    glb-greatest glb-cont-listcons <:-bot <:-bot = <:-bot
    glb-greatest (glb-cont x) <:-bot p2 = <:-bot
    glb-greatest (glb-cont x) (<:-cont x₁) (<:-cont x₂) = <:-cont (lubCtx-least x x₁ x₂)
    glb-greatest (glb-cont x) (<:-cont x₁) <:-refl = <:-cont (lubCtx-least x x₁ ⊂-refl)
    glb-greatest (glb-cont x) <:-refl (<:-cont x₁) = <:-cont (lubCtx-least x ⊂-refl x₁)
    glb-greatest (glb-cont x) <:-refl <:-refl = <:-cont (lubCtx-least x ⊂-refl ⊂-refl)
    glb-greatest glb-top1 p1 p2 = p2
    glb-greatest glb-top2 p1 p2 = p1


    glbCtx-greatest glb-ctx-1 p1 p2 = p2
    glbCtx-greatest glb-ctx-2 p1 p2 = p1
    glbCtx-greatest (glb-ctx-3 x p) (env-sub1 refl x₂ p1) (env-sub1 refl x₃ p2)
      = env-sub1 refl (glb-greatest x x₂ x₃) (glbCtx-greatest p p1 p2)

    lubCtx-least lub-ctx-1 p1 p2 = p1
    lubCtx-least lub-ctx-2 p1 p2 = p2
    lubCtx-least (lub-ctx-3 x p) (env-sub1 refl x₂ p1) (env-sub1 refl x₄ p2)
      = env-sub1 refl (lub-least x x₂ x₄) (lubCtx-least p p1 p2)
    lubCtx-least (lub-ctx-3 x p) env-sub2 p2 = env-sub2

------ syntax

  module Instr where

    open Type
    open Subtyping
    open LeastSuperType


    Label : ℕ → Set
    Label n = Fin n

    -- program typing

    PCtx : ℕ → Set
    PCtx n = Vec Ctx n

    -- intrinsically typed instructions

    infix 0 _⊢_⇒_

    data _⊢_⇒_ {n}(Π : PCtx n)(Γ : Ctx) : Ctx → Set where
      instr-seq : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ' → Π ⊢ Γ' ⇒ Γ'' → Π ⊢ Γ ⇒ Γ''
      instr-branch-list : ∀ {τ l Γ'} → (idx : list τ ∈ Γ) → Π [ l ]= Γ' → (idx ∷= nil) ⊂ Γ' → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
      instr-branch-listcons : ∀ {τ l Γ₁} → (idx : listcons τ ∈ Γ) → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
      instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
      instr-fetch-0-new     : ∀ {τ}{v' : ℕ} → listcons τ ∈ Γ → Π ⊢ Γ ⇒ τ ∷ Γ
      instr-fetch-0-upd     : ∀ {τ τ'} → listcons τ ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= τ)
      instr-fetch-1-new     : ∀ {τ}{v' : ℕ} → listcons τ ∈ Γ → Π ⊢ Γ ⇒ (list τ ∷ Γ)
      instr-fetch-1-upd     : ∀ {τ τ'} → listcons τ ∈ Γ → (idx : τ' ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= list τ)
      instr-cons-new        : ∀ {τ τ₀ τ₁}{v' : ℕ} → τ₀ ∈ Γ → τ₁ ∈ Γ → (list τ₀ ⊓ τ₁ ~ list τ) → Π ⊢ Γ ⇒ listcons τ ∷ Γ
      instr-cons-upd        : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ →  τ₁ ∈ Γ → (idx :  τ₂ ∈ Γ) → list τ₀ ⊓ τ₁ ~ list τ → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
      instr-getlabel-0      : ∀ {τ}{l : Label n} → (idx : τ ∈ Γ) → Π ⊢ Γ ⇒ (idx ∷= nil)
      instr-getlabel        : ∀ {l τ Γ₁} → (idx : τ ∈ Γ) → Π [ l ]= Γ₁ → Π ⊢ Γ ⇒ (idx ∷= cont Γ₁)

    -- programs

    data Block {n}(Π : PCtx n) (Γ : Ctx) : Ctx →  Set where
      block-halt            : Block Π Γ Γ
      block-seq             : ∀ {Γ′ Γ''} → Π ⊢ Γ ⇒ Γ′ → Block Π Γ′ Γ'' → Block Π Γ Γ''
      block-jump            : ∀ {Γ₁ l}{idx : Π [ l ]= Γ₁} → cont Γ₁ ∈ Γ → Γ ⊂ Γ₁ → Block Π Γ Γ₁

    Program : ∀ {n} → PCtx n → Set
    Program Π = ∀ {Γ'} → All (λ Γ → Block Π Γ Γ') Π

  module UInstr where
    open Type
    open Instr
    open Subtyping

    -- list indexing view

    index : ∀ {A : Set}{t : A}{Γ : List A} → t ∈ Γ → ℕ
    index (here px) = zero
    index (there p) = suc (index p)


    data Lookup {A : Set}(xs : List A) : ℕ → Set where
      inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
      outside : ∀ {n} → Lookup xs n

    lookup-var : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
    lookup-var [] n = outside
    lookup-var (x ∷ xs) zero = inside x (here refl)
    lookup-var (x ∷ xs) (suc n) with lookup-var xs n
    lookup-var (x ∷ xs) (suc .(index p)) | inside y p = inside y (there p)
    lookup-var (x ∷ xs) (suc _) | outside = outside

    data UInstr (n : ℕ) : Set where
      jump          : (x : ℕ) → Label n → UInstr n
      branch-if-nil : (v : ℕ) → Label n → UInstr n
      fetch-field-0 : (v : ℕ) → (v′ : ℕ) → UInstr n
      fetch-field-1 : (v : ℕ) → (v′ : ℕ) → UInstr n
      get-label     : (v : ℕ) → Label n → UInstr n
      cons          : (v₀ : ℕ) → (v₁ : ℕ) → (v′ : ℕ) → UInstr n
      halt          : UInstr n
      seq           : UInstr n → UInstr n → UInstr n

    forget-types-instr : ∀ {n}{Π : PCtx n}{Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr n
    forget-types-instr (instr-seq p p₁) = seq (forget-types-instr p) (forget-types-instr p₁)
    forget-types-instr (instr-branch-list {l = l} idx x x₁) = branch-if-nil (index idx) l
    forget-types-instr (instr-branch-listcons {l = l} idx x x₁) = branch-if-nil (index idx) l
    forget-types-instr (instr-branch-nil {l = l} x x₁ x₂) = branch-if-nil (index x) l
    forget-types-instr (instr-fetch-0-new {v' = v'} x) = fetch-field-0 (index x) v'
    forget-types-instr (instr-fetch-0-upd x idx) = fetch-field-0 (index x) (index idx)
    forget-types-instr (instr-fetch-1-new {v' = v'} x) = fetch-field-1 (index x) v'
    forget-types-instr (instr-fetch-1-upd x idx) = fetch-field-1 (index x) (index idx)
    forget-types-instr (instr-cons-new {v' = v'} x x₁ x₂) = cons (index x) (index x₁) v'
    forget-types-instr (instr-cons-upd x x₁ idx x₂) = cons (index x) (index x₁) (index idx)
    forget-types-instr (instr-getlabel-0 {l = l} idx) = get-label (index idx) l
    forget-types-instr (instr-getlabel {l = l} idx x) = get-label (index idx) l

    forget-types : ∀ {n}{Π : PCtx n}{Γ Γ'} → Block Π Γ Γ' → UInstr n
    forget-types block-halt = halt
    forget-types (block-seq i b) = seq (forget-types-instr i) (forget-types b)
    forget-types (block-jump {l = l} k p) = jump (index k) l


----------------------- type checker


  module TypeChecker where

    open Type
    open Subtyping
    open Instr
    open UInstr
    open LeastSuperType

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


  --- interpreter

  module Intepreter where

    open Type
    open Instr
    open UInstr
    open Subtyping
    open LeastSuperType

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

    Env-permutation : ∀ {Γ Γ'} → Γ ↭ Γ' → Env Γ → Env Γ'
    Env-permutation refl env = env
    Env-permutation (prep x Γ⇔Γ') (v ∷ env) = v ∷ Env-permutation Γ⇔Γ' env
    Env-permutation (_↭_.swap x y Γ⇔Γ') (vx ∷ vy ∷ env) = vy ∷ vx ∷ Env-permutation Γ⇔Γ' env
    Env-permutation (_↭_.trans Γ⇔Γ' Γ⇔Γ'') env = Env-permutation Γ⇔Γ'' (Env-permutation Γ⇔Γ' env)

    -- subsumption

    ⊂-Env : ∀ {Γ Γ'} → Γ ⊂ Γ' → Env Γ → Env Γ'

    <:-val : ∀ {t t' : Ty} → t <: t' → Val t → Val t'
    <:-val <:-top v = top v
    <:-val (<:-cont p) (cont env) = cont (⊂-Env {!!} env)
    <:-val <:-refl v = v
    <:-val <:-nil v = []v
    <:-val (<:-list p) []v = []v
    <:-val (<:-list p) (v ∷v vs) = <:-val p v ∷v <:-val (<:-list p) vs
    <:-val (<:-listcons p) (v ∷ vs) = <:-val p v ∷v <:-val (<:-list p) vs
    <:-val (<:-listmixed p) (v ∷ vs) = <:-val p v ∷ <:-val (<:-list p) vs


    ⊂-Env (env-sub1 refl x₁ p) (v ∷ env) = <:-val x₁ v ∷ ⊂-Env p env
    ⊂-Env env-sub2 env = []


{-

    data _⊂_ where
      env-sub1 : ∀ {Γ'' : Ctx}{Γ Γ' t t'} →
                 Γ ≡ (t' ∷ Γ'')    →
                 t' <: t         →
                 Γ'' ⊂ Γ'        →
                 Γ ⊂ (t ∷ Γ')
      env-sub2 : ∀ {Γ} → Γ ⊂ []


    ⊂-Env {Γ} {[]} p env = []
    ⊂-Env {Γ} {t ∷ Γ'} p env with any? (flip _<:?_ t) Γ
    ⊂-Env {.(_ ∷ _)} {t ∷ Γ'} (env-sub1 x x₁ p) (px₁ ∷ env) | yes (here px)
      rewrite (proj₂ (∷-injective x)) = (<:-val px px₁) ∷ ⊂-Env p env
    ⊂-Env {.(_ ∷ _)} {t ∷ Γ'} (env-sub1 x x₁ p) (px ∷ env) | yes (there q) rewrite (proj₂ (∷-injective x)) = {!!} ∷ ⊂-Env p env
    ... | no q = {!!}
    -}

    -- updating the environment

    update-env : ∀ {τ τ′ Γ} → Env Γ → (i : τ′ ∈ Γ) → Val τ → Env (i ∷= τ)
    update-env (x ∷ xs) (here px₁) v = v ∷ xs
    update-env (x ∷ xs) (there i) v = x ∷ update-env xs i v

    Fuel = ℕ

    run-step : ∀ {n}{Π : PCtx n}{Γ Γ′} → Fuel → PEnv Π → Program Π → Env Γ → Block Π Γ Γ′ → Maybe (Env Γ′)
    run-step zero Π prog env b = nothing
    run-step (suc n) Π prog env block-halt = just env
    run-step (suc n) Π prog env (block-jump {l = l} x x₁) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-seq x x₁) b) = run-step n Π prog env (block-seq x (block-seq x₁ b))
    run-step (suc n) Π prog env (block-seq (instr-branch-list idx x x₁) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-branch-listcons idx x x₁) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-branch-nil x x₁ x₂) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-fetch-0-new x) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-fetch-0-upd x idx) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-fetch-1-new x) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-fetch-1-upd x idx) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-cons-new x x₁ x₂) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-cons-upd x x₁ idx x₂) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-getlabel-0 idx) b) = {!!}
    run-step (suc n) Π prog env (block-seq (instr-getlabel idx x) b) = {!!}
