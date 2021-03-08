open import Data.List
open import Data.Product
open import Data.String renaming (_≟_ to _≟s_)

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary hiding (Decidable ; _⊂_)

open import Subtyping
open import Type

module LeastSuperType where


-- definition of least subtype relation

data _∩_~_ : Ctx → Ctx → Ctx → Set
data _⊓_~_ : Ty → Ty → Ty → Set

data _⊔_~_ : Ty → Ty → Ty → Set
data _∪_~_ : Ctx → Ctx → Ctx → Set

data _∩_~_  where
  lub-ctx-1 : ∀ {Γ'} → [] ∩ Γ' ~ []
  lub-ctx-2 : ∀ {Γ}  → Γ ∩ [] ~ []
  lub-ctx-3 : ∀ {t t' t'' Γ Γ' Γ'' x} → -- @TODO: see this 'x'
                t ⊓ t' ~ t'' →
                Γ ∩ Γ' ~ Γ'' →
                ((x , t) ∷ Γ) ∩ ((x , t') ∷ Γ') ~ ((x , t'') ∷ Γ'')

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
  glb-ctx-3 : ∀ {t t' t'' Γ Γ' Γ'' x} → -- @TODO: see this 'x'
                t ⊔ t' ~ t'' →
                Γ ∪ Γ' ~ Γ'' →
                ((x , t) ∷ Γ) ∪ ((x , t') ∷ Γ') ~ ((x , t'') ∷ Γ'')


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

postulate 
  lubCtx : ∀ Γ Γ' → ∃ (λ Γ'' → Γ ∩ Γ' ~ Γ'')

glb : ∀ t1 t2 → ∃ (λ t3 → t1 ⊔ t2 ~ t3)

postulate
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

{-
lubCtx [] Γ' = [] , lub-ctx-1
lubCtx (t ∷ Γ) [] = [] , lub-ctx-2
lubCtx (t ∷ Γ) (t' ∷ Γ') with lub t t' | lubCtx Γ Γ'
...| t3 , p3 | Γ'' , p4 = t3 ∷ Γ'' , lub-ctx-3 p3 p4
-}

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

{-
glbCtx [] [] = [] , glb-ctx-1
glbCtx [] (t' ∷ Γ') = t' ∷ Γ' , glb-ctx-1
glbCtx (t ∷ Γ) [] = t ∷ Γ , glb-ctx-2
glbCtx (t ∷ Γ) (t' ∷ Γ') with glb t t' | glbCtx Γ Γ'
...| t3 , p3 | Γ'' , p4 = t3 ∷ Γ'' , glb-ctx-3 p3 p4
-}

-- relating subtyping and lub , glb


lub-subtype : ∀ {t1 t2 t3} → t1 ⊓ t2 ~ t3 → (t1 <: t3) × (t2 <: t3)

postulate 
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

{-
lubCtx-subtype lub-ctx-1 = env-sub2 , env-sub2
lubCtx-subtype lub-ctx-2 = env-sub2 , env-sub2
lubCtx-subtype (lub-ctx-3 x x₁) with lub-subtype x | lubCtx-subtype x₁
...| k1 , k2 | k3 , k4 = env-sub1 refl k1 k3 , env-sub1 refl k2 k4
-}

glbCtx-supertype glb-ctx-1 = env-sub2 , ⊂-refl
glbCtx-supertype glb-ctx-2 = ⊂-refl , env-sub2
glbCtx-supertype (glb-ctx-3 x x₁) with glb-supertype x | glbCtx-supertype x₁
...| k1 , k2 | k3 , k4 = env-sub1 refl k1 k3 , env-sub1 refl k2 k4

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

postulate 
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

{-
lubCtx-comm lub-ctx-1 = lub-ctx-2
lubCtx-comm lub-ctx-2 = lub-ctx-1
lubCtx-comm (lub-ctx-3 x p) with lub-comm x | lubCtx-comm p
...| q | q' = lub-ctx-3 q q'

glbCtx-comm glb-ctx-1 = glb-ctx-2
glbCtx-comm glb-ctx-2 = glb-ctx-1
glbCtx-comm (glb-ctx-3 x p) = glb-ctx-3 (glb-comm x) (glbCtx-comm p)
-}

-- correctness lemmas

lub-least : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⊓ τ₂ ~ τ₃ → τ₁ <: τ₄ → τ₂ <: τ₄ → τ₃ <: τ₄
glb-greatest : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⊔ τ₂ ~ τ₃ → τ₄ <: τ₁ → τ₄ <: τ₂ → τ₄ <: τ₃

postulate 
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

{-
glbCtx-greatest glb-ctx-1 p1 p2 = p2
glbCtx-greatest glb-ctx-2 p1 p2 = p1
glbCtx-greatest (glb-ctx-3 x p) (env-sub1 refl x₂ p1) (env-sub1 refl x₃ p2)
  = env-sub1 refl (glb-greatest x x₂ x₃) (glbCtx-greatest p p1 p2)

lubCtx-least lub-ctx-1 p1 p2 = p1
lubCtx-least lub-ctx-2 p1 p2 = p2
lubCtx-least (lub-ctx-3 x p) (env-sub1 refl x₂ p1) (env-sub1 refl x₄ p2) = env-sub1 refl (lub-least x x₂ x₄) (lubCtx-least p p1 p2)
lubCtx-least (lub-ctx-3 x p) env-sub2 p2 = env-sub2
-}
