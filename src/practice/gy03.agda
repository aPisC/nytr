{-# OPTIONS --prop --rewriting #-}

module gy03 where

open import Lib
open import NatBoolAST hiding (T)

tm1 : I.Tm
tm1 = ite true (_+o_ (num 1) (num 3)) (isZero (isZero false))
  where open I

-- FEL: do all the compulsory exercises from the book!

-- FEL: count the number of trues in a term (exercise 1.10 in the book)
Trues : Model {lzero}
Model.Tm Trues = ℕ
Model.true Trues = 1
Model.false Trues = 0
<<<<<<< Updated upstream
Model.ite Trues t t' t'' = t + t' + t''
Model.num Trues n = 0
Model.isZero Trues t = t
Model._+o_ Trues = _+_
=======
Model.ite Trues m n o = m + n + o
Model.num Trues n = 0
Model.isZero Trues n = n
Model._+o_ Trues  = λ m n →  m + n  
>>>>>>> Stashed changes

module testTrues where
  module M = Model Trues

  t : M.Tm
  t = M.true

  t' : M.Tm
  t' = 10

  test1 : M.⟦ I.false I.+o (I.num 1) ⟧ ≡ 0
  test1 = refl -- M.⟦ I.false I.+o I.num 1 ⟧ = M.⟦ I.false ⟧ M.+o M.⟦ I.num 1 ⟧ = M.false M.+o M.num 1 = 0 + 0 = 0
  test2 : M.⟦ tm1 ⟧ ≡ 1
  test2 = refl
  test3 : M.⟦ I.ite I.true I.true I.true ⟧ ≡ 3
  test3 = refl

  -- FEL: adj meg ket kulonbozo termet, melyek ertelmezese 2
  t2 t3 : I.Tm
  t2 = I.true I.+o I.true
<<<<<<< Updated upstream
  t3 = I.true I.+o I.isZero I.true
=======
  t3 = I.true I.+o I.false I.+o I.true
>>>>>>> Stashed changes
  t2≠t3 : ¬ (t2 ≡ t3)
  t2≠t3 ()
  testt2 : M.⟦ t2 ⟧ ≡ 2
  testt2 = refl
  testt3 : M.⟦ t3 ⟧ ≡ 2
  testt3 = refl

-- FEL: number of nodes in the tree
N : Model {lzero}
N = record
      { Tm = ℕ
      ; true = 1
      ; false = 1
      ; ite = λ t t' t'' → 1 + t + t' + t''
      ; num = λ _ → 1
      ; isZero = suc
      ; _+o_ = λ t t' → 1 + t + t'
      }
module testN where
  module N = Model N

  f : ℕ → I.Tm
  f zero = I.true
  f (suc n) = I.isZero (f n)

  flen : (n : ℕ) → N.⟦ f n ⟧ ≡ suc n
  flen zero = refl
  flen (suc n) = cong suc (flen n)

ite : ℕ → ℕ → ℕ → ℕ
ite zero a b = b
ite (suc _) a b = a

isZero : ℕ → ℕ
isZero zero = 1
isZero (suc _) = 0

-- FEL: C stilusu modell
C : Model {lzero}
<<<<<<< Updated upstream
C = record
      { Tm = ℕ
      ; true = 1
      ; false = 0
      ; ite = ite
      ; num = λ n → n
      ; isZero = isZero
      ; _+o_ = _+_
      }
=======
Model.Tm C = ℕ
Model.true C = 1
Model.false C = 0
Model.ite C zero n o = o
Model.ite C (suc m) n o = n
Model.num C n = n
Model.isZero C zero = 1
Model.isZero C (suc n) = 0
Model._+o_ C m n = m + n
>>>>>>> Stashed changes

module testC where
  module M = Model C

  test1 : M.⟦ I.false ⟧ ≡ 0
  test1 = refl
  test2 : M.⟦ I.true ⟧ ≡ 1
  test2 = refl
  test3 : M.⟦ I.ite (I.num 100) (I.num 3) (I.num 2) ⟧ ≡ 3
  test3 = refl
  test4 : M.⟦ I.ite (I.num 0) (I.num 3) (I.num 2) I.+o I.num 3 ⟧ ≡ 5
  test4 = refl

  test5 : M.true ≡ M.isZero (M.num 0)
  test5 = refl

-- mutasd meg, hogy true ≠ isZero (num 0) a szintaxisban! ehhez adj
-- meg egy modellt, amiben a true tt-re, az isZero (num 0) ff-re
-- ertekelodik!
TN : Model {lzero}
TN = record
  { Tm = 𝟚
  ; true = tt
<<<<<<< Updated upstream
  ; false = tt
  ; ite = λ _ _ _ → tt
  ; num = λ _ → tt
  ; isZero = λ _ → ff
  ; _+o_ = λ _ _ → tt
=======
  ; false = ff
  ; ite  = λ m n o → {! m  !}
  ; num = λ { zero -> tt ; (suc n) -> ff }
  ; isZero = λ n → ff
  ; _+o_ = {!!}
>>>>>>> Stashed changes
  }
true≠isZeronum0 : ¬ (I.true ≡ I.isZero (I.num 0))
true≠isZeronum0 e = tt≠ff (cong TN.⟦_⟧ e)
  -- tt≠ff (cong TN.⟦_⟧ e)          -- cong f : a ≡ b → f a ≡ f b
  -- e : I.true ≡ I.isZero (I.num 0)
  -- cong TN.⟦_⟧ e : TN.⟦ I.true ⟧ ≡ TN.⟦ I.isZero (I.num 0) ⟧
  where module TN = Model TN

-- nemsztenderd modell (a szintaxis ertelmezese nem rakepzes)
NS : Model {lzero}
NS = record
       { Tm = ℕ
       ; true = 2
       ; false = 0
       ; ite = λ { zero a b → b ; _ a b → a }
       ; num = λ n → n + n
       ; isZero = λ { zero → 2 ; _ → 0 }
       ; _+o_ = _+_
       }
module testNS where
  module NS = Model NS

  -- adj meg egy ℕ-t, amire nem kepez egyik term sem
  n : ℕ
  n = 1

  -- bizonyitsd be, hogy minden szintaktikus term ertelmezese paros szam
  ps : (t : I.Tm) → Σsp ℕ λ m → NS.⟦ t ⟧ ≡ m + m
  ps = {!!} -- KESOBB

-- FEL: add meg a legegyszerubb nemsztenderd modellt!
NS' : Model {lzero}
NS' = record
  { Tm = 𝟚
  ; true = ff
  ; false = ff
  ; ite = λ _ _ _ → ff
<<<<<<< Updated upstream
  ; num = λ _ → ff
  ; isZero = λ _ → ff
  ; _+o_ = λ _ _ → ff
=======
  ; num = λ n → ff
  ; isZero = λ n → ff
  ; _+o_ = λ m n → ff
>>>>>>> Stashed changes
  }
module testNS' where
  module NS' = Model NS'
  b : 𝟚
  b = tt

  -- indukcio
  D : DepModel {lzero}
<<<<<<< Updated upstream
  D = record
        { Tm∙ = λ t → Lift (NS'.⟦ t ⟧ ≡ ff)  -- \[[            -- mk : A ↔ Lift A : un
        ; true∙ = mk refl
        ; false∙ = mk refl
        ; ite∙ = λ _ _ _ → mk refl
        ; num∙ = λ _ → mk refl
        ; isZero∙ = λ _ → mk refl
        ; _+o∙_ = λ _ _ → mk refl
        }
=======
  DepModel.Tm∙ D = λ t → Lift (NS'.⟦ t ⟧ ≡ ff)
  DepModel.true∙ D = mk refl
  DepModel.false∙ D = mk refl
  DepModel.ite∙ D m n o = mk refl
  DepModel.num∙ D = λ n → mk refl
  DepModel.isZero∙ D n = mk refl
  DepModel._+o∙_ D m n = mk refl
>>>>>>> Stashed changes
  module D = DepModel D
  
  ∀ff : (t : I.Tm) → NS'.⟦ t ⟧ ≡ ff
  ∀ff t = un D.⟦ t ⟧
  
  ns : (Σsp I.Tm λ t → NS'.⟦ t ⟧ ≡ tt) → ⊥
  ns e = tt≠ff (π₂ e ⁻¹ ◾ ∀ff (π₁ e))
