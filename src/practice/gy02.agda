{-# OPTIONS --prop --rewriting #-}

module gy02 where

open import Lib

-- Natural numbers

addTwo : ℕ → ℕ
addTwo = 2 +_

addTwo-test-1 : addTwo 0 ≡ 2
addTwo-test-1 = refl 

addTwo-test-2 : addTwo 3 ≡ 5
addTwo-test-2 = refl

_*2+1 : ℕ → ℕ
_*2+1 = λ x → suc (x + x) 

*2+1-test-1 : 3 *2+1 ≡ 7
*2+1-test-1 = refl -- refl

plus : ℕ → ℕ → ℕ
plus = _+_ 

plus-idl : (n : ℕ) → plus 0 n ≡ n
plus-idl n = refl

plus-idr : (n : ℕ) → plus n 0 ≡ n
plus-idr zero = refl
plus-idr (suc n) = cong ℕ.suc (plus-idr n) 

-- plus-idr (suc n) = cong ℕ.suc { n + 0 } { n }  (plus-idr n) 

-- NatBool nyelv AST szinten

open import NatBoolAST hiding ( T )

  {-
          ite
        /  |  \
       /   |   \
     true  +o   isZero
          /\        |
         /  \       |
    num 1  num 3  isZero
                    |
                    |
                  false
  -}
tm1 : I.Tm
tm1 = ite true ((num 1) +o (num 3)) (isZero (isZero false))
  where open I
  
-- more exercises from the book

t1 : I.Tm
t1 = tm1

t1-test : height t1 ≡ 3
t1-test = refl

t2 : I.Tm
t2 = ite false ((num 1) +o (num 3)) (isZero (isZero false))
  where open I

t2-test-1 : height t2 ≡ 3
t2-test-1 = refl

t2-test-2 : ¬ (t1 ≡ t2)
t2-test-2 ()

-- ird le az alabbi nyelveket data-val!

-- T ::= op0 | op1 T | op2 T T | op3 T T T | op4 T T T T

module examples where  
  data T : Set where
    op0 : T
    op1 : T → T  
    op2 : T → T  → T  
    op3 : T → T  → T  → T  
    op4 : T → T  → T  → T  → T 

-- A ::= a | fb B
-- B ::= fa A
  data A : Set
  data B : Set
  data A where
    a : A
    fb : B → A
  data B where
    fa : A → B


-- V ::= vzero | vsuc V
-- E ::= num N | E < E | E = E | var V
-- C ::= V := E | while E S | if E then S else S
-- S ::= empty | C colon S

  data V : Set
  data E : Set
  data C : Set
  data S : Set
  data V where
    vzero : V
    vsuc : V → V  
  data E where
    num : ℕ → E
    _le_ : E → E → E
    _eq_ : E → E → E
    var : V → E
  data C where
    _:=_ : V → E → C
    while : E → S → C
    if_then_else : E → S → S → C 
  data S where
    empty : S
    _colon_ : C → S → S


-- Model Tm-re
-- ujradefinialni height-ot modell segitsegevel

HH : Model
Model.Tm HH = ℕ
Model.true HH = 0
Model.false HH = 0
Model.ite HH = λ m n o → suc (max m (max n o))
Model.num HH = λ n → 0
Model.isZero HH = suc
Model._+o_ HH = λ m n → suc (max m n)
{-
  height definition 

  height : I.Tm → ℕ
  height I.true            = 0
  height I.false           = 0
  height (I.ite t t' t'')  = 1 + max (height t) (max (height t') (height t''))
  height (I.num n)         = 0
  height (I.isZero t)      = 1 + height t
  height (t I.+o t')       = 1 + max (height t) (height t')

-}
-- modell: Count the number of trues in a term

Trues : Model {lzero}
Trues = {!!}

module testTrues where
  module M = Model Trues

  -- kulonbseg modell-beli es szintaktikus termek kozott
  t : M.Tm
  t = M.true

  t' : M.Tm
  t' = 10

  test1 : M.⟦ I.false I.+o (I.num 1) ⟧ ≡ 0
  test1 = refl
  test2 : M.⟦ tm1 ⟧ ≡ 1
  test2 = refl
  test3 : M.⟦ I.ite I.true I.true I.true ⟧ ≡ 3
  test3 = refl


-- C stilusu interpreter

C : Model {lsuc lzero}
C = {!!}

module testC where
  module M = Model C
  open I

  test1 : M.⟦ false ⟧ ≡ 0
  test1 = refl
  test2 : M.⟦ true ⟧ ≡ 1
  test2 = refl
  test3 : M.⟦ ite (num 100) (num 3) (num 2) ⟧ ≡ 3
  test3 = refl
  test4 : M.⟦ ite (num 0) (num 3) (num 2) +o num 3 ⟧ ≡ 5
  test4 = refl
