{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to โ)
open import Agda.Builtin.Bool renaming (Bool to ๐; true to tt; false to ff)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma public renaming (fst to ฯโ; snd to ฯโ)
infixr 2 _ร_
_ร_ : โ{โ}{โ'}(A : Set โ)(B : Set โ') โ Set (โ โ โ')
A ร B = ฮฃ A (ฮป _ โ B)
infixr 1 _โ_
data _โ_ {โ}{โ'}(A : Set โ)(B : Set โ') : Set (โ โ โ') where
  ฮนโ : A โ A โ B
  ฮนโ : B โ A โ B
data โฅ : Set where
module I where
  data Tm   : Set where
    true    : Tm
    false   : Tm
    ite     : Tm โ Tm โ Tm โ Tm
    num     : โ โ Tm
    isZero  : Tm โ Tm
    _+o_    : Tm โ Tm โ Tm
record Model {โ} : Set (lsuc โ) where
  field
    Tm      : Set โ
    true    : Tm
    false   : Tm
    ite     : Tm โ Tm โ Tm โ Tm
    num     : โ โ Tm
    isZero  : Tm โ Tm
    _+o_    : Tm โ Tm โ Tm
  โฆ_โง : I.Tm โ Tm
  โฆ I.true          โง = true
  โฆ I.false         โง = false
  โฆ I.ite t t' t''  โง = ite โฆ t โง โฆ t' โง โฆ t'' โง
  โฆ I.num n         โง = num n
  โฆ I.isZero t      โง = isZero โฆ t โง
  โฆ t I.+o t'       โง = โฆ t โง +o โฆ t' โง
I : Model
I = record { Tm = I.Tm ; true = I.true ; false = I.false ; ite = I.ite ; num = I.num ; isZero = I.isZero ; _+o_ = I._+o_ }

-- FEL: isZero operatorok szama
{- END FIX -}
M3 : Model
M3 = record
  { Tm = โ
  ; true = 0
  ; false = 0
  ; ite = ฮป m n o โ m + n + o
  ; num = ฮป n โ 0
  ; isZero = ฮป t โ (1 + t)
  ; _+o_ = ฮป m n โ m + n
  }
{- BEGIN FIX -}
module M3 = Model M3
testM3 : M3.โฆ I.isZero (I.num 1) โง โก 1
testM3 = refl
testM3' : M3.โฆ I.isZero (I.isZero (I.isZero (I.num 1))) โง โก 3
testM3' = refl
testM3'' : M3.โฆ I.isZero (I.isZero (I.isZero (I.isZero I.true I.+o I.isZero I.false))) โง โก 5
testM3'' = refl
testM3''' : M3.โฆ I.ite (I.isZero I.true) (I.isZero I.false) I.true โง โก 2
testM3''' = refl
testM3'''' : M3.โฆ I.ite (I.isZero (I.isZero I.true)) (I.isZero I.false) (I.isZero I.false I.+o I.true) โง โก 4
testM3'''' = refl
{- END FIX -}
