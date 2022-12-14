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

-- FEL: operatorok szama modell: ebbe kiertekelve megkapjuk a hasznalt
-- operatorok szamat, last a teszteket
M1 : Model
M1 = record
  { Tm = โ
  ; true = 1
  ; false = 1
  ; ite = ฮป m n o โ 1 + m + n + o
  ; num = ฮป n โ 1
  ; isZero = ฮป n โ 1 + n
  ; _+o_ = ฮป m n โ m + n + 1
  }
module M1 = Model M1
testM1 : M1.โฆ I.true I.+o I.false โง โก 3
testM1 = refl
testM1' : M1.โฆ I.num 100 โง โก 1
testM1' = refl
testM1'' : M1.โฆ I.isZero (I.ite I.false I.false (I.num 1 I.+o I.num 2)) โง โก 7
testM1'' = refl
testM1''' : M1.โฆ I.isZero (I.isZero (I.isZero (I.false))) โง โก 4
testM1''' = refl

-- FEL: szorzat modell: ket modell egyszerre
Prod : โ{i j} โ Model {i} โ Model {j} โ Model {i โ j}
Prod M N = record
  { Tm = M.Tm ร N.Tm
  ; true = M.true , N.true
  ; false = M.false , N.false
  ; ite = ฮป m n o โ (M.ite (ฯโ m) (ฯโ n) (ฯโ o) , N.ite (ฯโ m) (ฯโ n) (ฯโ o))
  ; num = ฮป n โ M.num n , N.num n
  ; isZero = ฮป t โ ((M.isZero (ฯโ t)) , (N.isZero (ฯโ t) ))
  ; _+o_ = ฮป t t' โ ฯโ t M.+o ฯโ t' , ฯโ t N.+o ฯโ t'
  }
  where
    module M = Model M
    module N = Model N

-- FEL: error modell: az M modellt hasznaljuk, de lehet, hogy error van, akkor meghagyjuk az errort
Error : โ{i j} โ Model {i} โ Set j โ Model {i โ j}
Error M E = record
  { Tm = M.Tm โ E -- osszeg tipus (Haskellben Either): egy eleme vagy egy M.Tm, vagy egy E
  ; true = ฮนโ M.true
  ; false = ฮนโ M.false
  ; ite =  ฮป { (ฮนโ m) (ฮนโ n) (ฮนโ o) โ ฮนโ ( M.ite m n o ) ; (ฮนโ e) _ _ โ ฮนโ e ; _ (ฮนโ e) _ โ ฮนโ e ; _ _ (ฮนโ e) โ ฮนโ e } 
  ; num = ฮป n โ ฮนโ (M.num n)
  ; isZero = ฮป { (ฮนโ t) โ ฮนโ (M.isZero t) ; (ฮนโ e) โ ฮนโ e }
  ; _+o_ = ฮป { (ฮนโ m) (ฮนโ n) โ ฮนโ (m M.+o n ) ; (ฮนโ e) _ โ ฮนโ e ; _ (ฮนโ e) โ ฮนโ e }
  }
  where
    module M = Model M
module E = Model (Error I โฅ)
testError : E.โฆ I.true โง โก ฮนโ I.true
testError = refl
testError' : E.โฆ I.num 1 I.+o I.num 2 โง โก ฮนโ (I.num 1 I.+o I.num 2)
testError' = refl
testError'' : E.โฆ I.ite (I.false) (I.num 2) (I.isZero (I.num 1 I.+o I.false)) โง โก ฮนโ (I.ite (I.false) (I.num 2) (I.isZero (I.num 1 I.+o I.false)))
testError'' = refl

-- FEL: "tipus" modell: ebben a modellben kiertekelve megkapjuk a term
-- tipusat, mely vagy Bool vagy Nat, vagy nem tipusozhato (pl. isZero true)
data Ty : Set where
  Bool  : Ty
  Nat   : Ty
  none  : Ty
M2 : Model
M2 = record
  { Tm = Ty
  ; true = Bool
  ; false = Bool
  ; ite = ฮป { Bool โ ? ; _ โ ?  }
  ; num = ฮป n โ Nat
  ; isZero = ฮป { Bool โ none ; Nat โ Bool ; none โ none }
  ; _+o_ = ฮป {Nat Nat โ Nat ; _ _ โ none}
  }
module M2 = Model M2
testM2 : M2.โฆ I.true โง โก Bool
testM2 = refl
testM2' : M2.โฆ I.false โง โก Bool
testM2' = refl
testM2'' : M2.โฆ I.num 1 I.+o I.num 2 โง โก Nat
testM2'' = refl
testM2''' : M2.โฆ I.isZero (I.num 1 I.+o I.num 2) โง โก Bool
testM2''' = refl
testM2'''' : M2.โฆ I.isZero (I.num 1 I.+o I.true) โง โก none
testM2'''' = refl
testM2''''' : M2.โฆ I.false I.+o I.true โง โก none
testM2''''' = refl
testM2'''''' : M2.โฆ I.ite I.true I.true I.false โง โก Bool
testM2'''''' = refl
testM2''''''' : M2.โฆ I.ite I.true (I.num 1) (I.num 2) โง โก Nat
testM2''''''' = refl
testM2'''''''' : M2.โฆ I.ite I.true (I.num 1) (I.false) โง โก none
testM2'''''''' = refl
testM2''''''''' : M2.โฆ I.isZero (I.false) โง โก none
testM2''''''''' = refl
 