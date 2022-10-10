{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)
infixr 2 _×_
_×_ : ∀{ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)
infixr 1 _⊎_
data _⊎_ {ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B
data ⊥ : Set where
module I where
  data Tm   : Set where
    true    : Tm
    false   : Tm
    ite     : Tm → Tm → Tm → Tm
    num     : ℕ → Tm
    isZero  : Tm → Tm
    _+o_    : Tm → Tm → Tm
record Model {ℓ} : Set (lsuc ℓ) where
  field
    Tm      : Set ℓ
    true    : Tm
    false   : Tm
    ite     : Tm → Tm → Tm → Tm
    num     : ℕ → Tm
    isZero  : Tm → Tm
    _+o_    : Tm → Tm → Tm
  ⟦_⟧ : I.Tm → Tm
  ⟦ I.true          ⟧ = true
  ⟦ I.false         ⟧ = false
  ⟦ I.ite t t' t''  ⟧ = ite ⟦ t ⟧ ⟦ t' ⟧ ⟦ t'' ⟧
  ⟦ I.num n         ⟧ = num n
  ⟦ I.isZero t      ⟧ = isZero ⟦ t ⟧
  ⟦ t I.+o t'       ⟧ = ⟦ t ⟧ +o ⟦ t' ⟧
I : Model
I = record { Tm = I.Tm ; true = I.true ; false = I.false ; ite = I.ite ; num = I.num ; isZero = I.isZero ; _+o_ = I._+o_ }

-- FEL: operatorok szama modell: ebbe kiertekelve megkapjuk a hasznalt
-- operatorok szamat, last a teszteket
M1 : Model
M1 = record
  { Tm = ℕ
  ; true = 1
  ; false = 1
  ; ite = λ m n o → 1 + m + n + o
  ; num = λ n → 1
  ; isZero = λ n → 1 + n
  ; _+o_ = λ m n → m + n + 1
  }
module M1 = Model M1
testM1 : M1.⟦ I.true I.+o I.false ⟧ ≡ 3
testM1 = refl
testM1' : M1.⟦ I.num 100 ⟧ ≡ 1
testM1' = refl
testM1'' : M1.⟦ I.isZero (I.ite I.false I.false (I.num 1 I.+o I.num 2)) ⟧ ≡ 7
testM1'' = refl
testM1''' : M1.⟦ I.isZero (I.isZero (I.isZero (I.false))) ⟧ ≡ 4
testM1''' = refl

-- FEL: szorzat modell: ket modell egyszerre
Prod : ∀{i j} → Model {i} → Model {j} → Model {i ⊔ j}
Prod M N = record
  { Tm = M.Tm × N.Tm
  ; true = M.true , N.true
  ; false = M.false , N.false
  ; ite = λ m n o → (M.ite (π₁ m) (π₁ n) (π₁ o) , N.ite (π₂ m) (π₂ n) (π₂ o))
  ; num = λ n → M.num n , N.num n
  ; isZero = λ t → ((M.isZero (π₁ t)) , (N.isZero (π₂ t) ))
  ; _+o_ = λ t t' → π₁ t M.+o π₁ t' , π₂ t N.+o π₂ t'
  }
  where
    module M = Model M
    module N = Model N

-- FEL: error modell: az M modellt hasznaljuk, de lehet, hogy error van, akkor meghagyjuk az errort
Error : ∀{i j} → Model {i} → Set j → Model {i ⊔ j}
Error M E = record
  { Tm = M.Tm ⊎ E -- osszeg tipus (Haskellben Either): egy eleme vagy egy M.Tm, vagy egy E
  ; true = ι₁ M.true
  ; false = ι₁ M.false
  ; ite =  λ { (ι₁ m) (ι₁ n) (ι₁ o) → ι₁ ( M.ite m n o ) ; (ι₂ e) _ _ → ι₂ e ; _ (ι₂ e) _ → ι₂ e ; _ _ (ι₂ e) → ι₂ e } 
  ; num = λ n → ι₁ (M.num n)
  ; isZero = λ { (ι₁ t) → ι₁ (M.isZero t) ; (ι₂ e) → ι₂ e }
  ; _+o_ = λ { (ι₁ m) (ι₁ n) → ι₁ (m M.+o n ) ; (ι₂ e) _ → ι₂ e ; _ (ι₂ e) → ι₂ e }
  }
  where
    module M = Model M
module E = Model (Error I ⊥)
testError : E.⟦ I.true ⟧ ≡ ι₁ I.true
testError = refl
testError' : E.⟦ I.num 1 I.+o I.num 2 ⟧ ≡ ι₁ (I.num 1 I.+o I.num 2)
testError' = refl
testError'' : E.⟦ I.ite (I.false) (I.num 2) (I.isZero (I.num 1 I.+o I.false)) ⟧ ≡ ι₁ (I.ite (I.false) (I.num 2) (I.isZero (I.num 1 I.+o I.false)))
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
  ; ite = λ { Bool → ? ; _ → ?  }
  ; num = λ n → Nat
  ; isZero = λ { Bool → none ; Nat → Bool ; none → none }
  ; _+o_ = λ {Nat Nat → Nat ; _ _ → none}
  }
module M2 = Model M2
testM2 : M2.⟦ I.true ⟧ ≡ Bool
testM2 = refl
testM2' : M2.⟦ I.false ⟧ ≡ Bool
testM2' = refl
testM2'' : M2.⟦ I.num 1 I.+o I.num 2 ⟧ ≡ Nat
testM2'' = refl
testM2''' : M2.⟦ I.isZero (I.num 1 I.+o I.num 2) ⟧ ≡ Bool
testM2''' = refl
testM2'''' : M2.⟦ I.isZero (I.num 1 I.+o I.true) ⟧ ≡ none
testM2'''' = refl
testM2''''' : M2.⟦ I.false I.+o I.true ⟧ ≡ none
testM2''''' = refl
testM2'''''' : M2.⟦ I.ite I.true I.true I.false ⟧ ≡ Bool
testM2'''''' = refl
testM2''''''' : M2.⟦ I.ite I.true (I.num 1) (I.num 2) ⟧ ≡ Nat
testM2''''''' = refl
testM2'''''''' : M2.⟦ I.ite I.true (I.num 1) (I.false) ⟧ ≡ none
testM2'''''''' = refl
testM2''''''''' : M2.⟦ I.isZero (I.false) ⟧ ≡ none
testM2''''''''' = refl
 