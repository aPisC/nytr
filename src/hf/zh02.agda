{- BEGIN FIX -}
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

-- FEL: isZero operatorok szama
{- END FIX -}
M3 : Model
M3 = record
  { Tm = ℕ
  ; true = 0
  ; false = 0
  ; ite = λ m n o → m + n + o
  ; num = λ n → 0
  ; isZero = λ t → (1 + t)
  ; _+o_ = λ m n → m + n
  }
{- BEGIN FIX -}
module M3 = Model M3
testM3 : M3.⟦ I.isZero (I.num 1) ⟧ ≡ 1
testM3 = refl
testM3' : M3.⟦ I.isZero (I.isZero (I.isZero (I.num 1))) ⟧ ≡ 3
testM3' = refl
testM3'' : M3.⟦ I.isZero (I.isZero (I.isZero (I.isZero I.true I.+o I.isZero I.false))) ⟧ ≡ 5
testM3'' = refl
testM3''' : M3.⟦ I.ite (I.isZero I.true) (I.isZero I.false) I.true ⟧ ≡ 2
testM3''' = refl
testM3'''' : M3.⟦ I.ite (I.isZero (I.isZero I.true)) (I.isZero I.false) (I.isZero I.false I.+o I.true) ⟧ ≡ 4
testM3'''' = refl
{- END FIX -}
