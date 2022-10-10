{- BEGIN FIX -}
{-# OPTIONS --prop #-}
open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)

infix  4 _≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixl 2 _◾_
data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}
cong : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl
_⁻¹ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl
_◾_ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → ∀{a''} → a' ≡ a'' → a ≡ a''
refl ◾ refl = refl
_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z
_∎ : ∀{ℓ}{A : Set ℓ}(a : A) → a ≡ a
a ∎ = refl
record Lift {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk
  field un : A
open Lift public

record Model {ℓ} : Set (lsuc ℓ) where
  field
    Nat   : Set ℓ
    Zero  : Nat
    Suc   : Nat → Nat
  ⟦_⟧ : ℕ → Nat
  ⟦ zero ⟧ = Zero
  ⟦ suc n ⟧ = Suc ⟦ n ⟧
I : Model
I = record { Nat = ℕ ; Zero = 0 ; Suc = 1 +_ }
module I = Model I
record DepModel {ℓ} : Set (lsuc ℓ) where
  field
    Nat∙   : I.Nat → Set ℓ
    Zero∙  : Nat∙ I.Zero
    Suc∙   : {n : I.Nat} → Nat∙ n → Nat∙ (I.Suc n)
  ⟦_⟧ : (n : I.Nat) → Nat∙ n
  ⟦ zero ⟧ = Zero∙
  ⟦ suc n ⟧ = Suc∙ ⟦ n ⟧

D : DepModel
{- END FIX -}
D = record
  { Nat∙ = λ n → Lift (n + 2 ≡ 1 + n + 1)
  ; Zero∙ = {!!}
  ; Suc∙ = {!!}
  }
{- BEGIN FIX -}
module D = DepModel D
+2=1++1 : (n : ℕ) → n + 2 ≡ 1 + n + 1
+2=1++1 n = un D.⟦ n ⟧
{- END FIX -}
