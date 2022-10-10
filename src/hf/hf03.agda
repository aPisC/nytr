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

-- a *2+1 model
M : Model
M = record
  { Nat  = ℕ
  ; Zero = 1
  ; Suc  = λ n → suc (suc n) }
module M = Model M

-- nehany teszteset
testM : M.⟦ 3 ⟧ ≡ 3 * 2 + 1
testM = refl
testM' : M.⟦ 5 ⟧ ≡ 5 * 2 + 1
testM' = refl

-- belatjuk, hogy az ebbe a modellbe valo kiertekeles tenlyeg beszoroz 2-vel es hozzad egyet
D : DepModel
D = record
  { Nat∙ = λ n → Lift (M.⟦ n ⟧ ≡ n * 2 + 1)
  ; Zero∙ = mk refl
  ; Suc∙ = λ (mk n∙) → mk (cong (λ z → suc (suc z)) n∙)
  }
module D = DepModel D
M=*2+1 : (n : ℕ) → M.⟦ n ⟧ ≡ n * 2 + 1
M=*2+1 n = un D.⟦ n ⟧

-- a nulla jobb identitas
D' : DepModel
D' = record
  { Nat∙ = λ n → Lift (n + 0 ≡ n)
  ; Zero∙ = mk refl -- ez konnyu
  ; Suc∙ = λ (mk n∙) → mk (cong suc n∙) -- hasznald "cong suc"-ot es "n∙"-t
  }
module D' = DepModel D'
idr+ : (n : ℕ) → n + 0 ≡ n
idr+ n = un D'.⟦ n ⟧

-- osszeadas asszociativitasa
D'' : DepModel
D'' = record
  { Nat∙ = λ m → ∀ n o → Lift ((m + n) + o ≡ m + (n + o))
  ; Zero∙ = λ _ _ → mk refl
  ; Suc∙ = λ {m} m∙ n o → mk (cong suc (un( m∙ n o))) -- hasznald "cong suc"-ot, "m∙"-ot, es "un"-t
  }
module D'' = DepModel D''
ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ m n o = un (D''.⟦ m ⟧ n o)

-- +suc-ra vonatkozo egyenloseg
D''' : DepModel
D''' = record
  { Nat∙ = λ m → ∀ n → Lift (m + suc n ≡ suc m + n)
  ; Zero∙ = λ n → mk (cong suc refl)
  ; Suc∙ = λ {m} m∙ n → mk (cong suc (un (m∙ n))) -- hasznald "cong suc"-ot, "m∙"-t, "un"-t
  }
module D''' = DepModel D'''
+suc : (m n : ℕ) → m + suc n ≡ suc m + n
+suc m n = un (D'''.⟦ m ⟧ n)

-- osszeadas kommutativitasa
D'''' : DepModel
D'''' = record
  { Nat∙ = λ m → ∀ n → Lift (m + n ≡ n + m)
  ; Zero∙ = λ n → mk ((idr+ n)⁻¹) -- hasznald idr+-t es ⁻¹-et!
  ; Suc∙ = λ {m} m∙ n → mk ((
    suc (m + n)
                    ≡⟨ cong suc (un (m∙ n)) ⟩ -- hasznald "cong suc"-ot, "m∙"-t, "un"-t
    suc (n + m)
                    ≡⟨ cong suc refl ⟩ -- ez konnyu
    suc n + m
                    ≡⟨ (+suc n m )⁻¹ ⟩ -- hasznald "+suc"-ot es "_⁻¹"-t
    n + suc m
    ∎))
  }
module D'''' = DepModel D''''
+comm : (m n : ℕ) → m + n ≡ n + m
+comm m n = un (D''''.⟦ m ⟧ n)

-- valami egyenloseg
D''''' : DepModel {lzero}
D''''' = record
  { Nat∙ = λ n → Lift(n + 3 ≡ 1 + n + 2) -- lasd lejjebb, hogy mi legyen Nat∙
  ; Zero∙ = mk refl
  ; Suc∙ =  λ {n} (mk n∙) → mk (suc (n + 3)
          ≡⟨ cong suc n∙ ⟩
      
    suc (suc (n + 2)) 
          ∎) 
  }
module D''''' = DepModel D'''''
+2=1++1 : (n : ℕ) → n + 3 ≡ 1 + n + 2
+2=1++1 n = un D'''''.⟦ n ⟧
