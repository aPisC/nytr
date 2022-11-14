{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

module hf05 where

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.Bool public renaming (Bool to 𝟚; true to tt; false to ff)
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)

infix  4 _≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixl 2 _◾_
infix 5 _⁻¹
infixr 2 _×_
infixr 4 _,×=_

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

cong : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong₂ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}
        {a c : A}{b d : B}(f : A → B → C)(p : a ≡ c)(q : b ≡ d) →
        f a b ≡ f c d
cong₂ f refl refl = refl

cong₃ : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
        {a d : A}{b e : B}{c f : C}(g : A → B → C → D)(p : a ≡ d)(q : b ≡ e)(r : c ≡ f) →
        g a b c ≡ g d e f
cong₃ g refl refl refl = refl

_◾_ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → ∀{a''} → a' ≡ a'' → a ≡ a''
refl ◾ refl = refl

_⁻¹ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

_≡≡_ : ∀{ℓ}{A : Set ℓ}(x : A){y} → x ≡ y → x ≡ y
x ≡≡ x≡y = x≡y

_∎ : ∀{ℓ}{A : Set ℓ}(a : A) → a ≡ a
a ∎ = refl

_×_ : ∀{ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

_,×=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a') → {b b' : B} → b  ≡ b' → (a , b) ≡ (a' , b')
_,×=_ refl refl = refl

module I where
  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty

  data Con  : Set where
    ◇       : Con              -- \di2
    _▹_     : Con → Ty → Con   -- \t6

  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
  infixl 7 _+o_

  postulate
    Sub       : Con → Con → Set
    _⊚_       : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    ass       : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → (γ ⊚ δ) ⊚ θ ≡ γ ⊚ (δ ⊚ θ)
    id        : ∀{Γ} → Sub Γ Γ
    idl       : ∀{Γ Δ}{γ : Sub Δ Γ} → id ⊚ γ ≡ γ
    idr       : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ⊚ id ≡ γ

    ε         : ∀{Γ} → Sub Γ ◇
    ◇η        : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε

    Tm        : Con → Ty → Set
    _[_]      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    [∘]       : ∀{Γ Δ Θ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →  t [ γ ⊚ δ ] ≡ t [ γ ] [ δ ]
    [id]      : ∀{Γ A}{t : Tm Γ A} → t [ id ] ≡ t
    _,o_      : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
    p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
    q         : ∀{Γ A} → Tm (Γ ▹ A) A
    ▹β₁       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → p ⊚ (γ ,o t) ≡ γ
    ▹β₂       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → q [ γ ,o t ] ≡ t
    ▹η        : ∀{Γ Δ A}{γa : Sub Δ (Γ ▹ A)} → p ⊚ γa ,o q [ γa ] ≡ γa

    true      : ∀{Γ} → Tm Γ Bool
    false     : ∀{Γ} → Tm Γ Bool
    ite       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    iteβ₁     : ∀{Γ A u v} → ite {Γ}{A} true u v ≡ u
    iteβ₂     : ∀{Γ A u v} → ite {Γ}{A} false u v ≡ v
    true[]    : ∀{Γ Δ}{γ : Sub Δ Γ} → true [ γ ] ≡ true
    false[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → false [ γ ] ≡ false
    ite[]     : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} → (ite {Γ}{A} t u v) [ γ ] ≡ ite (t [ γ ]) (u [ γ ]) (v [ γ ])

    num       : ∀{Γ} → ℕ → Tm Γ Nat
    isZero    : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
    _+o_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
    isZeroβ₁  : ∀{Γ} → isZero (num {Γ} 0) ≡ true
    isZeroβ₂  : ∀{Γ n} → isZero (num {Γ} (1 + n)) ≡ false
    +β        : ∀{Γ m n} → num {Γ} m +o num n ≡ num (m + n)
    num[]     : ∀{Γ n Δ}{γ : Sub Δ Γ} → num n [ γ ] ≡ num n
    isZero[]  : ∀{Γ t Δ}{γ : Sub Δ Γ} → isZero t [ γ ] ≡ isZero (t [ γ ])
    +[]       : ∀{Γ u v Δ}{γ : Sub Δ Γ} → (u +o v) [ γ ] ≡ (u [ γ ]) +o (v [ γ ])

  v0 : {Γ : Con} → {A : Ty} → Tm (Γ ▹ A) A
  v0 = q
  v1 : {Γ : Con} → {A B : Ty} → Tm (Γ ▹ A ▹ B) A
  v1 = q [ p ]
  v2 : {Γ : Con} → {A B C : Ty} → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = q [ p ⊚ p ]
  v3 : {Γ : Con} → {A B C D : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = q [ p ⊚ p ⊚ p ]
  v4 : {Γ : Con} → {A B C D E : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) A
  v4 = q [ p ⊚ p ⊚ p ⊚ p ]
  v5 : {Γ : Con} → {A B C D E F : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F) A
  v5 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v6 : {Γ : Con} → {A B C D E F G : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G) A
  v6 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v7 : {Γ : Con} → {A B C D E F G H : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G ▹ H) A
  v7 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]

  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def t u = u [ id ,o t ]

open I

{- END FIX -}
eq-1 : def true (ite v0 ((num 3) +o (num 1)) (num 2)) ≡ num {◇} 4
eq-1 = 
  def true (ite v0 ((num 3) +o (num 1)) (num 2))
         ≡⟨ refl ⟩
  (ite q ((num 3) +o (num 1)) (num 2)) [ id ,o true ]
         ≡⟨ ite[] ⟩
  ite (q [ id ,o true ]) (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])
         ≡⟨ cong (λ z → (ite z (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])))  ▹β₂ ⟩
  ite (true) (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])
         ≡⟨ iteβ₁ ⟩
  ((num 3 +o num 1) [ id ,o true ])
         ≡⟨ cong (λ z → z [ id ,o true ]) +β ⟩
  (num 4 [ id ,o true ])
         ≡⟨ num[] ⟩
  num 4 
         ∎

v1β : ∀{Γ Δ A B}{γ : Sub Δ Γ}{a : Tm Δ A}{b : Tm Δ B} → v1 [ γ ,o a ,o b ] ≡ a
v1β {Γ} {Δ} {A} {B} {γ} {a} {b} = 
    q [ p ] [ γ ,o a ,o b ]
        ≡⟨ ([∘])⁻¹ ⟩
    q [ p ⊚ (γ ,o a ,o b) ]
        ≡⟨ cong (λ z → q [ z ]) ▹β₁ ⟩
    q [ γ ,o a ]
        ≡⟨ ▹β₂ ⟩
    a
        ∎

v2β : ∀{Γ Δ A B C}{γ : Sub Δ Γ}{a : Tm Δ A}{b : Tm Δ B}{c : Tm Δ C} → v2 [ γ ,o a ,o b ,o c ] ≡ a
v2β {Γ} {Δ} {A} {B} {C} {γ} {a} {b} {c} = 
    q [ p ⊚ p ] [ γ ,o a ,o b ,o c ] 
        ≡⟨ ([∘])⁻¹ ⟩
    q [ (p ⊚ p) ⊚ (γ ,o a ,o b ,o c) ]
        ≡⟨ cong (λ z → q [ z ]) ass ⟩ 
    q [ p ⊚ (p ⊚ (γ ,o a ,o b ,o c)) ]
        ≡⟨ cong (λ z → q [ p ⊚ z ]) ▹β₁ ⟩
    q [ p ⊚ (γ ,o a ,o b) ]
        ≡⟨ cong (λ z → q [ z ]) ▹β₁ ⟩
    q [ γ ,o a ]
        ≡⟨ ▹β₂ ⟩
    a 
        ∎

eq-2 : ite v1 (isZero v0) false [ ε ,o true ,o num 0 ] ≡ true {◇}
eq-2 = 
    ite (q [ p ]) (isZero q) false [ ε ,o true ,o num zero ] 
        ≡⟨ ite[] ⟩ 
    ite (q [ p ] [ ε ,o true ,o num zero ]) (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ]) 
        ≡⟨ cong (λ z → ite z (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ])) (([∘])⁻¹) ⟩ 
    ite (q [ p ⊚ (ε ,o true ,o num zero) ]) (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ])
        ≡⟨ cong (λ z → ite (q [ z ]) (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ]))  ▹β₁ ⟩ 
    ite (q [ (ε ,o true ) ]) (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ])
        ≡⟨ cong (λ z → ite z (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ])) ▹β₂ ⟩ 
    ite true (isZero q [ ε ,o true ,o num zero ]) (false [ ε ,o true ,o num zero ])
        ≡⟨ iteβ₁ ⟩ 
    (isZero q) [ ε ,o true ,o num zero ]
        ≡⟨ isZero[] ⟩ 
    isZero (q [ ε ,o true ,o num zero ])
        ≡⟨ cong (λ z → isZero z) ▹β₂ ⟩ 
    isZero (num zero)
        ≡⟨ isZeroβ₁ ⟩ 
    true 
        ∎

eq-3 : isZero (ite v0 (num 1) v1) [ ε ,o num 0 ,o false ] ≡ true {◇}
eq-3 = {!!}

sub-eq-1 : {Γ : Con} → {σ δ : Sub Γ ◇} → σ ≡ δ
sub-eq-1 {Γ} {σ} {δ} = σ ≡⟨ (◇η {Γ} {σ}) ⟩ ε ≡⟨ (◇η {Γ} {δ})⁻¹ ⟩ δ ∎

sub-eq-2 : {Γ Δ : Con} → {σ : Sub Γ Δ} → ε ⊚ σ ≡ ε
sub-eq-2 = ◇η

sub-eq-3 : ε ≡ id
sub-eq-3 = (◇η)⁻¹

sub-eq-4 : {Γ : Con}{A : Ty} → (p ,o q) ≡ id {Γ ▹ A}
sub-eq-4 = {!!}

sub-eq-5 : ∀{Γ A} → (id ⊚ p ,o q) ≡ id {Γ ▹ A}
sub-eq-5 = {!!}
