{-# OPTIONS --prop --rewriting #-}

module hf07import where

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.Bool public renaming (Bool to 𝟚; true to tt; false to ff)
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)

infix  4 _≡_ _≈_
infixr 2 _≡≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixr 7 _⊃_
infixl 8 _∨_
infixl 9 _∧_
infixr 1 _⊎_
infixr 2 _×_
infixr 4 _,_
infixr 4 _,=_ _,×=_
infixl 6 _∘_
infixl 2 _◾_
infix 5 _⁻¹


-- rewriting

postulate _≈_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Set ℓ
{-# BUILTIN REWRITE _≈_ #-}


-- exercise

postulate
  exercise  : ∀{ℓ}{A : Set  ℓ} → A
  exercisep : ∀{ℓ}{A : Prop ℓ} → A

-- Bottom

data ⊥ : Prop where

exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

exfalsop : ∀{ℓ}{A : Prop ℓ} → ⊥ → A
exfalsop ()

¬_ : ∀{ℓ}(A : Prop ℓ) → Prop ℓ
¬ A = A → ⊥


-- Top

record ⊤ : Prop where
  constructor triv

-- Functions

_∘_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : A → Set ℓ'}{C : ∀ {x} → B x → Set ℓ''}
  (f : ∀ {x} (y : B x) → C y)(g : (x : A) → B x)
  (x : A) → C (g x)
(f ∘ g) x = f (g x)


-- Lift

record Lift {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk
  field un : A
open Lift public


-- Raise

record Raise {ℓ ℓ'}(A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor mk
  field un : A
open Raise public


-- Equality

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≢_

_≢_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Prop ℓ
x ≢ y = ¬ (x ≡ y)

_◾_ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → ∀{a''} → a' ≡ a'' → a ≡ a''
refl ◾ refl = refl

postulate transp       : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
postulate transprefl   : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → transp P e p ≈ p

{-# REWRITE transprefl   #-}
-- {-# REWRITE transpconst  #-}
-- {-# REWRITE transptransp #-}

_⁻¹ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl

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

transpconst  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}{e : a ≡ a'}{b : B} → transp (λ _ → B) e b ≡ b
transpconst {e = refl} = refl

transptransp : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' a'' : A}(e : a ≡ a'){e' : a' ≡ a''}{p : P a} → transp P e' (transp P e p) ≡ transp P (e ◾ e') p
transptransp P refl {refl} = refl

transp→' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B → C a} → 
  transp (λ a → B → C a) e f ≡ λ b → transp C e (f b)
transp→' C refl = refl

transp→i' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : {b : B} → C a} → 
  (λ {b} → transp (λ a → {_ : B} → C a) e (λ {b} → f {b}) {b}) ≡ (λ {b} → transp C e (f {b}))
transp→i' C refl = refl

transpΠ' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){f : (b : B) → C a b} → 
  transp (λ a → (b : B) → C a b) e f ≡ λ b → transp (λ a → C a b) e (f b)
transpΠ' C refl = refl

transpΠi' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){f : {b : B} → C a b} → 
  (λ {b} → transp (λ a → {b : B} → C a b) e f {b}) ≡ λ {b} → transp (λ a → C a b) e (f {b})
transpΠi' C refl = refl

transp→ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B a → C a} → 
  transp (λ a → B a → C a) e f ≡ λ b' → transp C e (f (transp B (e ⁻¹) b'))
transp→ C refl = refl

transpcong : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : B → Set ℓ'')(f : A → B){a a' : A}(e : a ≡ a'){c : C (f a)} → transp {A = B} C {f a} {f a'} (cong f e) c ≡ transp {A = A} (λ a → C (f a)) {a} {a'} e c
transpcong C f refl = refl

transp$ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}(f : ∀ a → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → f a' (transp B e b) ≡ transp C e (f a b) 
transp$ f refl = refl

transp$i : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}(f : ∀{a} → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → f (transp B e b) ≡ transp C e (f b) 
transp$i f refl = refl

-- if this doesn't normalise (C-c C-n PROBLEM), then your Agda is too old
PROBLEM : {A : Set}(B : A → Prop){a a' : A}(e : a ≡ a') → B a → Lift (B a')
PROBLEM B e b = transp (λ a → Lift (B a)) e (mk b)

_~ : ∀{ℓ ℓ'}{A : Set ℓ}(B : A → Set ℓ'){a₀ a₁ : A}(a₀₁ : a₀ ≡ a₁) → B a₀ → B a₁ → Prop ℓ'
(B ~) a₀₁ b₀ b₁ = transp B a₀₁ b₀ ≡ b₁

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

_≡≡_ : ∀{ℓ}{A : Set ℓ}(x : A){y} → x ≡ y → x ≡ y
x ≡≡ x≡y = x≡y

_∎ : ∀{ℓ}{A : Set ℓ}(a : A) → a ≡ a
a ∎ = refl

transpP : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'
transpP P refl p = p

UIP : ∀{ℓ}{A : Set ℓ}{a a' : A}{e e' : a ≡ a'} → _≡_ {A = Lift (a ≡ a')} (mk e) (mk e')
UIP = refl


-- Function space

postulate funext  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
postulate funexti : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g


-- Maybe

data Maybe {ℓ}(A : Set ℓ) : Set ℓ where
  Nothing  : Maybe A
  Just     : A → Maybe A

caseMaybe : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (A → B) → Maybe A → B
caseMaybe n j Nothing = n
caseMaybe n j (Just a) = j a


-- Product

_×_ : ∀{ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

_,=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{a a' : A}(e : a ≡ a') → {b : B a}{b' : B a'} → (B ~) e b b' → (a , b) ≡ (a' , b')
_,=_ refl refl = refl

_,×=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a') → {b b' : B} → b  ≡ b' → (a , b) ≡ (a' , b')
_,×=_ refl refl = refl

record Σsp {ℓ ℓ'} (A : Set ℓ)(B : A → Prop ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σsp public

_,=- : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Prop ℓ'}{a a' : A}(e : a ≡ a') → {b : B a}{b' : B a'} → _≡_ {A = Σsp A B} (a , b) (a' , b')
_,=- refl = refl

transp× : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){a : A}{w : B a × C a}{a' : A}(e : a ≡ a') →
  transp (λ a → B a × C a) e w ≡ (transp B e (π₁ w) , transp C e (π₂ w))
transp× B C refl = refl

transpΣ' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ''){a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
  transp (λ a → Σ B (C a)) e w ≡ (π₁ w , transp (λ a → C a (π₁ w)) e (π₂ w))
transpΣ' C refl = refl


-- ℕ

max : ℕ → ℕ → ℕ
max zero    b       = b
max (suc a) zero    = suc a
max (suc a) (suc b) = suc (max a b)

iteℕ : ∀{ℓ}{A : Set ℓ}(u : A)(v : A → A)(t : ℕ) → A
iteℕ u v zero = u
iteℕ u v (suc t) = v (iteℕ u v t)

indℕ : ∀{ℓ}(A : ℕ → Set ℓ)(z : A zero)(s : ∀ n → A n → A (suc n))(n : ℕ) → A n
indℕ A z s zero = z
indℕ A z s (suc n) = s n (indℕ A z s n)

zero≠suc : {n : ℕ} → ¬ (zero ≡ suc n)
zero≠suc e = transpP P e triv
  where
    P : ℕ → Prop
    P zero = ⊤
    P (suc _) = ⊥

ass+ : ∀{m n o} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

idr+ : ∀{n} → n + 0 ≡ n
idr+ {zero} = refl
idr+ {suc n} = cong suc (idr+ {n})

+suc : ∀{m n} → m + suc n ≡ suc (m + n)
+suc {zero} = refl
+suc {suc m} = cong suc (+suc {m})

+comm : ∀{m n} → m + n ≡ n + m
+comm {zero} = idr+ ⁻¹
+comm {suc m}{n} = cong suc (+comm {m}{n}) ◾ +suc {n}{m} ⁻¹

-- 𝟚

if_then_else_ : ∀{ℓ}{A : Set ℓ}(t : 𝟚)(u v : A) → A
if tt then u else v = u
if ff then u else v = v

_∨_ : 𝟚 → 𝟚 → 𝟚
a ∨ b = if a then tt else b

_∧_ : 𝟚 → 𝟚 → 𝟚
a ∧ b = if a then b else ff

_⊃_ : 𝟚 → 𝟚 → 𝟚
a ⊃ b = if a then b else tt

tt≠ff : ¬ (tt ≡ ff)
tt≠ff e = transpP P e triv
  where
    P : 𝟚 → Prop
    P tt = ⊤
    P ff = ⊥


-- Sum type

data _⊎_ {ℓ}{ℓ'}(A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

case : ∀ {ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}
       (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (ι₁ t) u v = u t
case (ι₂ t) u v = v t

ind⊎ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(P : A ⊎ B → Set ℓ'') →
       ((a : A) → P (ι₁ a)) → ((b : B) → P (ι₂ b)) → (t : A ⊎ B) → P t
ind⊎ P u v (ι₁ t) = u t
ind⊎ P u v (ι₂ t) = v t

transp⊎ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){a : A}{w : B a ⊎ C a}{a' : A}(e : a ≡ a') →
  transp (λ a → B a ⊎ C a) e w ≡ case w (λ b → ι₁ (transp B e b)) (λ c → ι₂ (transp C e c))
transp⊎ B C {w = ι₁ a} refl = refl
transp⊎ B C {w = ι₂ b} refl = refl

casetransp : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}(B : A → Set ℓ')(C : A → Set ℓ''){D : Set ℓ'''}{a a' : A}(e : a ≡ a')(w : B a ⊎ C a){u : B a' → D}{v : C a' → D} →
  case (transp (λ a → B a ⊎ C a) e w) u v ≡ case w (λ b → u (transp B e b)) (λ c → v (transp C e c))
casetransp B C refl w = refl

transpcase : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}(D : A → Set ℓ'''){a a' : A}(e : a ≡ a')(w : B ⊎ C){u : B → D a}{v : C → D a} →
  transp D e (case w u v) ≡ case w (λ a → transp D e (u a)) (λ b → transp D e (v b))
transpcase D refl e = refl

Dec : ∀{ℓ} → Set ℓ → Set ℓ
Dec A = A ⊎ Lift (A → ⊥)

True : ∀{i}{A : Set i} → Dec A → Set
True (ι₁ _) = Lift ⊤
True (ι₂ _) = Lift ⊥

extract : ∀{i}{A : Set i}(da : Dec A) → {True da} → A
extract (ι₁ a) = a

-- finite types

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

{-# INJECTIVE Fin #-}

module I where
  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
  infixr 5 _⇒_
  infixl 5 _$_
  infixl 7 _+o_

  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty
    _⇒_     : Ty → Ty → Ty

  data Con  : Set where
    ◇       : Con
    _▹_     : Con → Ty → Con

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

    lam       : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_       : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β        : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ id ,o u ]
    ⇒η        : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → lam (t [ p ] $ q) ≡ t
    lam[]     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{γ : Sub Δ Γ} →
                (lam t) [ γ ] ≡ lam (t [ γ ⊚ p ,o q ])
    $[]       : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                (t $ u) [ γ ] ≡ t [ γ ] $ u [ γ ]

  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def t u = u [ id ,o t ]

  v0 : {Γ : Con} → {A : Ty} → Tm (Γ ▹ A) A
  v0 = q
  v1 : {Γ : Con} → {A B : Ty} → Tm (Γ ▹ A ▹ B) A
  v1 = q [ p ]
  v2 : {Γ : Con} → {A B C : Ty} → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = q [ p ⊚ p ]
  v3 : {Γ : Con} → {A B C D : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = q [ p ⊚ p ⊚ p ]

  ,∘ : ∀{Γ Δ Θ A}{γ : Sub Δ Γ}{t : Tm Δ A}{δ : Sub Θ Δ} →
    (γ ,o t) ⊚ δ ≡ γ ⊚ δ ,o t [ δ ]
  ,∘ {Γ}{Δ}{Θ}{A}{γ}{t}{δ} =
    (γ ,o t) ⊚ δ
      ≡⟨ ▹η ⁻¹ ⟩
    (p ⊚ ((γ ,o t) ⊚ δ) ,o q [ (γ ,o t) ⊚ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (ass ⁻¹ ,×= [∘]) ⟩
    ((p ⊚ (γ ,o t)) ⊚ δ ,o q [ γ ,o t ] [ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (cong (_⊚ δ) ▹β₁ ,×= cong (_[ δ ]) ▹β₂) ⟩
    γ ⊚ δ ,o t [ δ ]
      ∎

record Model {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
  infixr 5 _⇒_
  infixl 5 _$_
  infixl 7 _+o_
  
  field
    Con       : Set i
    Sub       : Con → Con → Set j
    _⊚_       : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    ass       : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} →
                (γ ⊚ δ) ⊚ θ ≡ γ ⊚ (δ ⊚ θ)
    id        : ∀{Γ} → Sub Γ Γ
    idl       : ∀{Γ Δ}{γ : Sub Δ Γ} → id ⊚ γ ≡ γ
    idr       : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ⊚ id ≡ γ

    ◇         : Con
    ε         : ∀{Γ} → Sub Γ ◇
    ◇η        : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε

    Ty        : Set k

    Tm        : Con → Ty → Set l
    _[_]      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    [∘]       : ∀{Γ Δ Θ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →
                t [ γ ⊚ δ ] ≡ t [ γ ] [ δ ]
    [id]      : ∀{Γ A}{t : Tm Γ A} → t [ id ] ≡ t
    _▹_       : Con → Ty → Con
    _,o_      : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
    p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
    q         : ∀{Γ A} → Tm (Γ ▹ A) A
    ▹β₁       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → p ⊚ (γ ,o t) ≡ γ
    ▹β₂       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → q [ γ ,o t ] ≡ t
    ▹η        : ∀{Γ Δ A}{γa : Sub Δ (Γ ▹ A)} → p ⊚ γa ,o q [ γa ] ≡ γa

    Bool      : Ty
    true      : ∀{Γ} → Tm Γ Bool
    false     : ∀{Γ} → Tm Γ Bool
    ite       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    iteβ₁     : ∀{Γ A u v} → ite {Γ}{A} true u v ≡ u
    iteβ₂     : ∀{Γ A u v} → ite {Γ}{A} false u v ≡ v
    true[]    : ∀{Γ Δ}{γ : Sub Δ Γ} → true [ γ ] ≡ true
    false[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → false [ γ ] ≡ false
    ite[]     : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} → (ite {Γ}{A} t u v) [ γ ] ≡ ite (t [ γ ]) (u [ γ ]) (v [ γ ])

    Nat       : Ty
    num       : ∀{Γ} → ℕ → Tm Γ Nat
    isZero    : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
    _+o_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
    isZeroβ₁  : ∀{Γ} → isZero (num {Γ} 0) ≡ true
    isZeroβ₂  : ∀{Γ n} → isZero (num {Γ} (1 + n)) ≡ false
    +β        : ∀{Γ m n} → num {Γ} m +o num n ≡ num (m + n)
    num[]     : ∀{Γ n Δ}{γ : Sub Δ Γ} → num n [ γ ] ≡ num n
    isZero[]  : ∀{Γ t Δ}{γ : Sub Δ Γ} → isZero t [ γ ] ≡ isZero (t [ γ ])
    +[]       : ∀{Γ u v Δ}{γ : Sub Δ Γ} → (u +o v) [ γ ] ≡ (u [ γ ]) +o (v [ γ ])
    
    _⇒_       : Ty → Ty → Ty
    lam       : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_       : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β        : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ id ,o u ]
    ⇒η        : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → lam (t [ p ] $ q) ≡ t
    lam[]     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{γ : Sub Δ Γ} →
                (lam t) [ γ ] ≡ lam (t [ γ ⊚ p ,o q ])
    $[]       : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                (t $ u) [ γ ] ≡ t [ γ ] $ u [ γ ]
                
  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def t u = u [ id ,o t ]
  v0 : ∀{Γ A}        → Tm (Γ ▹ A) A
  v0 = q
  v1 : ∀{Γ A B}      → Tm (Γ ▹ A ▹ B) A
  v1 = q [ p ]
  v2 : ∀{Γ A B C}    → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = q [ p ⊚ p ]
  v3 : ∀{Γ A B C D}  → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = q [ p ⊚ p ⊚ p ]
  ▹η' : ∀{Γ A} → p ,o q ≡ id {Γ ▹ A}
  ▹η' {Γ}{A} =
    p ,o q
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (idr ,×= [id]) ⁻¹ ⟩
    p ⊚ id ,o q [ id ]
      ≡⟨ ▹η ⟩
    id
      ∎

  ,∘ : ∀{Γ Δ Θ A}{γ : Sub Δ Γ}{t : Tm Δ A}{δ : Sub Θ Δ} →
    (γ ,o t) ⊚ δ ≡ γ ⊚ δ ,o t [ δ ]
  ,∘ {Γ}{Δ}{Θ}{A}{γ}{t}{δ} =
    (γ ,o t) ⊚ δ
      ≡⟨ ▹η ⁻¹ ⟩
    (p ⊚ ((γ ,o t) ⊚ δ) ,o q [ (γ ,o t) ⊚ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (ass ⁻¹ ,×= [∘]) ⟩
    ((p ⊚ (γ ,o t)) ⊚ δ ,o q [ γ ,o t ] [ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w)
           (cong (_⊚ δ) ▹β₁ ,×= cong (_[ δ ]) ▹β₂) ⟩
    γ ⊚ δ ,o t [ δ ]
      ∎

  ^∘ : ∀{Γ Δ}{γ : Sub Δ Γ}{A}{Θ}{δ : Sub Θ Δ}{t : Tm Θ A} →
    (γ ⊚ p ,o q) ⊚ (δ ,o t) ≡ (γ ⊚ δ ,o t)
  ^∘ {Γ}{Δ}{γ}{A}{Θ}{δ}{t} =
    (γ ⊚ p ,o q) ⊚ (δ ,o t)
      ≡⟨ ,∘ ⟩
    (γ ⊚ p ⊚ (δ ,o t) ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → (x ,o q [ δ ,o t ])) ass ⟩
    (γ ⊚ (p ⊚ (δ ,o t)) ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → (γ ⊚ x ,o q [ δ ,o t ])) ▹β₁ ⟩
    (γ ⊚ δ ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → γ ⊚ δ ,o x) ▹β₂ ⟩
    (γ ⊚ δ ,o t)
      ∎

  ⟦_⟧T : I.Ty → Ty
  ⟦ I.Nat ⟧T = Nat
  ⟦ I.Bool ⟧T = Bool
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T

  ⟦_⟧C : I.Con → Con
  ⟦ I.◇ ⟧C = ◇
  ⟦ Γ I.▹ A ⟧C = ⟦ Γ ⟧C ▹ ⟦ A ⟧T

  postulate
    ⟦_⟧S      : ∀{Γ Δ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
    ⟦_⟧t      : ∀{Γ A} → I.Tm  Γ A → Tm  ⟦ Γ ⟧C ⟦ A ⟧T
    ⟦∘⟧       : ∀{Γ Δ Θ}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ} →
                         ⟦ γ I.⊚ δ ⟧S     ≈ ⟦ γ ⟧S ⊚ ⟦ δ ⟧S
    ⟦id⟧      : ∀{Γ} →   ⟦ I.id {Γ} ⟧S    ≈ id
    ⟦ε⟧       : ∀{Γ} →   ⟦ I.ε {Γ} ⟧S     ≈ ε
    ⟦[]⟧      : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Γ A} →
                         ⟦ t I.[ γ ] ⟧t   ≈ ⟦ t ⟧t [ ⟦ γ ⟧S ]
    ⟦,⟧       : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A} →
                         ⟦ γ I.,o t ⟧S    ≈ ⟦ γ ⟧S ,o ⟦ t ⟧t
    ⟦p⟧       : ∀{Γ A} → ⟦ I.p {Γ} {A} ⟧S ≈ p
    ⟦q⟧       : ∀{Γ A} → ⟦ I.q {Γ} {A} ⟧t ≈ q
    {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]⟧ ⟦,⟧ ⟦p⟧ ⟦q⟧ #-}

    ⟦true⟧    : ∀{Γ} →   ⟦ I.true {Γ} ⟧t  ≈ true
    ⟦false⟧   : ∀{Γ} →   ⟦ I.false {Γ} ⟧t ≈ false
    ⟦ite⟧     : ∀{Γ A}{t : I.Tm Γ I.Bool}{u v : I.Tm Γ A} →
                         ⟦ I.ite t u v ⟧t ≈ ite ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ #-}

    ⟦num⟧     : ∀{Γ n} → ⟦ I.num {Γ} n ⟧t ≈ num n
    ⟦isZero⟧  : ∀{Γ}{t : I.Tm Γ I.Nat} →
                         ⟦ I.isZero t ⟧t  ≈ isZero ⟦ t ⟧t
    ⟦+⟧       : ∀{Γ}{u v : I.Tm Γ I.Nat} → 
                         ⟦ u I.+o v ⟧t    ≈ ⟦ u ⟧t +o ⟦ v ⟧t
    {-# REWRITE ⟦num⟧ ⟦isZero⟧ ⟦+⟧ #-}

    ⟦lam⟧     : ∀{Γ A B}{t : I.Tm (Γ I.▹ A) B} →
                         ⟦ I.lam t ⟧t    ≈ lam ⟦ t ⟧t
    ⟦$⟧       : ∀{Γ A B}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A} →
                         ⟦ t I.$ u ⟧t     ≈ ⟦ t ⟧t $ ⟦ u ⟧t
    {-# REWRITE ⟦lam⟧ ⟦$⟧ #-}

record DepModel {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚∙_
  infixl 6 _[_]∙
  infixl 5 _▹∙_
  infixl 5 _,o∙_
  infixr 5 _⇒∙_
  infixl 5 _$∙_
  infixl 7 _+o∙_

  field
    Con∙       : I.Con → Set i
    Sub∙       : ∀{Δ} → Con∙ Δ → ∀{Γ} → Con∙ Γ → I.Sub Δ Γ → Set j
    _⊚∙_       : ∀{Γ Δ Θ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ} → 
                 Sub∙ Δ∙ Γ∙ γ → Sub∙ Θ∙ Δ∙ δ → Sub∙ Θ∙ Γ∙ (γ I.⊚ δ)
    ass∙       : ∀{Γ Δ Θ Ξ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{Ξ∙ : Con∙ Ξ}
                 {γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ}{θ : I.Sub Ξ Θ}
                 {γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}{θ∙ : Sub∙ Ξ∙ Θ∙ θ} →
                 (Sub∙ Ξ∙ Γ∙ ~) I.ass ((γ∙ ⊚∙ δ∙) ⊚∙ θ∙) (γ∙ ⊚∙ (δ∙ ⊚∙ θ∙))
    id∙        : ∀{Γ}{Γ∙ : Con∙ Γ} → Sub∙ Γ∙ Γ∙ (I.id {Γ})
    idl∙       : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Sub∙ Δ∙ Γ∙ ~) I.idl (id∙ ⊚∙ γ∙) γ∙
    idr∙       : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Sub∙ Δ∙ Γ∙ ~) I.idr (γ∙ ⊚∙ id∙) γ∙

    ◇∙         : Con∙ I.◇
    ε∙         : ∀{Γ}{Γ∙ : Con∙ Γ} → Sub∙ Γ∙ ◇∙ (I.ε {Γ})
    ◇η∙        : ∀{Γ}{Γ∙ : Con∙ Γ}{σ : I.Sub Γ I.◇}{σ∙ : Sub∙ Γ∙ ◇∙ σ} → (Sub∙ Γ∙ ◇∙ ~) I.◇η σ∙ ε∙

    Ty∙        : I.Ty → Set k

    Tm∙        : ∀{Γ} → Con∙ Γ → ∀{A} → Ty∙ A → I.Tm Γ A → Set l
    _[_]∙      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{γ : I.Sub Δ Γ} → Tm∙ Γ∙ A∙ t → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ (t I.[ γ ])
    [∘]∙       : ∀{Γ Δ Θ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ}
                 {t∙ : Tm∙ Γ∙ A∙ t}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ} →
                (Tm∙ Θ∙ A∙ ~) I.[∘] (t∙ [ γ∙ ⊚∙ δ∙ ]∙) (t∙ [ γ∙ ]∙ [ δ∙ ]∙)
    [id]∙      : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{t∙ : Tm∙ Γ∙ A∙ t} → (Tm∙ Γ∙ A∙ ~) I.[id] (t∙ [ id∙ ]∙) t∙
    _▹∙_       : ∀{Γ A} → Con∙ Γ → Ty∙ A → Con∙ (Γ I.▹ A)
    _,o∙_      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t : I.Tm Δ A}{γ : I.Sub Δ Γ} → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ t → Sub∙ Δ∙ (Γ∙ ▹∙ A∙) (γ I.,o t)
    p∙         : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ (I.p {Γ}{A})
    q∙         : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Tm∙ (Γ∙ ▹∙ A∙) A∙ (I.q {Γ}{A})
    ▹β₁∙       : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Δ∙ A∙ t} → 
                (Sub∙ Δ∙ Γ∙ ~) I.▹β₁ (p∙ ⊚∙ (γ∙ ,o∙ t∙)) γ∙
    ▹β₂∙       : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Δ∙ A∙ t} →
                (Tm∙ Δ∙ A∙ ~) I.▹β₂ (q∙ [ γ∙ ,o∙ t∙ ]∙) t∙
    ▹η∙        : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γa : I.Sub Δ (Γ I.▹ A)}{γa∙ : Sub∙ Δ∙ {Γ I.▹ A} (Γ∙ ▹∙ A∙) γa} →
                (Sub∙ Δ∙ (Γ∙ ▹∙ A∙) ~) I.▹η (p∙ ⊚∙ γa∙ ,o∙ q∙ [ γa∙ ]∙) γa∙

    Bool∙      : Ty∙ I.Bool
    true∙      : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ (I.true {Γ})
    false∙     : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ (I.false {Γ})
    ite∙       : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : I.Tm Γ I.Bool}{u v : I.Tm Γ A} → Tm∙ Γ∙ Bool∙ t → Tm∙ Γ∙ A∙ u → Tm∙ Γ∙ A∙ v → Tm∙ Γ∙ A∙ (I.ite t u v)
    iteβ₁∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u v : I.Tm Γ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} → 
                (Tm∙ Γ∙ A∙ ~) I.iteβ₁ (ite∙ true∙ u∙ v∙) u∙
    iteβ₂∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u v : I.Tm Γ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} →
                (Tm∙ Γ∙ A∙ ~) I.iteβ₂ (ite∙ false∙ u∙ v∙) v∙
    true[]∙    : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Tm∙ Δ∙ Bool∙ ~) I.true[] (true∙ [ γ∙ ]∙) true∙
    false[]∙   : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Tm∙ Δ∙ Bool∙ ~) I.false[] (false∙ [ γ∙ ]∙) false∙
    ite[]∙     : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : I.Tm Γ I.Bool}{u v : I.Tm Γ A}{t∙ : Tm∙ Γ∙ Bool∙ t}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v}
                {Δ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ A∙ ~) I.ite[] ((ite∙ t∙ u∙ v∙) [ γ∙ ]∙) (ite∙ (t∙ [ γ∙ ]∙) (u∙ [ γ∙ ]∙) (v∙ [ γ∙ ]∙))

    Nat∙       : Ty∙ I.Nat
    num∙       : ∀{Γ}{Γ∙ : Con∙ Γ}(n : ℕ) → Tm∙ Γ∙ Nat∙ (I.num {Γ} n)
    isZero∙    : ∀{Γ}{Γ∙ : Con∙ Γ}{t : I.Tm Γ I.Nat} → Tm∙ Γ∙ Nat∙ t → Tm∙ Γ∙ Bool∙ (I.isZero t)
    _+o∙_      : ∀{Γ}{Γ∙ : Con∙ Γ}{u v : I.Tm Γ I.Nat} → Tm∙ Γ∙ Nat∙ u → Tm∙ Γ∙ Nat∙ v → Tm∙ Γ∙ Nat∙ (u I.+o v)
    isZeroβ₁∙  : ∀{Γ}{Γ∙ : Con∙ Γ} → (Tm∙ Γ∙ Bool∙ ~) I.isZeroβ₁ (isZero∙ (num∙ {Γ}{Γ∙} 0)) true∙
    isZeroβ₂∙  : ∀{Γ n}{Γ∙ : Con∙ Γ} → (Tm∙ Γ∙ Bool∙ ~) I.isZeroβ₂ (isZero∙ (num∙ {Γ}{Γ∙} (1 + n))) false∙
    +β∙        : ∀{Γ m n}{Γ∙ : Con∙ Γ} → (Tm∙ Γ∙ Nat∙ ~) I.+β (num∙ {Γ}{Γ∙} m +o∙ num∙ n) (num∙ (m + n))
    num[]∙     : ∀{Γ n Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → (Tm∙ Δ∙ Nat∙ ~) I.num[] (num∙ n [ γ∙ ]∙) (num∙ n)
    isZero[]∙  : ∀{Γ}{Γ∙ : Con∙ Γ}{t : I.Tm Γ I.Nat}{t∙ : Tm∙ Γ∙ Nat∙ t}{Δ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ Bool∙ ~) I.isZero[] (isZero∙ t∙ [ γ∙ ]∙) (isZero∙ (t∙ [ γ∙ ]∙))
    +[]∙       : ∀{Γ}{Γ∙ : Con∙ Γ}{u v : I.Tm Γ I.Nat}{u∙ : Tm∙ Γ∙ Nat∙ u}{v∙ : Tm∙ Γ∙ Nat∙ v}{Δ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ Nat∙ ~) I.+[] ((u∙ +o∙ v∙) [ γ∙ ]∙) ((u∙ [ γ∙ ]∙) +o∙ (v∙ [ γ∙ ]∙))

    _⇒∙_       : ∀{A B} → Ty∙ A → Ty∙ B → Ty∙ (A I.⇒ B)
    lam∙       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm (Γ I.▹ A) B} →
                  Tm∙ {Γ I.▹ A} (Γ∙ ▹∙ A∙) B∙ t → Tm∙ Γ∙ (A∙ ⇒∙ B∙) (I.lam t)
    _$∙_       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A} →
                  Tm∙ {Γ} Γ∙ {A I.⇒ B} (A∙ ⇒∙ B∙) t → Tm∙ Γ∙ A∙ u → Tm∙ Γ∙ B∙ (t I.$ u)
    ⇒β∙        : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm (Γ I.▹ A) B}{u : I.Tm Γ A}{t∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ t}{u∙ : Tm∙ Γ∙ A∙ u} →
                  (Tm∙ Γ∙ B∙ ~) I.⇒β (lam∙ t∙ $∙ u∙) (t∙ [ id∙ ,o∙ u∙ ]∙)
    ⇒η∙        : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm Γ (A I.⇒ B)}{t∙ : Tm∙ Γ∙ {A I.⇒ B} (A∙ ⇒∙ B∙) t} →
                  (Tm∙ Γ∙ (A∙ ⇒∙ B∙) ~) I.⇒η (lam∙ (t∙ [ p∙ ]∙ $∙ q∙)) t∙
    lam[]∙     : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm (Γ I.▹ A) B}{t∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ t}
                {Δ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ (A∙ ⇒∙ B∙) ~) I.lam[] ((lam∙ t∙) [ γ∙ ]∙) (lam∙ (t∙ [ γ∙ ⊚∙ p∙ ,o∙ q∙ ]∙))
    $[]∙       : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A}{t∙ : Tm∙ Γ∙ {A I.⇒ B} (A∙ ⇒∙ B∙) t}{u∙ : Tm∙ Γ∙ A∙ u}
                {Δ}{Δ∙ : Con∙ Δ}{γ : I.Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} →
                (Tm∙ Δ∙ B∙ ~) I.$[] ((t∙ $∙ u∙) [ γ∙ ]∙) (t∙ [ γ∙ ]∙ $∙ u∙ [ γ∙ ]∙)

  ⟦_⟧T : (A : I.Ty) → Ty∙ A
  ⟦ I.Nat ⟧T = Nat∙
  ⟦ I.Bool ⟧T = Bool∙
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒∙ ⟦ B ⟧T

  ⟦_⟧C : (Γ : I.Con) → Con∙ Γ
  ⟦ I.◇ ⟧C = ◇∙
  ⟦ Γ I.▹ A ⟧C = ⟦ Γ ⟧C ▹∙ ⟦ A ⟧T

  postulate
    ⟦_⟧S      : ∀{Γ Δ}(γ : I.Sub Δ Γ) → Sub∙ ⟦ Δ ⟧C  ⟦ Γ ⟧C  γ
    ⟦_⟧t      : ∀{Γ A}(t : I.Tm Γ A)  → Tm∙  ⟦ Γ ⟧C  ⟦ A ⟧T  t
    ⟦∘⟧       : ∀{Γ Δ Θ}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ} → 
                         ⟦ γ I.⊚ δ ⟧S     ≈ ⟦ γ ⟧S ⊚∙ ⟦ δ ⟧S
    ⟦id⟧      : ∀{Γ} →   ⟦ I.id {Γ} ⟧S    ≈ id∙
    ⟦ε⟧       : ∀{Γ} →   ⟦ I.ε {Γ} ⟧S     ≈ ε∙
    ⟦[]⟧      : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Γ A} →
                         ⟦ t I.[ γ ] ⟧t   ≈ ⟦ t ⟧t [ ⟦ γ ⟧S ]∙
    ⟦,⟧       : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A} →
                         ⟦ γ I.,o t ⟧S    ≈ ⟦ γ ⟧S ,o∙ ⟦ t ⟧t
    ⟦p⟧       : ∀{Γ A} → ⟦ I.p {Γ}{A} ⟧S  ≈ p∙
    ⟦q⟧       : ∀{Γ A} → ⟦ I.q {Γ}{A} ⟧t  ≈ q∙
    {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]⟧ ⟦,⟧ ⟦p⟧ ⟦q⟧ #-}

    ⟦true⟧    : ∀{Γ} →   ⟦ I.true {Γ} ⟧t  ≈ true∙
    ⟦false⟧   : ∀{Γ} →   ⟦ I.false {Γ} ⟧t ≈ false∙
    ⟦ite⟧     : ∀{Γ A}{t : I.Tm Γ I.Bool}{u v : I.Tm Γ A} →
                         ⟦ I.ite t u v ⟧t ≈ ite∙ ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ #-}

    ⟦num⟧     : ∀{Γ n} → ⟦ I.num {Γ} n ⟧t ≈ num∙ n
    ⟦isZero⟧  : ∀{Γ}{t : I.Tm Γ I.Nat} →
                         ⟦ I.isZero t ⟧t  ≈ isZero∙ ⟦ t ⟧t
    ⟦+⟧       : ∀{Γ}{u v : I.Tm Γ I.Nat} →
                         ⟦ u I.+o v ⟧t    ≈ ⟦ u ⟧t +o∙ ⟦ v ⟧t
    {-# REWRITE ⟦num⟧ ⟦isZero⟧ ⟦+⟧ #-}

    ⟦lam⟧     : ∀{Γ A B}{t : I.Tm (Γ I.▹ A) B} →
                         ⟦ I.lam t ⟧t     ≈ lam∙ ⟦ t ⟧t
    ⟦$⟧       : ∀{Γ A B}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A} →
                         ⟦ t I.$ u ⟧t     ≈ ⟦ t ⟧t $∙ ⟦ u ⟧t
    {-# REWRITE ⟦lam⟧ ⟦$⟧ #-}

module ⇒vs→ {i j k l}(M : Model {i}{j}{k}{l})(A B : Model.Ty M) where
  open Model M
  EXT = Σsp (∀ Γ → Tm Γ A → Tm Γ B) λ f → ∀{Γ Δ γ a} → f Γ a [ γ ] ≡ f Δ (a [ γ ])
  INT = Tm ◇ (A ⇒ B)
  toINT : EXT → INT
  toINT f = lam (π₁ f (◇ ▹ A) q)
  toEXT : INT → EXT
  toEXT t = (λ Γ a → t [ ε ] $ a) , λ {Γ}{Δ}{γ}{a} → 
    (t [ ε ] $ a) [ γ ]
                             ≡⟨ $[] ⟩
    t [ ε ] [ γ ] $ a [ γ ]
                             ≡⟨ cong (_$ a [ γ ]) ([∘] ⁻¹) ⟩
    t [ ε ⊚ γ ] $ a [ γ ]
                             ≡⟨ cong (λ x → t [ x ] $ a [ γ ]) ◇η ⟩
    t [ ε ] $ a [ γ ]
                             ∎
  extRoundtrip : (f : EXT) → toEXT (toINT f) ≡ f
  extRoundtrip f = (funext λ Γ → funext λ a →
    lam (π₁ f (◇ ▹ A) q) [ ε ] $ a
                                                  ≡⟨ cong (_$ a) lam[] ⟩
    lam (π₁ f (◇ ▹ A) q [ ε ⊚ p ,o q ]) $ a
                                                  ≡⟨ cong (λ x → lam x $ a) (π₂ f) ⟩
    lam (π₁ f (Γ ▹ A) (q [ ε ⊚ p ,o q ])) $ a
                                                  ≡⟨ cong (λ x → lam (π₁ f (Γ ▹ A) x) $ a) ▹β₂ ⟩
    lam (π₁ f (Γ ▹ A) q) $ a
                                                  ≡⟨ ⇒β ⟩
    π₁ f (Γ ▹ A) q [ id ,o a ]
                                                  ≡⟨ π₂ f ⟩
    π₁ f Γ (q [ id ,o a ])
                                                  ≡⟨ cong (π₁ f Γ) ▹β₂ ⟩
    π₁ f Γ a
                                                  ∎) ,=-
  intRoundtrip : (t : INT) → toINT (toEXT t) ≡ t
  intRoundtrip t = cong (λ γ → lam (t [ γ ] $ q)) (◇η ⁻¹) ◾ ⇒η

St : Model
St = record
  { Con       = Set
  ; Sub       = λ Δ Γ → Δ → Γ
  ; _⊚_       = λ γ δ θ* → γ (δ θ*)
  ; ass       = λ {Γ}{Δ}{Θ}{Ξ} → refl {A = Ξ → Γ}
  ; id        = λ γ* → γ*
  ; idl       = λ {Γ}{Δ} → refl {A = Δ → Γ}
  ; idr       = λ {Γ}{Δ} → refl {A = Δ → Γ}
  
  ; ◇         = Lift ⊤
  ; ε         = _
  ; ◇η        = λ {Γ}{σ} → refl {A = Γ → Lift ⊤}
  
  ; Ty        = Set
  
  ; Tm        = λ Γ A → Γ → A
  ; _[_]      = λ a γ δ* → a (γ δ*) 
  ; [∘]       = λ {Γ}{Δ}{Θ}{A} → refl {A = Θ → A}
  ; [id]      = λ {Γ}{A}{a} → refl {A = Γ → A}
  ; _▹_       = _×_
  ; _,o_      = λ γ t δ* → γ δ* , t δ*
  ; p         = π₁
  ; q         = π₂
  ; ▹β₁       = λ {Γ}{Δ} → refl {A = Δ → Γ}
  ; ▹β₂       = λ {Γ}{Δ}{A} → refl {A = Δ → A}
  ; ▹η        = λ {Γ}{Δ}{A} → refl {A = Δ → Γ × A}

  ; Bool      = 𝟚
  ; true      = λ _ → tt
  ; false     = λ _ → ff
  ; ite       = λ t u v γ* → if t γ* then u γ* else v γ*
  ; iteβ₁     = refl
  ; iteβ₂     = refl
  ; true[]    = refl
  ; false[]   = refl
  ; ite[]     = refl

  ; Nat       = ℕ
  ; num       = λ n γ* → n
  ; isZero    = λ t γ* → iteℕ tt (λ _ → ff) (t γ*)
  ; _+o_      = λ m n γ* → m γ* + n γ*
  ; isZeroβ₁  = refl
  ; isZeroβ₂  = refl
  ; +β        = refl
  ; num[]     = refl
  ; isZero[]  = refl
  ; +[]       = refl
  
  ; _⇒_       = λ A B → A → B
  ; lam       = λ t γ* α* → t (γ* , α*)
  ; _$_       = λ t u γ* → t γ* (u γ*)
  ; ⇒β        = refl
  ; ⇒η        = refl
  ; lam[]     = refl
  ; $[]       = refl
  }
module St = Model St

open I public

data Var : Con → Ty → Set where
  vz : ∀{Γ A} → Var (Γ ▹ A) A
  vs : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

data Ne (Γ : Con) : Ty → Set
data Nf (Γ : Con) : Ty → Set

data Ne Γ where
  var       : ∀{A} → Var Γ A → Ne Γ A
  _$Ne_     : ∀{A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  iteNe     : ∀{A} → Ne Γ Bool → Nf Γ A → Nf Γ A → Ne Γ A
  isZeroNe  : Ne Γ Nat → Ne Γ Bool
  _+NeNe_   : Ne Γ Nat → Ne Γ Nat → Ne Γ Nat
  _+NeNf_   : Ne Γ Nat → ℕ → Ne Γ Nat
  _+NfNe_   : ℕ → Ne Γ Nat → Ne Γ Nat
  
data Nf Γ where
  neuBool   : Ne Γ Bool → Nf Γ Bool
  neuNat    : Ne Γ Nat → Nf Γ Nat
  lamNf     : ∀{A B} → Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  trueNf    : Nf Γ Bool
  falseNf   : Nf Γ Bool
  numNf     : (n : ℕ) → Nf Γ Nat

⌜_⌝V : ∀{Γ A} → Var Γ A → Tm Γ A
⌜ vz ⌝V = q
⌜ vs x ⌝V = ⌜ x ⌝V [ p ]
⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
⌜ var x ⌝Ne = ⌜ x ⌝V
⌜ t $Ne a ⌝Ne = ⌜ t ⌝Ne $ ⌜ a ⌝Nf
⌜ iteNe t a a' ⌝Ne = ite ⌜ t ⌝Ne ⌜ a ⌝Nf ⌜ a' ⌝Nf
⌜ isZeroNe t ⌝Ne = isZero ⌜ t ⌝Ne
⌜ t +NeNe t' ⌝Ne = ⌜ t ⌝Ne +o ⌜ t' ⌝Ne
⌜ t +NeNf n' ⌝Ne = ⌜ t ⌝Ne +o num n'
⌜ n +NfNe t' ⌝Ne = num n +o ⌜ t' ⌝Ne
⌜ neuBool t ⌝Nf = ⌜ t ⌝Ne
⌜ neuNat t ⌝Nf = ⌜ t ⌝Ne
⌜ lamNf t ⌝Nf = lam ⌜ t ⌝Nf
⌜ trueNf ⌝Nf = true
⌜ falseNf ⌝Nf = false
⌜ numNf n ⌝Nf = num n

