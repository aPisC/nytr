{-# OPTIONS --prop --rewriting #-}

module hf06import where

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
    isZero[]  : ∀{Γ t Δ}{γ : Sub Δ Γ} → (isZero t) [ γ ] ≡ isZero (t [ γ ])
    +[]       : ∀{Γ u v Δ}{γ : Sub Δ Γ} → (u +o v) [ γ ] ≡ (u [ γ ]) +o (v [ γ ])

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
  v4 : {Γ : Con} → {A B C D E : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) A
  v4 = q [ p ⊚ p ⊚ p ⊚ p ]
  v5 : {Γ : Con} → {A B C D E F : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F) A
  v5 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v6 : {Γ : Con} → {A B C D E F G : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G) A
  v6 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v7 : {Γ : Con} → {A B C D E F G H : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G ▹ H) A
  v7 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]

  ,∘ : ∀{Γ Δ Θ A}{γ : Sub Δ Γ}{t : Tm Δ A}{δ : Sub Θ Δ} →
    (γ ,o t) ⊚ δ ≡ γ ⊚ δ ,o t [ δ ]
  ,∘ {Γ}{Δ}{Θ}{A}{γ}{t}{δ} =
    (γ ,o t) ⊚ δ
      ≡⟨  ▹η ⁻¹ ⟩
    (p ⊚ ((γ ,o t) ⊚ δ) ,o q [ (γ ,o t) ⊚ δ ])
      ≡⟨ cong {A = Sub Θ Γ × Tm Θ A} (λ w → π₁ w ,o π₂ w) (ass ⁻¹ ,×= [∘]) ⟩
    ((p ⊚ (γ ,o t)) ⊚ δ ,o q [ γ ,o t ] [ δ ])
      ≡⟨ cong {A = Sub Θ Γ × Tm Θ A} (λ w → π₁ w ,o π₂ w)
           (cong (_⊚ δ) ▹β₁ ,×= cong (_[ δ ]) ▹β₂) ⟩
    γ ⊚ δ ,o t [ δ ]
      ∎

record DepModel {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚∙_
  infixl 6 _[_]∙
  infixl 5 _▹∙_
  infixl 5 _,o∙_

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

    Tm∙        : ∀{Γ A} → Con∙ Γ → Ty∙ A → I.Tm Γ A → Set l
    _[_]∙      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{γ : I.Sub Δ Γ} → Tm∙ Γ∙ A∙ t → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ (t I.[ γ ])
    [∘]∙       : ∀{Γ Δ Θ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ}
                 {t∙ : Tm∙ Γ∙ A∙ t}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ} →
                (Tm∙ Θ∙ A∙ ~) I.[∘] (t∙ [ γ∙ ⊚∙ δ∙ ]∙) (t∙ [ γ∙ ]∙ [ δ∙ ]∙)
    [id]∙      : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t : I.Tm Γ A}{t∙ : Tm∙ Γ∙ A∙ t} → (Tm∙ Γ∙ A∙ ~) I.[id] (t∙ [ id∙ ]∙) t∙
    _▹∙_       : ∀{Γ A} → Con∙ Γ → Ty∙ A → Con∙ (Γ I.▹ A)
    _,o∙_      : ∀{Γ Δ A}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A} → Sub∙ Δ∙ Γ∙ γ → Tm∙ Δ∙ A∙ t → Sub∙ Δ∙ (Γ∙ ▹∙ A∙) (γ I.,o t)
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

  ⟦_⟧T : (A : I.Ty) → Ty∙ A
  ⟦ I.Nat ⟧T = Nat∙
  ⟦ I.Bool ⟧T = Bool∙

  ⟦_⟧C : (Γ : I.Con) → Con∙ Γ
  ⟦ I.◇ ⟧C = ◇∙
  ⟦ Γ I.▹ A ⟧C = ⟦ Γ ⟧C ▹∙ ⟦ A ⟧T

  postulate
    ⟦_⟧s      : ∀{Γ Δ}(γ : I.Sub Δ Γ) → Sub∙ ⟦ Δ ⟧C  ⟦ Γ ⟧C  γ
    ⟦_⟧t      : ∀{Γ A}(t : I.Tm Γ A)  → Tm∙  ⟦ Γ ⟧C  ⟦ A ⟧T  t
    ⟦∘⟧       : ∀{Γ Δ Θ}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ} → 
                         ⟦ γ I.⊚ δ ⟧s     ≈ ⟦ γ ⟧s ⊚∙ ⟦ δ ⟧s
    ⟦id⟧      : ∀{Γ} →   ⟦ I.id {Γ} ⟧s    ≈ id∙
    ⟦ε⟧       : ∀{Γ} →   ⟦ I.ε {Γ} ⟧s     ≈ ε∙
    ⟦[]⟧      : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Γ A} →
                         ⟦ t I.[ γ ] ⟧t   ≈ ⟦ t ⟧t [ ⟦ γ ⟧s ]∙
    ⟦,⟧       : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A} →
                         ⟦ γ I.,o t ⟧s    ≈ ⟦ γ ⟧s ,o∙ ⟦ t ⟧t
    ⟦p⟧       : ∀{Γ A} → ⟦ I.p {Γ}{A} ⟧s  ≈ p∙
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
record Model {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
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
  v4 : {Γ : Con} → {A B C D E : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) A
  v4 = q [ p ⊚ p ⊚ p ⊚ p ]
  v5 : {Γ : Con} → {A B C D E F : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F) A
  v5 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v6 : {Γ : Con} → {A B C D E F G : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G) A
  v6 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  v7 : {Γ : Con} → {A B C D E F G H : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E ▹ F ▹ G ▹ H) A
  v7 = q [ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ⊚ p ]
  ▹η' : ∀{Γ A} → p ,o q ≡ id {Γ ▹ A}
  ▹η' {Γ}{A} =
    p ,o q
      ≡⟨ cong {A = Sub (Γ ▹ A) Γ × Tm (Γ ▹ A) A} (λ w → π₁ w ,o π₂ w) (idr ,×= [id]) ⁻¹ ⟩
    p ⊚ id ,o q [ id ]
      ≡⟨ ▹η ⟩
    id
      ∎

  ,∘ : ∀{Γ Δ Θ A}{γ : Sub Δ Γ}{t : Tm Δ A}{δ : Sub Θ Δ} →
    (γ ,o t) ⊚ δ ≡ γ ⊚ δ ,o t [ δ ]
  ,∘ {Γ}{Δ}{Θ}{A}{γ}{t}{δ} =
    (γ ,o t) ⊚ δ
      ≡⟨  ▹η ⁻¹ ⟩
    (p ⊚ ((γ ,o t) ⊚ δ) ,o q [ (γ ,o t) ⊚ δ ])
      ≡⟨ cong {A = Sub Θ Γ × Tm Θ A} (λ w → π₁ w ,o π₂ w) (ass ⁻¹ ,×= [∘]) ⟩
    ((p ⊚ (γ ,o t)) ⊚ δ ,o q [ γ ,o t ] [ δ ])
      ≡⟨ cong {A = Sub Θ Γ × Tm Θ A} (λ w → π₁ w ,o π₂ w)
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
  D : DepModel
  D = record
    { Con∙ = λ _ → Con
    ; Sub∙ = λ Δ Γ _ → Sub Δ Γ
    ; _⊚∙_ = _⊚_
    ; ass∙ = λ where {γ = γ}{δ = δ}{θ = θ} → transpconst {B = Sub _ _}{e = I.ass {γ = γ}{δ = δ}{θ = θ}} ◾ ass
    ; id∙ = id
    ; idl∙ = λ where {γ = γ} → transpconst {B = Sub _ _}{e = I.idl {γ = γ}} ◾ idl
    ; idr∙ = λ where {γ = γ} → transpconst {B = Sub _ _}{e = I.idr {γ = γ}} ◾ idr
    ; ◇∙ = ◇
    ; ε∙ = ε
    ; ◇η∙ = λ where {σ = σ} → transpconst {B = Sub _ _}{e = I.◇η {σ = σ}} ◾ ◇η
    ; Ty∙ = λ _ → Ty
    ; Tm∙ = λ Γ A _ → Tm Γ A
    ; _[_]∙ = _[_]
    ; [∘]∙ = λ where {t = t}{γ}{δ} → transpconst {B = Tm _ _}{e = I.[∘] {t = t}{γ}{δ}} ◾ [∘]
    ; [id]∙ = λ where{t = t} → transpconst {B = Tm _ _}{e = I.[id] {t = t}} ◾ [id]
    ; _▹∙_ = _▹_
    ; _,o∙_ = _,o_
    ; p∙ = p
    ; q∙ = q
    ; ▹β₁∙ = λ where {γ = γ}{t} → transpconst {B = Sub _ _}{e = I.▹β₁ {γ = γ}{t}} ◾ ▹β₁
    ; ▹β₂∙ = λ where {γ = γ}{t} → transpconst {B = Tm _ _}{e = I.▹β₂ {γ = γ}{t}} ◾ ▹β₂
    ; ▹η∙ = λ where {γa = γa} → transpconst {B = Sub _ _}{e = I.▹η {γa = γa}} ◾ ▹η
    ; Bool∙ = Bool
    ; true∙ = true
    ; false∙ = false
    ; ite∙ = ite
    ; iteβ₁∙ = λ where {u = u}{v} → transpconst {B = Tm _ _}{e = I.iteβ₁ {u = u}{v = v}} ◾ iteβ₁
    ; iteβ₂∙ = λ where {u = u}{v} → transpconst {B = Tm _ _}{e = I.iteβ₂ {u = u}{v = v}} ◾ iteβ₂
    ; true[]∙ = transpconst {B = Tm _ _}{e = I.true[]} ◾ true[]
    ; false[]∙ = transpconst {B = Tm _ _}{e = I.false[]} ◾ false[]
    ; ite[]∙ = transpconst {B = Tm _ _}{e = I.ite[]} ◾ ite[]
    ; Nat∙ = Nat
    ; num∙ = num
    ; isZero∙ = isZero
    ; _+o∙_ = _+o_
    ; isZeroβ₁∙ = transpconst {B = Tm _ _}{e = I.isZeroβ₁} ◾ isZeroβ₁
    ; isZeroβ₂∙ = transpconst {B = Tm _ _}{e = I.isZeroβ₂} ◾ isZeroβ₂
    ; +β∙ = transpconst {B = Tm _ _}{e = I.+β} ◾ +β
    ; num[]∙ = transpconst {B = Tm _ _}{e = I.num[]} ◾ num[]
    ; isZero[]∙ = transpconst {B = Tm _ _}{e = I.isZero[]} ◾ isZero[]
    ; +[]∙ = transpconst {B = Tm _ _}{e = I.+[]} ◾ +[]
    }
  module D = DepModel D

  ⟦_⟧T : I.Ty → Ty
  ⟦_⟧T = D.⟦_⟧T

  ⟦_⟧C : I.Con → Con
  ⟦_⟧C = D.⟦_⟧C

  ⟦_⟧s : ∀{Γ Δ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
  ⟦_⟧s = D.⟦_⟧s
  
  ⟦_⟧t : ∀{Γ A} → I.Tm  Γ A → Tm  ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦_⟧t = D.⟦_⟧t

-- could be also called PrimitiveModel or ConstDepModel
record ParaModel {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚∙_ _⊚_
  infixl 6 _[_]∙ _[_]
  infixl 5 _▹∙_ _▹_
  infixl 5 _,o∙_ _,o_

  field
    Con∙       : Set i
  Con          : Set i
  Con          = I.Con × Con∙
  field
    Sub∙       : Con → Con → Set j
  Sub          : Con → Con → Set j
  Sub Δ Γ      = I.Sub (π₁ Δ) (π₁ Γ) × Sub∙ Δ Γ
  field
    _⊚∙_       : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub∙ Θ Γ
  _⊚_          : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  γ ⊚ δ        = π₁ γ I.⊚ π₁ δ , γ ⊚∙ δ
  field
    ass∙       : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → π₂ ((γ ⊚ δ) ⊚ θ) ≡ π₂ (γ ⊚ (δ ⊚ θ))
    id∙        : ∀{Γ} → Sub∙ Γ Γ
  id           : ∀{Γ} → Sub Γ Γ
  id {Γ}       = I.id {π₁ Γ} , id∙ {Γ}
  field  
    idl∙       : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (id ⊚ γ) ≡ π₂ γ
    idr∙       : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (γ ⊚ id) ≡ π₂ γ

    ◇∙         : Con∙
  ◇            : Con
  ◇            = I.◇ , ◇∙
  field
    ε∙         : ∀{Γ} → Sub∙ Γ ◇
  ε            : ∀{Γ} → Sub Γ ◇
  ε            = I.ε , ε∙
  field
    ◇η∙        : ∀{Γ}{σ : Sub Γ ◇} → π₂ σ ≡ π₂ (ε {Γ})
    Ty∙        : Set k
  Ty           : Set k
  Ty           = I.Ty × Ty∙
  field
    Tm∙        : Con → Ty → Set l
  Tm           : Con → Ty → Set l
  Tm Γ A       = I.Tm (π₁ Γ) (π₁ A) × Tm∙ Γ A
  field
    _[_]∙      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm∙ Δ A
  _[_]         : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
  a [ γ ]      = π₁ a I.[ π₁ γ ] , a [ γ ]∙
  field
    [∘]∙       : ∀{Γ Δ Θ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →
                 π₂ (t [ γ ⊚ δ ]) ≡ π₂ (t [ γ ] [ δ ])
    [id]∙      : ∀{Γ A}{t : Tm Γ A} → π₂ (t [ id ]) ≡ π₂ t
    _▹∙_       : Con → Ty → Con∙
  _▹_          : Con → Ty → Con
  Γ ▹ A        = π₁ Γ I.▹ π₁ A , Γ ▹∙ A
  field
    _,o∙_      : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub∙ Δ (Γ ▹ A)
  _,o_         : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
  γ ,o a       = π₁ γ I.,o π₁ a , γ ,o∙ a
  field
    p∙         : ∀{Γ A} → Sub∙ (Γ ▹ A) Γ
  p            : ∀{Γ A} → Sub (Γ ▹ A) Γ
  p            = I.p , p∙
  field
    q∙         : ∀{Γ A} → Tm∙ (Γ ▹ A) A
  q            : ∀{Γ A} → Tm (Γ ▹ A) A
  q            = I.q , q∙
  field    
    ▹β₁∙       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → π₂ (p ⊚ (γ ,o t)) ≡ π₂ γ
    ▹β₂∙       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → π₂ (q [ γ ,o t ]) ≡ π₂ t
    ▹η∙        : ∀{Γ Δ A}{γa : Sub Δ (Γ ▹ A)} → π₂ (p ⊚ γa ,o q [ γa ]) ≡ π₂ γa

  field
    Bool∙      : Ty∙
  Bool         : Ty
  Bool         = I.Bool , Bool∙
  field
    true∙      : ∀{Γ} → Tm∙ Γ Bool
  true         : ∀{Γ} → Tm Γ Bool
  true         = I.true , true∙
  field
    false∙     : ∀{Γ} → Tm∙ Γ Bool
  false        : ∀{Γ} → Tm Γ Bool
  false        = I.false , false∙
  field
    ite∙       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm∙ Γ A
  ite          : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
  ite t a a'   = I.ite (π₁ t) (π₁ a) (π₁ a') , ite∙ t a a'
  field
    iteβ₁∙     : ∀{Γ A u v} → π₂ (ite {Γ}{A} true u v) ≡ π₂ u
    iteβ₂∙     : ∀{Γ A u v} → π₂ (ite {Γ}{A} false u v) ≡ π₂ v
    true[]∙    : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (true [ γ ]) ≡ π₂ (true {Δ})
    false[]∙   : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (false [ γ ]) ≡ π₂ (false {Δ})
    ite[]∙     : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} → π₂ ((ite {Γ}{A} t u v) [ γ ]) ≡ π₂ (ite (t [ γ ]) (u [ γ ]) (v [ γ ]))
    
  field
    Nat∙       : Ty∙
  Nat          : Ty
  Nat          = I.Nat , Nat∙
  field
    num∙       : ∀{Γ} → ℕ → Tm∙ Γ Nat
  num          : ∀{Γ} → ℕ → Tm Γ Nat
  num n        = I.num n , num∙ n
  field
    isZero∙    : ∀{Γ} → Tm Γ Nat → Tm∙ Γ Bool
  isZero       : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
  isZero t     = I.isZero (π₁ t) , isZero∙ t
  field
    _+o∙_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm∙ Γ Nat
  _+o_         : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
  t +o t'      = π₁ t I.+o π₁ t' , t +o∙ t'
  field
    isZeroβ₁∙  : ∀{Γ} → π₂ (isZero (num {Γ} 0)) ≡ π₂ (true {Γ})
    isZeroβ₂∙  : ∀{Γ n} → π₂ (isZero (num {Γ} (1 + n))) ≡ π₂ (false {Γ})
    +β∙        : ∀{Γ m n} → π₂ (num {Γ} m +o num n) ≡ π₂ (num (m + n))

    num[]∙     : ∀{Γ n Δ}{γ : Sub Δ Γ} → π₂ (num n [ γ ]) ≡ π₂ (num n)
    isZero[]∙  : ∀{Γ t Δ}{γ : Sub Δ Γ} → π₂ (isZero t [ γ ]) ≡ π₂ (isZero (t [ γ ]))
    +[]∙       : ∀{Γ u v Δ}{γ : Sub Δ Γ} → π₂ ((u +o v) [ γ ]) ≡ π₂ ((u [ γ ]) +o (v [ γ ]))

  D : DepModel -- we use Γ instead of I.Γ for metavariables
  D = record
    { Con∙ = λ _ → Con∙
    ; Sub∙ = λ {Δ} Δ∙ {Γ} Γ∙ _ → Sub∙ (Δ , Δ∙) (Γ , Γ∙)
    ; _⊚∙_ = λ where {γ = γ}{δ} γ∙ δ∙ → (γ , γ∙) ⊚∙ (δ , δ∙)
    ; ass∙ = λ where {γ = γ}{δ = δ}{θ = θ} → transpconst {B = Sub∙ _ _}{e = I.ass {γ = γ}{δ = δ}{θ = θ}} ◾ ass∙
    ; id∙ = id∙
    ; idl∙ = λ where {γ = γ} → transpconst {B = Sub∙ _ _}{e = I.idl {γ = γ}} ◾ idl∙
    ; idr∙ = λ where {γ = γ} → transpconst {B = Sub∙ _ _}{e = I.idr {γ = γ}} ◾ idr∙
    ; ◇∙ = ◇∙
    ; ε∙ = ε∙
    ; ◇η∙ = λ where {σ = σ} → transpconst {B = Sub∙ _ _}{e = I.◇η {σ = σ}} ◾ ◇η∙ {σ = σ , _}
    ; Ty∙ = λ _ → Ty∙
    ; Tm∙ = λ {Γ}{A} Γ∙ A∙ _ → Tm∙ (Γ , Γ∙) (A , A∙)
    ; _[_]∙ = λ where {t = t}{γ} t∙ γ∙ → (t , t∙) [ γ , γ∙ ]∙
    ; [∘]∙ = λ where {t = t}{γ}{δ} → transpconst {B = Tm∙ _ _}{e = I.[∘] {t = t}{γ}{δ}} ◾ [∘]∙
    ; [id]∙ = λ where{t = t} → transpconst {B = Tm∙ _ _}{e = I.[id] {t = t}} ◾ [id]∙
    ; _▹∙_ = λ {Γ}{A} Γ∙ A∙ → (Γ , Γ∙) ▹∙ (A , A∙)
    ; _,o∙_ = λ where {γ = γ}{t} γ∙ t∙ → (γ , γ∙) ,o∙ (t , t∙)
    ; p∙ = p∙
    ; q∙ = q∙
    ; ▹β₁∙ = λ where {γ = γ}{t} → transpconst {B = Sub∙ _ _}{e = I.▹β₁ {γ = γ}{t}} ◾ ▹β₁∙
    ; ▹β₂∙ = λ where {γ = γ}{t} → transpconst {B = Tm∙ _ _}{e = I.▹β₂ {γ = γ}{t}} ◾ ▹β₂∙
    ; ▹η∙ = λ where {γa = γa} → transpconst {B = Sub∙ _ _}{e = I.▹η {γa = γa}} ◾ ▹η∙
    ; Bool∙ = Bool∙
    ; true∙ = true∙
    ; false∙ = false∙
    ; ite∙ = λ where {t = t}{a}{a'} t∙ a∙ a'∙ → ite∙ (t , t∙) (a , a∙) (a' , a'∙)
    ; iteβ₁∙ = λ where {u = u}{v} → transpconst {B = Tm∙ _ _}{e = I.iteβ₁ {u = u}{v = v}} ◾ iteβ₁∙
    ; iteβ₂∙ = λ where {u = u}{v} → transpconst {B = Tm∙ _ _}{e = I.iteβ₂ {u = u}{v = v}} ◾ iteβ₂∙
    ; true[]∙ = transpconst {B = Tm∙ _ _}{e = I.true[]} ◾ true[]∙
    ; false[]∙ = transpconst {B = Tm∙ _ _}{e = I.false[]} ◾ false[]∙
    ; ite[]∙ = transpconst {B = Tm∙ _ _}{e = I.ite[]} ◾ ite[]∙
    ; Nat∙ = Nat∙
    ; num∙ = num∙
    ; isZero∙ = λ where {t = t} t∙ → isZero∙ (t , t∙)
    ; _+o∙_ = λ where {u = u}{v} u∙ v∙ → (u , u∙) +o∙ (v , v∙)
    ; isZeroβ₁∙ = transpconst {B = Tm∙ _ _}{e = I.isZeroβ₁} ◾ isZeroβ₁∙
    ; isZeroβ₂∙ = transpconst {B = Tm∙ _ _}{e = I.isZeroβ₂} ◾ isZeroβ₂∙
    ; +β∙ = transpconst {B = Tm∙ _ _}{e = I.+β} ◾ +β∙
    ; num[]∙ = transpconst {B = Tm∙ _ _}{e = I.num[]} ◾ num[]∙
    ; isZero[]∙ = transpconst {B = Tm∙ _ _}{e = I.isZero[]} ◾ isZero[]∙
    ; +[]∙ = transpconst {B = Tm∙ _ _}{e = I.+[]} ◾ +[]∙
    }
  module D = DepModel D

  ⟦_⟧T : I.Ty → Ty∙
  ⟦_⟧T = D.⟦_⟧T

  ⟦_⟧C : I.Con → Con∙
  ⟦_⟧C = D.⟦_⟧C

  ⟦_⟧s : ∀{Γ Δ} → I.Sub Δ Γ → Sub∙ (Δ , ⟦ Δ ⟧C) (Γ , ⟦ Γ ⟧C)
  ⟦_⟧s = D.⟦_⟧s
  
  ⟦_⟧t : ∀{Γ A} → I.Tm  Γ A → Tm∙ (Γ , ⟦ Γ ⟧C) (A , ⟦ A ⟧T)
  ⟦_⟧t = D.⟦_⟧t

I : Model
I = record { Con = I.Con ; Sub = I.Sub ; _⊚_ = I._⊚_ ; ass = I.ass ; id = I.id ; idl = I.idl ; idr = I.idr ; ◇ = I.◇  ; ε = I.ε ; ◇η = I.◇η ; Ty = I.Ty ; Tm = I.Tm ; _[_] = I._[_] ; [∘] = I.[∘] ; [id] = I.[id] ; _▹_ = I._▹_  ; _,o_ = I._,o_ ; p =  I.p  ; q = I.q ; ▹β₁ = I.▹β₁ ; ▹β₂ = I.▹β₂ ; ▹η = I.▹η ; Bool = I.Bool ; true = I.true ; false = I.false ; ite = I.ite ; iteβ₁ = I.iteβ₁ ; iteβ₂ = I.iteβ₂ ; true[] = I.true[] ; false[] = I.false[] ; ite[] = I.ite[] ; Nat = I.Nat ; num = I.num ; isZero = I.isZero ; _+o_ = I._+o_ ; isZeroβ₁ = I.isZeroβ₁ ; isZeroβ₂ = I.isZeroβ₂ ; +β = I.+β ; num[] = I.num[] ; isZero[] = I.isZero[] ; +[] = I.+[] }

open I public

infixl 6 _⊚Nf_
infixl 6 _[_]V _[_]Ne _[_]Nf
infixl 5 _,Nf_
infixl 7 _+NeNe_ _+NeNf_ _+NfNe_ _+NfNf_

data Var : Con → Ty → Set where
  vz : ∀{Γ A} → Var (Γ ▹ A) A
  vs : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

data Ne (Γ : Con) : Ty → Set
data Nf (Γ : Con) : Ty → Set

data Ne Γ where
  var       : ∀{A} → Var Γ A → Ne Γ A
  iteNe     : ∀{A} → Ne Γ Bool → Nf Γ A → Nf Γ A → Ne Γ A
  isZeroNe  : Ne Γ Nat → Ne Γ Bool
  _+NeNe_   : Ne Γ Nat → Ne Γ Nat → Ne Γ Nat
  _+NeNf_   : Ne Γ Nat → ℕ → Ne Γ Nat
  _+NfNe_   : ℕ → Ne Γ Nat → Ne Γ Nat

data Nf Γ where
  neu       : ∀{A} → Ne Γ A → Nf Γ A
  trueNf    : Nf Γ Bool
  falseNf   : Nf Γ Bool
  numNf     : (n : ℕ) → Nf Γ Nat

⌜_⌝V : ∀{Γ A} → Var Γ A → Tm Γ A
⌜ vz ⌝V = q
⌜ vs x ⌝V = ⌜ x ⌝V [ p ]

⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
⌜ var x ⌝Ne = ⌜ x ⌝V
⌜ iteNe t a a' ⌝Ne = ite ⌜ t ⌝Ne ⌜ a ⌝Nf ⌜ a' ⌝Nf
⌜ isZeroNe t ⌝Ne = isZero ⌜ t ⌝Ne
⌜ t +NeNe t' ⌝Ne = ⌜ t ⌝Ne +o ⌜ t' ⌝Ne
⌜ t +NeNf n' ⌝Ne = ⌜ t ⌝Ne +o num n'
⌜ n +NfNe t' ⌝Ne = num n +o ⌜ t' ⌝Ne
⌜ neu t ⌝Nf = ⌜ t ⌝Ne
⌜ trueNf ⌝Nf = true
⌜ falseNf ⌝Nf = false
⌜ numNf n ⌝Nf = num n

data Nfs (Δ : Con) : Con → Set where
  εNf       : Nfs Δ ◇
  _,Nf_     : ∀{Γ A} → Nfs Δ Γ → Nf Δ A → Nfs Δ (Γ ▹ A)

⌜_⌝Nfs : ∀{Δ Γ} → Nfs Δ Γ → Sub Δ Γ
⌜ εNf ⌝Nfs = ε
⌜ γ ,Nf a ⌝Nfs = ⌜ γ ⌝Nfs ,o ⌜ a ⌝Nf

iteNf : ∀{Γ A} → Nf Γ Bool → Nf Γ A → Nf Γ A → Nf Γ A
iteNf (neu t) a a' = neu (iteNe t a a')
iteNf trueNf a a' = a
iteNf falseNf a a' = a'

_+NfNf_ : ∀{Γ} → Nf Γ Nat → Nf Γ Nat → Nf Γ Nat
neu tn +NfNf neu tn' = neu (tn +NeNe tn')
neu tn +NfNf numNf n = neu (tn +NeNf n)
numNf n +NfNf neu tn = neu (n +NfNe tn)
numNf n +NfNf numNf n' = numNf (n + n')

isZeroNf : ∀{Γ} → Nf Γ Nat → Nf Γ Bool
isZeroNf (neu n) = neu (isZeroNe n)
isZeroNf (numNf zero) = trueNf
isZeroNf (numNf (suc n)) = falseNf

_[_]V : ∀{Γ A} → Var Γ A → ∀{Δ} → Nfs Δ Γ → Nf Δ A
vz [ γ ,Nf a ]V = a
vs x [ γ ,Nf a ]V = x [ γ ]V

_[_]Ne : ∀{Γ A} → Ne Γ A → ∀{Δ} → Nfs Δ Γ → Nf Δ A
_[_]Nf : ∀{Γ A} → Nf Γ A → ∀{Δ} → Nfs Δ Γ → Nf Δ A
var x [ γ ]Ne = x [ γ ]V
iteNe t a a' [ γ ]Ne = iteNf (t [ γ ]Ne) (a [ γ ]Nf) (a' [ γ ]Nf)
(t +NeNe t') [ γ ]Ne = (t [ γ ]Ne) +NfNf (t' [ γ ]Ne)
(t +NeNf n') [ γ ]Ne = (t [ γ ]Ne) +NfNf numNf n'
(n +NfNe t') [ γ ]Ne = numNf n +NfNf (t' [ γ ]Ne)
isZeroNe t [ γ ]Ne = isZeroNf (t [ γ ]Ne)
neu a [ γ ]Nf = a [ γ ]Ne
trueNf [ γ ]Nf = trueNf
falseNf [ γ ]Nf = falseNf
numNf n [ γ ]Nf = numNf n

iteNf[] : ∀{Γ A t u v Δ}{γ : Nfs Δ Γ} →
  (iteNf {Γ}{A} t u v) [ γ ]Nf ≡ iteNf (t [ γ ]Nf) (u [ γ ]Nf) (v [ γ ]Nf)
iteNf[] {t = neu t} = refl
iteNf[] {t = trueNf} = refl
iteNf[] {t = falseNf} = refl

+NfNf[] : ∀{Γ u v Δ}{γ : Nfs Δ Γ} → (u +NfNf v) [ γ ]Nf ≡ (u [ γ ]Nf) +NfNf (v [ γ ]Nf)
+NfNf[] {u = neu   t} {v = neu   t'} = refl
+NfNf[] {u = neu   t} {v = numNf n'} = refl
+NfNf[] {u = numNf n} {v = neu   t'} = refl
+NfNf[] {u = numNf n} {v = numNf n'} = refl

isZeroNf[]  : ∀{Γ t Δ}{γ : Nfs Δ Γ} → isZeroNf t [ γ ]Nf ≡ isZeroNf (t [ γ ]Nf)
isZeroNf[] {t = neu t} = refl
isZeroNf[] {t = numNf zero} = refl
isZeroNf[] {t = numNf (suc n)} = refl

_⊚Nf_ : ∀{Γ Δ Θ} → Nfs Δ Γ → Nfs Θ Δ → Nfs Θ Γ
εNf ⊚Nf δ = εNf
(γ ,Nf t) ⊚Nf δ = (γ ⊚Nf δ) ,Nf (t [ δ ]Nf)

[∘]V : ∀{Γ Δ Θ A}{x : Var Γ A}{γ : Nfs Δ Γ}{δ : Nfs Θ Δ} →
  x [ γ ⊚Nf δ ]V ≡ x [ γ ]V [ δ ]Nf
[∘]V {x = vz}{γ = γ ,Nf a} = refl
[∘]V {x = vs x}{γ = γ ,Nf a} = [∘]V {x = x}

[∘]Ne : ∀{Γ Δ Θ A}{t : Ne Γ A}{γ : Nfs Δ Γ}{δ : Nfs Θ Δ} →
  t [ γ ⊚Nf δ ]Ne ≡ t [ γ ]Ne [ δ ]Nf
[∘]Nf : ∀{Γ Δ Θ A}{t : Nf Γ A}{γ : Nfs Δ Γ}{δ : Nfs Θ Δ} →
  t [ γ ⊚Nf δ ]Nf ≡ t [ γ ]Nf [ δ ]Nf
[∘]Ne {t = var x} = [∘]V {x = x}
[∘]Ne {t = iteNe t a a'}{γ} = cong₃ iteNf ([∘]Ne {t = t}) ([∘]Nf {t = a}) ([∘]Nf {t = a'}) ◾
  iteNf[] {t = t [ γ ]Ne} ⁻¹
[∘]Ne {t = t +NeNe t'}{γ} = cong₂ _+NfNf_ ([∘]Ne {t = t}) ([∘]Ne {t = t'}) ◾
  +NfNf[] {u = t [ γ ]Ne}{v = t' [ γ ]Ne} ⁻¹
[∘]Ne {t = t +NeNf n'}{γ} = cong (_+NfNf numNf n') ([∘]Ne {t = t}) ◾
  +NfNf[] {u = t [ γ ]Ne}{v = numNf n'} ⁻¹
[∘]Ne {t = n +NfNe t'}{γ} = cong (numNf n +NfNf_) ([∘]Ne {t = t'}) ◾
  +NfNf[] {u = numNf n}{v = t' [ γ ]Ne} ⁻¹
[∘]Ne {t = isZeroNe t}{γ} = cong isZeroNf ([∘]Ne {t = t}) ◾ isZeroNf[] {t = t [ γ ]Ne} ⁻¹
[∘]Nf {t = neu t} = [∘]Ne {t = t}
[∘]Nf {t = trueNf} = refl
[∘]Nf {t = falseNf} = refl
[∘]Nf {t = numNf n} = refl

assNf : ∀{Γ Δ Θ Ξ}{γ : Nfs Δ Γ}{δ : Nfs Θ Δ}{θ : Nfs Ξ Θ} →
  (γ ⊚Nf δ) ⊚Nf θ ≡ γ ⊚Nf (δ ⊚Nf θ)
assNf {γ = εNf} {δ} {θ} = refl
assNf {γ = γ ,Nf a} {δ} {θ} = cong₂ _,Nf_ (assNf {γ = γ}) ([∘]Nf {t = a} ⁻¹)

wkNe : ∀{Γ A B} → Ne Γ A → Ne (Γ ▹ B) A
wkNf : ∀{Γ A B} → Nf Γ A → Nf (Γ ▹ B) A
wkNe (var x) = var (vs x)
wkNe (iteNe t a a') = iteNe (wkNe t) (wkNf a) (wkNf a')
wkNe (t +NeNe t') = wkNe t +NeNe wkNe t'
wkNe (t +NeNf n') = wkNe t +NeNf n'
wkNe (n +NfNe t') = n +NfNe wkNe t'
wkNe (isZeroNe t) = isZeroNe (wkNe t)
wkNf (neu t) = neu (wkNe t)
wkNf trueNf = trueNf
wkNf falseNf = falseNf
wkNf (numNf n) = numNf n

wk : ∀{Γ Δ} → Nfs Δ Γ → ∀{A} → Nfs (Δ ▹ A) Γ
wk εNf       = εNf
wk (γ ,Nf a) = wk γ ,Nf wkNf a

wk-iteNf : ∀{Γ A}{t : Nf Γ Bool}{a a' : Nf Γ A}{B} →
  wkNf {B = B} (iteNf t a a') ≡ iteNf (wkNf t) (wkNf a) (wkNf a')
wk-iteNf {t = neu t} = refl
wk-iteNf {t = trueNf} = refl
wk-iteNf {t = falseNf} = refl

wk-+NfNf : ∀{Γ}{t t' : Nf Γ Nat}{B} →
  wkNf {B = B} (t +NfNf t') ≡ wkNf t +NfNf wkNf t'
wk-+NfNf {t = neu   t}{t' = neu   t'} = refl
wk-+NfNf {t = neu   t}{t' = numNf n'} = refl
wk-+NfNf {t = numNf n}{t' = neu   t'} = refl
wk-+NfNf {t = numNf n}{t' = numNf n'} = refl

wk-isZeroNf : ∀{Γ}{t : Nf Γ Nat}{B} → wkNf {B = B} (isZeroNf t) ≡ isZeroNf (wkNf t)
wk-isZeroNf {t = neu x} = refl
wk-isZeroNf {t = numNf zero} = refl
wk-isZeroNf {t = numNf (suc n)} = refl

wkNe[] : ∀{Γ A}{a : Ne Γ A}{Δ}{γ : Nfs Δ Γ}{B}{b : Nf Δ B} →
  wkNe a [ γ ,Nf b ]Ne ≡ a [ γ ]Ne
wkNf[] : ∀{Γ A}{a : Nf Γ A}{Δ}{γ : Nfs Δ Γ}{B}{b : Nf Δ B} →
  wkNf a [ γ ,Nf b ]Nf ≡ a [ γ ]Nf
wkNe[] {a = var x} = refl
wkNe[] {a = iteNe t a a'} = cong₃ iteNf (wkNe[] {a = t}) (wkNf[] {a = a}) (wkNf[] {a = a'})
wkNe[] {a = t +NeNe t'} = cong₂ _+NfNf_ (wkNe[] {a = t}) (wkNe[] {a = t'})
wkNe[] {a = t +NeNf n'} = cong (_+NfNf numNf n') (wkNe[] {a = t})
wkNe[] {a = n +NfNe t'} = cong (numNf n +NfNf_) (wkNe[] {a = t'})
wkNe[] {a = isZeroNe t} = cong isZeroNf (wkNe[] {a = t})
wkNf[] {a = neu a} = wkNe[] {a = a}
wkNf[] {a = trueNf} = refl
wkNf[] {a = falseNf} = refl
wkNf[] {a = numNf n} = refl

wk∘ : ∀{Γ Δ}{γ : Nfs Δ Γ}{Θ}{δ : Nfs Θ Δ}{A}{a : Nf Θ A} →
  wk γ ⊚Nf (δ ,Nf a) ≡ γ ⊚Nf δ
wk∘ {γ = εNf} = refl
wk∘ {γ = γ ,Nf a}{δ = δ} = cong₂ _,Nf_ (wk∘ {γ = γ}) (wkNf[] {a = a})

idNf : ∀{Γ} → Nfs Γ Γ
idNf {◇} = εNf
idNf {Γ ▹ A} = wk (idNf {Γ}) ,Nf neu (var vz)

wk[]V : ∀{Γ A}{x : Var Γ A}{Δ}{γ : Nfs Δ Γ}{B} →
  wkNf {B = B} (x [ γ ]V) ≡ x [ wk γ ]V
wk[]V {x = vz  }{γ = γ ,Nf a} = refl
wk[]V {x = vs x}{γ = γ ,Nf a} = wk[]V {x = x}{γ = γ}

wk[]Ne : ∀{Γ A}{t : Ne Γ A}{Δ}{γ : Nfs Δ Γ}{B} →
  wkNf {B = B} (t [ γ ]Ne) ≡ t [ wk γ ]Ne
wk[]Nf : ∀{Γ A}{t : Nf Γ A}{Δ}{γ : Nfs Δ Γ}{B} →
  wkNf {B = B} (t [ γ ]Nf) ≡ t [ wk γ ]Nf
wk[]Ne {t = var x} = wk[]V {x = x}
wk[]Ne {t = iteNe t a a'}{γ = γ} = wk-iteNf {t = t [ γ ]Ne} ◾
  cong₃ iteNf (wk[]Ne {t = t}) (wk[]Nf {t = a}) (wk[]Nf {t = a'})
wk[]Ne {t = t +NeNe t'} = wk-+NfNf ◾ cong₂ _+NfNf_ (wk[]Ne {t = t}) (wk[]Ne {t = t'})
wk[]Ne {t = t +NeNf n'} = wk-+NfNf ◾ cong (_+NfNf numNf n') (wk[]Ne {t = t})
wk[]Ne {t = n +NfNe t'} = wk-+NfNf ◾ cong (numNf n +NfNf_) (wk[]Ne {t = t'})
wk[]Ne {t = isZeroNe t} = wk-isZeroNf ◾ cong isZeroNf (wk[]Ne {t = t})
wk[]Nf {t = neu t} = wk[]Ne {t = t}
wk[]Nf {t = trueNf} = refl
wk[]Nf {t = falseNf} = refl
wk[]Nf {t = numNf n} = refl

[id]V : ∀{Γ A}{x : Var Γ A} → x [ idNf ]V ≡ neu (var x)
[id]V {x = vz} = refl
[id]V {x = vs x} = wk[]V {x = x} ⁻¹ ◾ cong wkNf ([id]V {x = x})

[id]Ne : ∀{Γ A}{t : Ne Γ A} → t [ idNf ]Ne ≡ neu t
[id]Nf : ∀{Γ A}{t : Nf Γ A} → t [ idNf ]Nf ≡ t
[id]Ne {t = var x} = [id]V {x = x}
[id]Ne {t = iteNe t a a'} = cong₃ iteNf ([id]Ne {t = t}) ([id]Nf {t = a}) ([id]Nf {t = a'})
[id]Ne {t = t +NeNe t'} = cong₂ _+NfNf_ ([id]Ne {t = t}) ([id]Ne {t = t'})
[id]Ne {t = t +NeNf n'} = cong (_+NfNf numNf n') ([id]Ne {t = t})
[id]Ne {t = n +NfNe t'} = cong (numNf n +NfNf_) ([id]Ne {t = t'})
[id]Ne {t = isZeroNe t} = cong isZeroNf ([id]Ne {t = t})
[id]Nf {t = neu t} = [id]Ne {t = t}
[id]Nf {t = trueNf} = refl
[id]Nf {t = falseNf} = refl
[id]Nf {t = numNf n} = refl

idlNf : ∀{Γ Δ}{γ : Nfs Δ Γ} → idNf ⊚Nf γ ≡ γ
idlNf {Γ = ◇}{γ = εNf} = refl
idlNf {Γ = Γ ▹ A}{γ = γ ,Nf a} = cong (_,Nf a) (wk∘ {γ = idNf} ◾ idlNf {Γ = Γ})

idrNf : ∀{Γ Δ}{γ : Nfs Δ Γ} → γ ⊚Nf idNf ≡ γ
idrNf {γ = εNf} = refl
idrNf {γ = γ ,Nf a} = cong₂ _,Nf_ (idrNf {γ = γ}) [id]Nf

pNf : ∀{Γ A} → Nfs (Γ ▹ A) Γ
pNf = wk idNf

▹β₁Nf : ∀{Γ Δ A}{γ : Nfs Δ Γ}{t : Nf Δ A} → pNf ⊚Nf (γ ,Nf t) ≡ γ
▹β₁Nf = wk∘ ◾ idlNf

▹ηNf : ∀{Γ Δ A}{γa : Nfs Δ (Γ ▹ A)} → pNf ⊚Nf γa ,Nf vz [ γa ]V ≡ γa
▹ηNf {γa = γ ,Nf a} = cong (_,Nf a) (wk∘ ◾ idlNf)

N : ParaModel
N = record
  { Con∙ = Lift ⊤
  ; Sub∙ = λ Δ Γ → Nfs (π₁ Δ) (π₁ Γ)
  ; _⊚∙_ = λ γ δ → π₂ γ ⊚Nf π₂ δ
  ; ass∙ = assNf
  ; id∙ = idNf
  ; idl∙ = idlNf
  ; idr∙ = idrNf
  ; ◇∙ = _
  ; ε∙ = εNf
  ; ◇η∙ = λ { {_}{_ , εNf} → refl }
  ; Ty∙ = Lift ⊤
  ; Tm∙ = λ Γ A → Nf (π₁ Γ) (π₁ A)
  ; _[_]∙ = λ a γ → π₂ a [ π₂ γ ]Nf
  ; [∘]∙ = λ where {t = t} → [∘]Nf {t = π₂ t}
  ; [id]∙ = [id]Nf
  ; _▹∙_ = _
  ; _,o∙_ = λ γ a → π₂ γ ,Nf π₂ a
  ; p∙ = pNf
  ; q∙ = neu (var vz)
  ; ▹β₁∙ = ▹β₁Nf
  ; ▹β₂∙ = refl
  ; ▹η∙ = ▹ηNf
  ; Bool∙ = _
  ; true∙ = trueNf
  ; false∙ = falseNf
  ; ite∙ = λ t a a' → iteNf (π₂ t) (π₂ a) (π₂ a')
  ; iteβ₁∙ = refl
  ; iteβ₂∙ = refl
  ; true[]∙ = refl
  ; false[]∙ = refl
  ; ite[]∙ = λ where {t = t} → iteNf[] {t = π₂ t}
  ; Nat∙ = _
  ; num∙ = numNf
  ; isZero∙ = λ t → isZeroNf (π₂ t)
  ; _+o∙_ = λ t t' → π₂ t +NfNf π₂ t'
  ; isZeroβ₁∙ = refl
  ; isZeroβ₂∙ = refl
  ; +β∙ = refl
  ; num[]∙ = refl
  ; isZero[]∙ = λ where {t = t} → isZeroNf[] {t = π₂ t}
  ; +[]∙ = λ where {u = u} → +NfNf[] {u = π₂ u}
  }

module N = ParaModel N

norm : ∀{Γ A} → Tm Γ A → Nf Γ A
norm = N.⟦_⟧t

⌜ite⌝ : ∀{Γ A}{t : Nf Γ Bool}{a a' : Nf Γ A} →
  ⌜ iteNf t a a' ⌝Nf ≡ ite ⌜ t ⌝Nf ⌜ a ⌝Nf ⌜ a' ⌝Nf
⌜ite⌝ {t = neu t} = refl
⌜ite⌝ {t = trueNf} = iteβ₁ ⁻¹
⌜ite⌝ {t = falseNf} = iteβ₂ ⁻¹

⌜isZero⌝ : ∀{Γ}{t : Nf Γ Nat} → ⌜ isZeroNf t ⌝Nf ≡ isZero ⌜ t ⌝Nf
⌜isZero⌝ {t = neu t} = refl
⌜isZero⌝ {t = numNf zero} = isZeroβ₁ ⁻¹
⌜isZero⌝ {t = numNf (suc n)} = isZeroβ₂ ⁻¹

⌜+⌝ : ∀{Γ}{t t' : Nf Γ Nat} → ⌜ t +NfNf t' ⌝Nf ≡ ⌜ t ⌝Nf +o ⌜ t' ⌝Nf
⌜+⌝ {t = neu t} {t' = neu t'} = refl
⌜+⌝ {t = neu t} {t' = numNf n'} = refl
⌜+⌝ {t = numNf n} {t' = neu t'} = refl
⌜+⌝ {t = numNf n} {t' = numNf n'} = +β ⁻¹

⌜[]V⌝ : ∀{Γ Δ A}{x : Var Γ A}{γ : Nfs Δ Γ} → ⌜ x [ γ ]V ⌝Nf ≡ ⌜ x ⌝V [ ⌜ γ ⌝Nfs ]
⌜[]V⌝ {x = vz}{γ = γ ,Nf a} = ▹β₂ ⁻¹
⌜[]V⌝ {x = vs x}{γ = γ ,Nf a} = ⌜[]V⌝ {x = x} ◾ cong (⌜ x ⌝V [_]) (▹β₁ ⁻¹) ◾ [∘]

⌜[]Ne⌝ : ∀{Γ Δ A}{a : Ne Γ A}{γ : Nfs Δ Γ} → ⌜ a [ γ ]Ne ⌝Nf ≡ ⌜ a ⌝Ne [ ⌜ γ ⌝Nfs ]
⌜[]Nf⌝ : ∀{Γ Δ A}{a : Nf Γ A}{γ : Nfs Δ Γ} → ⌜ a [ γ ]Nf ⌝Nf ≡ ⌜ a ⌝Nf [ ⌜ γ ⌝Nfs ]

⌜[]Ne⌝ {a = var x} = ⌜[]V⌝ {x = x}
⌜[]Ne⌝ {a = iteNe t a a'} = ⌜ite⌝ {t = t [ _ ]Ne}{a = a [ _ ]Nf}{a' = a' [ _ ]Nf} ◾ cong₃ ite (⌜[]Ne⌝ {a = t}) (⌜[]Nf⌝ {a = a}) (⌜[]Nf⌝ {a = a'}) ◾ ite[] ⁻¹
⌜[]Ne⌝ {a = isZeroNe t} = ⌜isZero⌝ {t = t [ _ ]Ne} ◾ cong isZero (⌜[]Ne⌝ {a = t}) ◾ isZero[] ⁻¹
⌜[]Ne⌝ {a = t +NeNe t'} = ⌜+⌝ {t = t [ _ ]Ne}{t' = t' [ _ ]Ne} ◾ cong₂ _+o_ (⌜[]Ne⌝ {a = t}) (⌜[]Ne⌝ {a = t'}) ◾ +[] ⁻¹
⌜[]Ne⌝ {a = t +NeNf n'} = ⌜+⌝ {t = t [ _ ]Ne}{t' = numNf n'} ◾ cong₂ _+o_ (⌜[]Ne⌝ {a = t}) (num[] ⁻¹) ◾ +[] ⁻¹
⌜[]Ne⌝ {a = n +NfNe t'} = ⌜+⌝ {t = numNf n}{t' = t' [ _ ]Ne} ◾ cong₂ _+o_ (num[] ⁻¹) (⌜[]Ne⌝ {a = t'}) ◾ +[] ⁻¹
⌜[]Nf⌝ {a = neu a} = ⌜[]Ne⌝ {a = a}
⌜[]Nf⌝ {a = trueNf} = true[] ⁻¹
⌜[]Nf⌝ {a = falseNf} = false[] ⁻¹
⌜[]Nf⌝ {a = numNf n} = num[] ⁻¹

⌜wkNe⌝ : ∀{Γ A}{a : Ne Γ A}{B} → ⌜ wkNe {B = B} a ⌝Ne ≡ ⌜ a ⌝Ne [ p ]
⌜wkNf⌝ : ∀{Γ A}{a : Nf Γ A}{B} → ⌜ wkNf {B = B} a ⌝Nf ≡ ⌜ a ⌝Nf [ p ]
⌜wkNe⌝ {a = var x} = refl
⌜wkNe⌝ {a = iteNe t a a'} = cong₃ ite (⌜wkNe⌝ {a = t}) (⌜wkNf⌝ {a = a}) (⌜wkNf⌝ {a = a'}) ◾ ite[] ⁻¹
⌜wkNe⌝ {a = isZeroNe t} = cong isZero (⌜wkNe⌝ {a = t}) ◾ isZero[] ⁻¹
⌜wkNe⌝ {a = t +NeNe t'} = cong₂ _+o_ (⌜wkNe⌝ {a = t}) (⌜wkNe⌝ {a = t'}) ◾ +[] ⁻¹
⌜wkNe⌝ {a = t +NeNf n'} = cong₂ _+o_ (⌜wkNe⌝ {a = t}) (num[] ⁻¹) ◾ +[] ⁻¹
⌜wkNe⌝ {a = n +NfNe t'} = cong₂ _+o_ (num[] ⁻¹) (⌜wkNe⌝ {a = t'}) ◾ +[] ⁻¹
⌜wkNf⌝ {a = neu a} = ⌜wkNe⌝ {a = a}
⌜wkNf⌝ {a = trueNf} = true[] ⁻¹
⌜wkNf⌝ {a = falseNf} = false[] ⁻¹
⌜wkNf⌝ {a = numNf n} = num[] ⁻¹

⌜wk⌝ : ∀{Γ Δ}{γ : Nfs Δ Γ}{A} → ⌜ wk γ {A = A} ⌝Nfs ≡ ⌜ γ ⌝Nfs ⊚ p
⌜wk⌝ {γ = εNf} = ◇η ⁻¹
⌜wk⌝ {γ = γ ,Nf a} = cong₂ _,o_ (⌜wk⌝ {γ = γ}) (⌜wkNf⌝ {a = a}) ◾ ,∘ ⁻¹

⌜id⌝ : ∀{Γ} → ⌜ idNf {Γ} ⌝Nfs ≡ id
⌜id⌝ {◇} = ◇η ⁻¹
⌜id⌝ {Γ ▹ A} = cong₂ _,o_ (⌜wk⌝ ◾ (cong (_⊚ p) (⌜id⌝ {Γ}) ◾ idl ◾ idr ⁻¹)) ([id] ⁻¹) ◾ ▹η

⌜∘⌝ : ∀{Γ Δ Θ}{γ : Nfs Δ Γ}{δ : Nfs Θ Δ} → ⌜ γ ⊚Nf δ ⌝Nfs ≡ ⌜ γ ⌝Nfs ⊚ ⌜ δ ⌝Nfs
⌜∘⌝ {γ = εNf} = ◇η ⁻¹
⌜∘⌝ {γ = γ ,Nf a} = cong₂ _,o_ (⌜∘⌝ {γ = γ}) (⌜[]Nf⌝ {a = a}) ◾ ,∘ ⁻¹

C : DepModel
C = record
  { Con∙ = λ _ → Lift ⊤
  ; Sub∙ = λ {Δ} _ {Γ} _ γ → Lift (⌜ N.⟦ γ ⟧s ⌝Nfs ≡ γ)
  ; _⊚∙_ = λ γ= δ= → mk (⌜∘⌝ ◾ cong₂ _⊚_ (un γ=) (un δ=))
  ; ass∙ = refl
  ; id∙ = mk ⌜id⌝
  ; idl∙ = refl
  ; idr∙ = refl
  ; ◇∙ = _
  ; ε∙ = mk refl
  ; ◇η∙ = refl
  ; Ty∙ = λ _ → Lift ⊤
  ; Tm∙ = λ {Γ}{A} _ _ a → Lift (⌜ N.⟦ a ⟧t ⌝Nf ≡ a)
  ; _[_]∙ = λ where {t = a} a= γ= → mk (⌜[]Nf⌝ {a = N.⟦ a ⟧t} ◾ cong₂ _[_] (un a=) (un γ=))
  ; [∘]∙ = refl
  ; [id]∙ = refl
  ; _▹∙_ = _
  ; _,o∙_ = λ where {γ = γ}{a} γ= a= → mk (cong₂ _,o_ (un γ=) (un a=))
  ; p∙ = mk (⌜wk⌝ {γ = idNf} ◾ cong (_⊚ p) ⌜id⌝ ◾ idl)
  ; q∙ = mk refl
  ; ▹β₁∙ = refl
  ; ▹β₂∙ = refl
  ; ▹η∙ = refl
  ; Bool∙ = _
  ; true∙ = mk refl
  ; false∙ = mk refl
  ; ite∙ = λ where {t = t}{a}{a'} t= a= a'= → mk (⌜ite⌝ {t = N.⟦ t ⟧t} ◾ cong₃ ite (un t=) (un a=) (un a'=))
  ; iteβ₁∙ = refl
  ; iteβ₂∙ = refl
  ; true[]∙ = refl
  ; false[]∙ = refl
  ; ite[]∙ = refl
  ; Nat∙ = _
  ; num∙ = λ _ → mk refl
  ; isZero∙ = λ where {t = t} t= → mk (⌜isZero⌝ {t = N.⟦ t ⟧t} ◾ cong isZero (un t=))
  ; _+o∙_ = λ where {u = t}{t'} t= t'= → mk (⌜+⌝ {t = N.⟦ t ⟧t}{t' = N.⟦ t' ⟧t} ◾ cong₂ _+o_ (un t=) (un t'=))
  ; isZeroβ₁∙ = refl
  ; isZeroβ₂∙ = refl
  ; +β∙ = refl
  ; num[]∙ = refl
  ; isZero[]∙ = refl
  ; +[]∙ = refl
  }
module C = DepModel C

compl : ∀{Γ A}(t : Tm Γ A) → ⌜ norm t ⌝Nf ≡ t
compl t = un C.⟦ t ⟧t
