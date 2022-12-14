{-# OPTIONS --prop --rewriting #-}

module hf07import where

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to โ)
open import Agda.Builtin.Bool public renaming (Bool to ๐; true to tt; false to ff)
open import Agda.Builtin.Sigma public renaming (fst to ฯโ; snd to ฯโ)

infix  4 _โก_ _โ_
infixr 2 _โกโก_
infix  3 _โ
infixr 2 _โกโจ_โฉ_
infixr 7 _โ_
infixl 8 _โจ_
infixl 9 _โง_
infixr 1 _โ_
infixr 2 _ร_
infixr 4 _,_
infixr 4 _,=_ _,ร=_
infixl 6 _โ_
infixl 2 _โพ_
infix 5 _โปยน


-- rewriting

postulate _โ_ : โ{โ}{A : Set โ}(a : A) โ A โ Set โ
{-# BUILTIN REWRITE _โ_ #-}


-- exercise

postulate
  exercise  : โ{โ}{A : Set  โ} โ A
  exercisep : โ{โ}{A : Prop โ} โ A

-- Bottom

data โฅ : Prop where

exfalso : โ{โ}{A : Set โ} โ โฅ โ A
exfalso ()

exfalsop : โ{โ}{A : Prop โ} โ โฅ โ A
exfalsop ()

ยฌ_ : โ{โ}(A : Prop โ) โ Prop โ
ยฌ A = A โ โฅ


-- Top

record โค : Prop where
  constructor triv

-- Functions

_โ_ : โ {โ โ' โ''} {A : Set โ}{B : A โ Set โ'}{C : โ {x} โ B x โ Set โ''}
  (f : โ {x} (y : B x) โ C y)(g : (x : A) โ B x)
  (x : A) โ C (g x)
(f โ g) x = f (g x)


-- Lift

record Lift {โ}(A : Prop โ) : Set โ where
  constructor mk
  field un : A
open Lift public


-- Raise

record Raise {โ โ'}(A : Set โ) : Set (โ โ โ') where
  constructor mk
  field un : A
open Raise public


-- Equality

data _โก_ {โ}{A : Set โ}(a : A) : A โ Prop โ where
  refl : a โก a

{-# BUILTIN EQUALITY _โก_ #-}

infix 4 _โข_

_โข_ : โ{โ}{A : Set โ}(a : A) โ A โ Prop โ
x โข y = ยฌ (x โก y)

_โพ_ : โ{โ}{A : Set โ}{a a' : A} โ a โก a' โ โ{a''} โ a' โก a'' โ a โก a''
refl โพ refl = refl

postulate transp       : โ{โ}{A : Set โ}{โ'}(P : A โ Set โ'){a a' : A} โ a โก a' โ P a โ P a'
postulate transprefl   : โ{โ}{A : Set โ}{โ'}{P : A โ Set โ'}{a : A}{e : a โก a}{p : P a} โ transp P e p โ p

{-# REWRITE transprefl   #-}
-- {-# REWRITE transpconst  #-}
-- {-# REWRITE transptransp #-}

_โปยน : โ{โ}{A : Set โ}{a a' : A} โ a โก a' โ a' โก a
refl โปยน = refl

cong : โ{โ}{A : Set โ}{โ'}{B : Set โ'}(f : A โ B){a a' : A} โ a โก a' โ f a โก f a'
cong f refl = refl

congโ : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}{C : Set โ''}
        {a c : A}{b d : B}(f : A โ B โ C)(p : a โก c)(q : b โก d) โ
        f a b โก f c d
congโ f refl refl = refl

congโ : โ{โ โ' โ'' โ'''}{A : Set โ}{B : Set โ'}{C : Set โ''}{D : Set โ'''}
        {a d : A}{b e : B}{c f : C}(g : A โ B โ C โ D)(p : a โก d)(q : b โก e)(r : c โก f) โ
        g a b c โก g d e f
congโ g refl refl refl = refl

transpconst  : โ{โ}{A : Set โ}{โ'}{B : Set โ'}{a a' : A}{e : a โก a'}{b : B} โ transp (ฮป _ โ B) e b โก b
transpconst {e = refl} = refl

transptransp : โ{โ}{A : Set โ}{โ'}(P : A โ Set โ'){a a' a'' : A}(e : a โก a'){e' : a' โก a''}{p : P a} โ transp P e' (transp P e p) โก transp P (e โพ e') p
transptransp P refl {refl} = refl

transpโ' : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : A โ Set โ''){a a' : A}(e : a โก a'){f : B โ C a} โ 
  transp (ฮป a โ B โ C a) e f โก ฮป b โ transp C e (f b)
transpโ' C refl = refl

transpโi' : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : A โ Set โ''){a a' : A}(e : a โก a'){f : {b : B} โ C a} โ 
  (ฮป {b} โ transp (ฮป a โ {_ : B} โ C a) e (ฮป {b} โ f {b}) {b}) โก (ฮป {b} โ transp C e (f {b}))
transpโi' C refl = refl

transpฮ?' : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : A โ B โ Set โ''){a a' : A}(e : a โก a'){f : (b : B) โ C a b} โ 
  transp (ฮป a โ (b : B) โ C a b) e f โก ฮป b โ transp (ฮป a โ C a b) e (f b)
transpฮ?' C refl = refl

transpฮ?i' : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : A โ B โ Set โ''){a a' : A}(e : a โก a'){f : {b : B} โ C a b} โ 
  (ฮป {b} โ transp (ฮป a โ {b : B} โ C a b) e f {b}) โก ฮป {b} โ transp (ฮป a โ C a b) e (f {b})
transpฮ?i' C refl = refl

transpโ : โ{โ โ' โ''}{A : Set โ}{B : A โ Set โ'}(C : A โ Set โ''){a a' : A}(e : a โก a'){f : B a โ C a} โ 
  transp (ฮป a โ B a โ C a) e f โก ฮป b' โ transp C e (f (transp B (e โปยน) b'))
transpโ C refl = refl

transpcong : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : B โ Set โ'')(f : A โ B){a a' : A}(e : a โก a'){c : C (f a)} โ transp {A = B} C {f a} {f a'} (cong f e) c โก transp {A = A} (ฮป a โ C (f a)) {a} {a'} e c
transpcong C f refl = refl

transp$ : โ{โ โ' โ''}{A : Set โ}{B : A โ Set โ'}{C : A โ Set โ''}(f : โ a โ B a โ C a){a a' : A}(e : a โก a'){b : B a} โ f a' (transp B e b) โก transp C e (f a b) 
transp$ f refl = refl

transp$i : โ{โ โ' โ''}{A : Set โ}{B : A โ Set โ'}{C : A โ Set โ''}(f : โ{a} โ B a โ C a){a a' : A}(e : a โก a'){b : B a} โ f (transp B e b) โก transp C e (f b) 
transp$i f refl = refl

-- if this doesn't normalise (C-c C-n PROBLEM), then your Agda is too old
PROBLEM : {A : Set}(B : A โ Prop){a a' : A}(e : a โก a') โ B a โ Lift (B a')
PROBLEM B e b = transp (ฮป a โ Lift (B a)) e (mk b)

_~ : โ{โ โ'}{A : Set โ}(B : A โ Set โ'){aโ aโ : A}(aโโ : aโ โก aโ) โ B aโ โ B aโ โ Prop โ'
(B ~) aโโ bโ bโ = transp B aโโ bโ โก bโ

_โกโจ_โฉ_ : โ{โ}{A : Set โ}(x : A){y z : A} โ x โก y โ y โก z โ x โก z
x โกโจ xโกy โฉ yโกz = xโกy โพ yโกz

_โกโก_ : โ{โ}{A : Set โ}(x : A){y} โ x โก y โ x โก y
x โกโก xโกy = xโกy

_โ : โ{โ}{A : Set โ}(a : A) โ a โก a
a โ = refl

transpP : โ{โ}{A : Set โ}{โ'}(P : A โ Prop โ'){a a' : A} โ a โก a' โ P a โ P a'
transpP P refl p = p

UIP : โ{โ}{A : Set โ}{a a' : A}{e e' : a โก a'} โ _โก_ {A = Lift (a โก a')} (mk e) (mk e')
UIP = refl


-- Function space

postulate funext  : โ{โ}{A : Set โ}{โ'}{B : A โ Set โ'}{f g : (x : A) โ B x} โ ((x : A) โ f x โก g x) โ f โก g
postulate funexti : โ{โ}{A : Set โ}{โ'}{B : A โ Set โ'}{f g : {x : A} โ B x} โ ((x : A) โ f {x} โก g {x}) โ (ฮป {x} โ f {x}) โก g


-- Maybe

data Maybe {โ}(A : Set โ) : Set โ where
  Nothing  : Maybe A
  Just     : A โ Maybe A

caseMaybe : โ{โ โ'}{A : Set โ}{B : Set โ'} โ B โ (A โ B) โ Maybe A โ B
caseMaybe n j Nothing = n
caseMaybe n j (Just a) = j a


-- Product

_ร_ : โ{โ}{โ'}(A : Set โ)(B : Set โ') โ Set (โ โ โ')
A ร B = ฮฃ A (ฮป _ โ B)

_,=_ : โ{โ}{A : Set โ}{โ'}{B : A โ Set โ'}{a a' : A}(e : a โก a') โ {b : B a}{b' : B a'} โ (B ~) e b b' โ (a , b) โก (a' , b')
_,=_ refl refl = refl

_,ร=_ : โ{โ}{A : Set โ}{โ'}{B : Set โ'}{a a' : A}(e : a โก a') โ {b b' : B} โ b  โก b' โ (a , b) โก (a' , b')
_,ร=_ refl refl = refl

record ฮฃsp {โ โ'} (A : Set โ)(B : A โ Prop โ') : Set (โ โ โ') where
  constructor _,_
  field
    ฯโ : A
    ฯโ : B ฯโ
open ฮฃsp public

_,=- : โ{โ}{A : Set โ}{โ'}{B : A โ Prop โ'}{a a' : A}(e : a โก a') โ {b : B a}{b' : B a'} โ _โก_ {A = ฮฃsp A B} (a , b) (a' , b')
_,=- refl = refl

transpร : โ{โ โ' โ''}{A : Set โ}(B : A โ Set โ')(C : A โ Set โ''){a : A}{w : B a ร C a}{a' : A}(e : a โก a') โ
  transp (ฮป a โ B a ร C a) e w โก (transp B e (ฯโ w) , transp C e (ฯโ w))
transpร B C refl = refl

transpฮฃ' : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(C : A โ B โ Set โ''){a a' : A}(e : a โก a'){w : ฮฃ B (C a)} โ
  transp (ฮป a โ ฮฃ B (C a)) e w โก (ฯโ w , transp (ฮป a โ C a (ฯโ w)) e (ฯโ w))
transpฮฃ' C refl = refl


-- โ

max : โ โ โ โ โ
max zero    b       = b
max (suc a) zero    = suc a
max (suc a) (suc b) = suc (max a b)

iteโ : โ{โ}{A : Set โ}(u : A)(v : A โ A)(t : โ) โ A
iteโ u v zero = u
iteโ u v (suc t) = v (iteโ u v t)

indโ : โ{โ}(A : โ โ Set โ)(z : A zero)(s : โ n โ A n โ A (suc n))(n : โ) โ A n
indโ A z s zero = z
indโ A z s (suc n) = s n (indโ A z s n)

zeroโ?suc : {n : โ} โ ยฌ (zero โก suc n)
zeroโ?suc e = transpP P e triv
  where
    P : โ โ Prop
    P zero = โค
    P (suc _) = โฅ

ass+ : โ{m n o} โ (m + n) + o โก m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

idr+ : โ{n} โ n + 0 โก n
idr+ {zero} = refl
idr+ {suc n} = cong suc (idr+ {n})

+suc : โ{m n} โ m + suc n โก suc (m + n)
+suc {zero} = refl
+suc {suc m} = cong suc (+suc {m})

+comm : โ{m n} โ m + n โก n + m
+comm {zero} = idr+ โปยน
+comm {suc m}{n} = cong suc (+comm {m}{n}) โพ +suc {n}{m} โปยน

-- ๐

if_then_else_ : โ{โ}{A : Set โ}(t : ๐)(u v : A) โ A
if tt then u else v = u
if ff then u else v = v

_โจ_ : ๐ โ ๐ โ ๐
a โจ b = if a then tt else b

_โง_ : ๐ โ ๐ โ ๐
a โง b = if a then b else ff

_โ_ : ๐ โ ๐ โ ๐
a โ b = if a then b else tt

ttโ?ff : ยฌ (tt โก ff)
ttโ?ff e = transpP P e triv
  where
    P : ๐ โ Prop
    P tt = โค
    P ff = โฅ


-- Sum type

data _โ_ {โ}{โ'}(A : Set โ)(B : Set โ') : Set (โ โ โ') where
  ฮนโ : A โ A โ B
  ฮนโ : B โ A โ B

case : โ {โ โ' โ''}{A : Set โ}{B : Set โ'}{C : Set โ''}
       (t : A โ B)(u : A โ C)(v : B โ C) โ C
case (ฮนโ t) u v = u t
case (ฮนโ t) u v = v t

indโ : โ{โ โ' โ''}{A : Set โ}{B : Set โ'}(P : A โ B โ Set โ'') โ
       ((a : A) โ P (ฮนโ a)) โ ((b : B) โ P (ฮนโ b)) โ (t : A โ B) โ P t
indโ P u v (ฮนโ t) = u t
indโ P u v (ฮนโ t) = v t

transpโ : โ{โ โ' โ''}{A : Set โ}(B : A โ Set โ')(C : A โ Set โ''){a : A}{w : B a โ C a}{a' : A}(e : a โก a') โ
  transp (ฮป a โ B a โ C a) e w โก case w (ฮป b โ ฮนโ (transp B e b)) (ฮป c โ ฮนโ (transp C e c))
transpโ B C {w = ฮนโ a} refl = refl
transpโ B C {w = ฮนโ b} refl = refl

casetransp : โ{โ โ' โ'' โ'''}{A : Set โ}(B : A โ Set โ')(C : A โ Set โ''){D : Set โ'''}{a a' : A}(e : a โก a')(w : B a โ C a){u : B a' โ D}{v : C a' โ D} โ
  case (transp (ฮป a โ B a โ C a) e w) u v โก case w (ฮป b โ u (transp B e b)) (ฮป c โ v (transp C e c))
casetransp B C refl w = refl

transpcase : โ{โ โ' โ'' โ'''}{A : Set โ}{B : Set โ'}{C : Set โ''}(D : A โ Set โ'''){a a' : A}(e : a โก a')(w : B โ C){u : B โ D a}{v : C โ D a} โ
  transp D e (case w u v) โก case w (ฮป a โ transp D e (u a)) (ฮป b โ transp D e (v b))
transpcase D refl e = refl

Dec : โ{โ} โ Set โ โ Set โ
Dec A = A โ Lift (A โ โฅ)

True : โ{i}{A : Set i} โ Dec A โ Set
True (ฮนโ _) = Lift โค
True (ฮนโ _) = Lift โฅ

extract : โ{i}{A : Set i}(da : Dec A) โ {True da} โ A
extract (ฮนโ a) = a

-- finite types

data Fin : โ โ Set where
  zero : {n : โ} โ Fin (suc n)
  suc  : {n : โ} โ Fin n โ Fin (suc n)

{-# INJECTIVE Fin #-}

module I where
  infixl 6 _โ_
  infixl 6 _[_]
  infixl 5 _โน_
  infixl 5 _,o_
  infixr 5 _โ_
  infixl 5 _$_
  infixl 7 _+o_

  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty
    _โ_     : Ty โ Ty โ Ty

  data Con  : Set where
    โ       : Con
    _โน_     : Con โ Ty โ Con

  postulate
    Sub       : Con โ Con โ Set
    _โ_       : โ{ฮ ฮ ฮ} โ Sub ฮ ฮ โ Sub ฮ ฮ โ Sub ฮ ฮ
    ass       : โ{ฮ ฮ ฮ ฮ}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ}{ฮธ : Sub ฮ ฮ} โ (ฮณ โ ฮด) โ ฮธ โก ฮณ โ (ฮด โ ฮธ)
    id        : โ{ฮ} โ Sub ฮ ฮ
    idl       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ id โ ฮณ โก ฮณ
    idr       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฮณ โ id โก ฮณ

    ฮต         : โ{ฮ} โ Sub ฮ โ
    โฮท        : โ{ฮ}{ฯ : Sub ฮ โ} โ ฯ โก ฮต

    Tm        : Con โ Ty โ Set
    _[_]      : โ{ฮ ฮ A} โ Tm ฮ A โ Sub ฮ ฮ โ Tm ฮ A
    [โ]       : โ{ฮ ฮ ฮ A}{t : Tm ฮ A}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ} โ  t [ ฮณ โ ฮด ] โก t [ ฮณ ] [ ฮด ]
    [id]      : โ{ฮ A}{t : Tm ฮ A} โ t [ id ] โก t
    _,o_      : โ{ฮ ฮ A} โ Sub ฮ ฮ โ Tm ฮ A โ Sub ฮ (ฮ โน A)
    p         : โ{ฮ A} โ Sub (ฮ โน A) ฮ
    q         : โ{ฮ A} โ Tm (ฮ โน A) A
    โนฮฒโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ p โ (ฮณ ,o t) โก ฮณ
    โนฮฒโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ q [ ฮณ ,o t ] โก t
    โนฮท        : โ{ฮ ฮ A}{ฮณa : Sub ฮ (ฮ โน A)} โ p โ ฮณa ,o q [ ฮณa ] โก ฮณa

    true      : โ{ฮ} โ Tm ฮ Bool
    false     : โ{ฮ} โ Tm ฮ Bool
    ite       : โ{ฮ A} โ Tm ฮ Bool โ Tm ฮ A โ Tm ฮ A โ Tm ฮ A
    iteฮฒโ     : โ{ฮ A u v} โ ite {ฮ}{A} true u v โก u
    iteฮฒโ     : โ{ฮ A u v} โ ite {ฮ}{A} false u v โก v
    true[]    : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ true [ ฮณ ] โก true
    false[]   : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ false [ ฮณ ] โก false
    ite[]     : โ{ฮ A t u v ฮ}{ฮณ : Sub ฮ ฮ} โ (ite {ฮ}{A} t u v) [ ฮณ ] โก ite (t [ ฮณ ]) (u [ ฮณ ]) (v [ ฮณ ])

    num       : โ{ฮ} โ โ โ Tm ฮ Nat
    isZero    : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Bool
    _+o_      : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Nat โ Tm ฮ Nat
    isZeroฮฒโ  : โ{ฮ} โ isZero (num {ฮ} 0) โก true
    isZeroฮฒโ  : โ{ฮ n} โ isZero (num {ฮ} (1 + n)) โก false
    +ฮฒ        : โ{ฮ m n} โ num {ฮ} m +o num n โก num (m + n)
    num[]     : โ{ฮ n ฮ}{ฮณ : Sub ฮ ฮ} โ num n [ ฮณ ] โก num n
    isZero[]  : โ{ฮ t ฮ}{ฮณ : Sub ฮ ฮ} โ isZero t [ ฮณ ] โก isZero (t [ ฮณ ])
    +[]       : โ{ฮ u v ฮ}{ฮณ : Sub ฮ ฮ} โ (u +o v) [ ฮณ ] โก (u [ ฮณ ]) +o (v [ ฮณ ])

    lam       : โ{ฮ A B} โ Tm (ฮ โน A) B โ Tm ฮ (A โ B)
    _$_       : โ{ฮ A B} โ Tm ฮ (A โ B) โ Tm ฮ A โ Tm ฮ B
    โฮฒ        : โ{ฮ A B}{t : Tm (ฮ โน A) B}{u : Tm ฮ A} โ lam t $ u โก t [ id ,o u ]
    โฮท        : โ{ฮ A B}{t : Tm ฮ (A โ B)} โ lam (t [ p ] $ q) โก t
    lam[]     : โ{ฮ A B}{t : Tm (ฮ โน A) B}{ฮ}{ฮณ : Sub ฮ ฮ} โ
                (lam t) [ ฮณ ] โก lam (t [ ฮณ โ p ,o q ])
    $[]       : โ{ฮ A B}{t : Tm ฮ (A โ B)}{u : Tm ฮ A}{ฮ}{ฮณ : Sub ฮ ฮ} โ
                (t $ u) [ ฮณ ] โก t [ ฮณ ] $ u [ ฮณ ]

  def : โ{ฮ A B} โ Tm ฮ A โ Tm (ฮ โน A) B โ Tm ฮ B
  def t u = u [ id ,o t ]

  v0 : {ฮ : Con} โ {A : Ty} โ Tm (ฮ โน A) A
  v0 = q
  v1 : {ฮ : Con} โ {A B : Ty} โ Tm (ฮ โน A โน B) A
  v1 = q [ p ]
  v2 : {ฮ : Con} โ {A B C : Ty} โ Tm (ฮ โน A โน B โน C) A
  v2 = q [ p โ p ]
  v3 : {ฮ : Con} โ {A B C D : Ty} โ Tm (ฮ โน A โน B โน C โน D) A
  v3 = q [ p โ p โ p ]

  ,โ : โ{ฮ ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A}{ฮด : Sub ฮ ฮ} โ
    (ฮณ ,o t) โ ฮด โก ฮณ โ ฮด ,o t [ ฮด ]
  ,โ {ฮ}{ฮ}{ฮ}{A}{ฮณ}{t}{ฮด} =
    (ฮณ ,o t) โ ฮด
      โกโจ โนฮท โปยน โฉ
    (p โ ((ฮณ ,o t) โ ฮด) ,o q [ (ฮณ ,o t) โ ฮด ])
      โกโจ cong (ฮป w โ ฯโ w ,o ฯโ w) (ass โปยน ,ร= [โ]) โฉ
    ((p โ (ฮณ ,o t)) โ ฮด ,o q [ ฮณ ,o t ] [ ฮด ])
      โกโจ cong (ฮป w โ ฯโ w ,o ฯโ w) (cong (_โ ฮด) โนฮฒโ ,ร= cong (_[ ฮด ]) โนฮฒโ) โฉ
    ฮณ โ ฮด ,o t [ ฮด ]
      โ

record Model {i j k l} : Set (lsuc (i โ j โ k โ l)) where
  infixl 6 _โ_
  infixl 6 _[_]
  infixl 5 _โน_
  infixl 5 _,o_
  infixr 5 _โ_
  infixl 5 _$_
  infixl 7 _+o_
  
  field
    Con       : Set i
    Sub       : Con โ Con โ Set j
    _โ_       : โ{ฮ ฮ ฮ} โ Sub ฮ ฮ โ Sub ฮ ฮ โ Sub ฮ ฮ
    ass       : โ{ฮ ฮ ฮ ฮ}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ}{ฮธ : Sub ฮ ฮ} โ
                (ฮณ โ ฮด) โ ฮธ โก ฮณ โ (ฮด โ ฮธ)
    id        : โ{ฮ} โ Sub ฮ ฮ
    idl       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ id โ ฮณ โก ฮณ
    idr       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฮณ โ id โก ฮณ

    โ         : Con
    ฮต         : โ{ฮ} โ Sub ฮ โ
    โฮท        : โ{ฮ}{ฯ : Sub ฮ โ} โ ฯ โก ฮต

    Ty        : Set k

    Tm        : Con โ Ty โ Set l
    _[_]      : โ{ฮ ฮ A} โ Tm ฮ A โ Sub ฮ ฮ โ Tm ฮ A
    [โ]       : โ{ฮ ฮ ฮ A}{t : Tm ฮ A}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ} โ
                t [ ฮณ โ ฮด ] โก t [ ฮณ ] [ ฮด ]
    [id]      : โ{ฮ A}{t : Tm ฮ A} โ t [ id ] โก t
    _โน_       : Con โ Ty โ Con
    _,o_      : โ{ฮ ฮ A} โ Sub ฮ ฮ โ Tm ฮ A โ Sub ฮ (ฮ โน A)
    p         : โ{ฮ A} โ Sub (ฮ โน A) ฮ
    q         : โ{ฮ A} โ Tm (ฮ โน A) A
    โนฮฒโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ p โ (ฮณ ,o t) โก ฮณ
    โนฮฒโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ q [ ฮณ ,o t ] โก t
    โนฮท        : โ{ฮ ฮ A}{ฮณa : Sub ฮ (ฮ โน A)} โ p โ ฮณa ,o q [ ฮณa ] โก ฮณa

    Bool      : Ty
    true      : โ{ฮ} โ Tm ฮ Bool
    false     : โ{ฮ} โ Tm ฮ Bool
    ite       : โ{ฮ A} โ Tm ฮ Bool โ Tm ฮ A โ Tm ฮ A โ Tm ฮ A
    iteฮฒโ     : โ{ฮ A u v} โ ite {ฮ}{A} true u v โก u
    iteฮฒโ     : โ{ฮ A u v} โ ite {ฮ}{A} false u v โก v
    true[]    : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ true [ ฮณ ] โก true
    false[]   : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ false [ ฮณ ] โก false
    ite[]     : โ{ฮ A t u v ฮ}{ฮณ : Sub ฮ ฮ} โ (ite {ฮ}{A} t u v) [ ฮณ ] โก ite (t [ ฮณ ]) (u [ ฮณ ]) (v [ ฮณ ])

    Nat       : Ty
    num       : โ{ฮ} โ โ โ Tm ฮ Nat
    isZero    : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Bool
    _+o_      : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Nat โ Tm ฮ Nat
    isZeroฮฒโ  : โ{ฮ} โ isZero (num {ฮ} 0) โก true
    isZeroฮฒโ  : โ{ฮ n} โ isZero (num {ฮ} (1 + n)) โก false
    +ฮฒ        : โ{ฮ m n} โ num {ฮ} m +o num n โก num (m + n)
    num[]     : โ{ฮ n ฮ}{ฮณ : Sub ฮ ฮ} โ num n [ ฮณ ] โก num n
    isZero[]  : โ{ฮ t ฮ}{ฮณ : Sub ฮ ฮ} โ isZero t [ ฮณ ] โก isZero (t [ ฮณ ])
    +[]       : โ{ฮ u v ฮ}{ฮณ : Sub ฮ ฮ} โ (u +o v) [ ฮณ ] โก (u [ ฮณ ]) +o (v [ ฮณ ])
    
    _โ_       : Ty โ Ty โ Ty
    lam       : โ{ฮ A B} โ Tm (ฮ โน A) B โ Tm ฮ (A โ B)
    _$_       : โ{ฮ A B} โ Tm ฮ (A โ B) โ Tm ฮ A โ Tm ฮ B
    โฮฒ        : โ{ฮ A B}{t : Tm (ฮ โน A) B}{u : Tm ฮ A} โ lam t $ u โก t [ id ,o u ]
    โฮท        : โ{ฮ A B}{t : Tm ฮ (A โ B)} โ lam (t [ p ] $ q) โก t
    lam[]     : โ{ฮ A B}{t : Tm (ฮ โน A) B}{ฮ}{ฮณ : Sub ฮ ฮ} โ
                (lam t) [ ฮณ ] โก lam (t [ ฮณ โ p ,o q ])
    $[]       : โ{ฮ A B}{t : Tm ฮ (A โ B)}{u : Tm ฮ A}{ฮ}{ฮณ : Sub ฮ ฮ} โ
                (t $ u) [ ฮณ ] โก t [ ฮณ ] $ u [ ฮณ ]
                
  def : โ{ฮ A B} โ Tm ฮ A โ Tm (ฮ โน A) B โ Tm ฮ B
  def t u = u [ id ,o t ]
  v0 : โ{ฮ A}        โ Tm (ฮ โน A) A
  v0 = q
  v1 : โ{ฮ A B}      โ Tm (ฮ โน A โน B) A
  v1 = q [ p ]
  v2 : โ{ฮ A B C}    โ Tm (ฮ โน A โน B โน C) A
  v2 = q [ p โ p ]
  v3 : โ{ฮ A B C D}  โ Tm (ฮ โน A โน B โน C โน D) A
  v3 = q [ p โ p โ p ]
  โนฮท' : โ{ฮ A} โ p ,o q โก id {ฮ โน A}
  โนฮท' {ฮ}{A} =
    p ,o q
      โกโจ cong (ฮป w โ ฯโ w ,o ฯโ w) (idr ,ร= [id]) โปยน โฉ
    p โ id ,o q [ id ]
      โกโจ โนฮท โฉ
    id
      โ

  ,โ : โ{ฮ ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A}{ฮด : Sub ฮ ฮ} โ
    (ฮณ ,o t) โ ฮด โก ฮณ โ ฮด ,o t [ ฮด ]
  ,โ {ฮ}{ฮ}{ฮ}{A}{ฮณ}{t}{ฮด} =
    (ฮณ ,o t) โ ฮด
      โกโจ โนฮท โปยน โฉ
    (p โ ((ฮณ ,o t) โ ฮด) ,o q [ (ฮณ ,o t) โ ฮด ])
      โกโจ cong (ฮป w โ ฯโ w ,o ฯโ w) (ass โปยน ,ร= [โ]) โฉ
    ((p โ (ฮณ ,o t)) โ ฮด ,o q [ ฮณ ,o t ] [ ฮด ])
      โกโจ cong (ฮป w โ ฯโ w ,o ฯโ w)
           (cong (_โ ฮด) โนฮฒโ ,ร= cong (_[ ฮด ]) โนฮฒโ) โฉ
    ฮณ โ ฮด ,o t [ ฮด ]
      โ

  ^โ : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ}{A}{ฮ}{ฮด : Sub ฮ ฮ}{t : Tm ฮ A} โ
    (ฮณ โ p ,o q) โ (ฮด ,o t) โก (ฮณ โ ฮด ,o t)
  ^โ {ฮ}{ฮ}{ฮณ}{A}{ฮ}{ฮด}{t} =
    (ฮณ โ p ,o q) โ (ฮด ,o t)
      โกโจ ,โ โฉ
    (ฮณ โ p โ (ฮด ,o t) ,o q [ ฮด ,o t ])
      โกโจ cong (ฮป x โ (x ,o q [ ฮด ,o t ])) ass โฉ
    (ฮณ โ (p โ (ฮด ,o t)) ,o q [ ฮด ,o t ])
      โกโจ cong (ฮป x โ (ฮณ โ x ,o q [ ฮด ,o t ])) โนฮฒโ โฉ
    (ฮณ โ ฮด ,o q [ ฮด ,o t ])
      โกโจ cong (ฮป x โ ฮณ โ ฮด ,o x) โนฮฒโ โฉ
    (ฮณ โ ฮด ,o t)
      โ

  โฆ_โงT : I.Ty โ Ty
  โฆ I.Nat โงT = Nat
  โฆ I.Bool โงT = Bool
  โฆ A I.โ B โงT = โฆ A โงT โ โฆ B โงT

  โฆ_โงC : I.Con โ Con
  โฆ I.โ โงC = โ
  โฆ ฮ I.โน A โงC = โฆ ฮ โงC โน โฆ A โงT

  postulate
    โฆ_โงS      : โ{ฮ ฮ} โ I.Sub ฮ ฮ โ Sub โฆ ฮ โงC โฆ ฮ โงC
    โฆ_โงt      : โ{ฮ A} โ I.Tm  ฮ A โ Tm  โฆ ฮ โงC โฆ A โงT
    โฆโโง       : โ{ฮ ฮ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ} โ
                         โฆ ฮณ I.โ ฮด โงS     โ โฆ ฮณ โงS โ โฆ ฮด โงS
    โฆidโง      : โ{ฮ} โ   โฆ I.id {ฮ} โงS    โ id
    โฆฮตโง       : โ{ฮ} โ   โฆ I.ฮต {ฮ} โงS     โ ฮต
    โฆ[]โง      : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ t I.[ ฮณ ] โงt   โ โฆ t โงt [ โฆ ฮณ โงS ]
    โฆ,โง       : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ ฮณ I.,o t โงS    โ โฆ ฮณ โงS ,o โฆ t โงt
    โฆpโง       : โ{ฮ A} โ โฆ I.p {ฮ} {A} โงS โ p
    โฆqโง       : โ{ฮ A} โ โฆ I.q {ฮ} {A} โงt โ q
    {-# REWRITE โฆโโง โฆidโง โฆฮตโง โฆ[]โง โฆ,โง โฆpโง โฆqโง #-}

    โฆtrueโง    : โ{ฮ} โ   โฆ I.true {ฮ} โงt  โ true
    โฆfalseโง   : โ{ฮ} โ   โฆ I.false {ฮ} โงt โ false
    โฆiteโง     : โ{ฮ A}{t : I.Tm ฮ I.Bool}{u v : I.Tm ฮ A} โ
                         โฆ I.ite t u v โงt โ ite โฆ t โงt โฆ u โงt โฆ v โงt
    {-# REWRITE โฆtrueโง โฆfalseโง โฆiteโง #-}

    โฆnumโง     : โ{ฮ n} โ โฆ I.num {ฮ} n โงt โ num n
    โฆisZeroโง  : โ{ฮ}{t : I.Tm ฮ I.Nat} โ
                         โฆ I.isZero t โงt  โ isZero โฆ t โงt
    โฆ+โง       : โ{ฮ}{u v : I.Tm ฮ I.Nat} โ 
                         โฆ u I.+o v โงt    โ โฆ u โงt +o โฆ v โงt
    {-# REWRITE โฆnumโง โฆisZeroโง โฆ+โง #-}

    โฆlamโง     : โ{ฮ A B}{t : I.Tm (ฮ I.โน A) B} โ
                         โฆ I.lam t โงt    โ lam โฆ t โงt
    โฆ$โง       : โ{ฮ A B}{t : I.Tm ฮ (A I.โ B)}{u : I.Tm ฮ A} โ
                         โฆ t I.$ u โงt     โ โฆ t โงt $ โฆ u โงt
    {-# REWRITE โฆlamโง โฆ$โง #-}

record DepModel {i j k l} : Set (lsuc (i โ j โ k โ l)) where
  infixl 6 _โโ_
  infixl 6 _[_]โ
  infixl 5 _โนโ_
  infixl 5 _,oโ_
  infixr 5 _โโ_
  infixl 5 _$โ_
  infixl 7 _+oโ_

  field
    Conโ       : I.Con โ Set i
    Subโ       : โ{ฮ} โ Conโ ฮ โ โ{ฮ} โ Conโ ฮ โ I.Sub ฮ ฮ โ Set j
    _โโ_       : โ{ฮ ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ} โ 
                 Subโ ฮโ ฮโ ฮณ โ Subโ ฮโ ฮโ ฮด โ Subโ ฮโ ฮโ (ฮณ I.โ ฮด)
    assโ       : โ{ฮ ฮ ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}
                 {ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ}{ฮธ : I.Sub ฮ ฮ}
                 {ฮณโ : Subโ ฮโ ฮโ ฮณ}{ฮดโ : Subโ ฮโ ฮโ ฮด}{ฮธโ : Subโ ฮโ ฮโ ฮธ} โ
                 (Subโ ฮโ ฮโ ~) I.ass ((ฮณโ โโ ฮดโ) โโ ฮธโ) (ฮณโ โโ (ฮดโ โโ ฮธโ))
    idโ        : โ{ฮ}{ฮโ : Conโ ฮ} โ Subโ ฮโ ฮโ (I.id {ฮ})
    idlโ       : โ{ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ (Subโ ฮโ ฮโ ~) I.idl (idโ โโ ฮณโ) ฮณโ
    idrโ       : โ{ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ (Subโ ฮโ ฮโ ~) I.idr (ฮณโ โโ idโ) ฮณโ

    โโ         : Conโ I.โ
    ฮตโ         : โ{ฮ}{ฮโ : Conโ ฮ} โ Subโ ฮโ โโ (I.ฮต {ฮ})
    โฮทโ        : โ{ฮ}{ฮโ : Conโ ฮ}{ฯ : I.Sub ฮ I.โ}{ฯโ : Subโ ฮโ โโ ฯ} โ (Subโ ฮโ โโ ~) I.โฮท ฯโ ฮตโ

    Tyโ        : I.Ty โ Set k

    Tmโ        : โ{ฮ} โ Conโ ฮ โ โ{A} โ Tyโ A โ I.Tm ฮ A โ Set l
    _[_]โ      : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{ฮณ : I.Sub ฮ ฮ} โ Tmโ ฮโ Aโ t โ Subโ ฮโ ฮโ ฮณ โ Tmโ ฮโ Aโ (t I.[ ฮณ ])
    [โ]โ       : โ{ฮ ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ}
                 {tโ : Tmโ ฮโ Aโ t}{ฮณโ : Subโ ฮโ ฮโ ฮณ}{ฮดโ : Subโ ฮโ ฮโ ฮด} โ
                (Tmโ ฮโ Aโ ~) I.[โ] (tโ [ ฮณโ โโ ฮดโ ]โ) (tโ [ ฮณโ ]โ [ ฮดโ ]โ)
    [id]โ      : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{tโ : Tmโ ฮโ Aโ t} โ (Tmโ ฮโ Aโ ~) I.[id] (tโ [ idโ ]โ) tโ
    _โนโ_       : โ{ฮ A} โ Conโ ฮ โ Tyโ A โ Conโ (ฮ I.โน A)
    _,oโ_      : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{ฮณ : I.Sub ฮ ฮ} โ Subโ ฮโ ฮโ ฮณ โ Tmโ ฮโ Aโ t โ Subโ ฮโ (ฮโ โนโ Aโ) (ฮณ I.,o t)
    pโ         : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A} โ Subโ (ฮโ โนโ Aโ) ฮโ (I.p {ฮ}{A})
    qโ         : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A} โ Tmโ (ฮโ โนโ Aโ) Aโ (I.q {ฮ}{A})
    โนฮฒโโ       : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A}{ฮณโ : Subโ ฮโ ฮโ ฮณ}{tโ : Tmโ ฮโ Aโ t} โ 
                (Subโ ฮโ ฮโ ~) I.โนฮฒโ (pโ โโ (ฮณโ ,oโ tโ)) ฮณโ
    โนฮฒโโ       : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A}{ฮณโ : Subโ ฮโ ฮโ ฮณ}{tโ : Tmโ ฮโ Aโ t} โ
                (Tmโ ฮโ Aโ ~) I.โนฮฒโ (qโ [ ฮณโ ,oโ tโ ]โ) tโ
    โนฮทโ        : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{ฮณa : I.Sub ฮ (ฮ I.โน A)}{ฮณaโ : Subโ ฮโ {ฮ I.โน A} (ฮโ โนโ Aโ) ฮณa} โ
                (Subโ ฮโ (ฮโ โนโ Aโ) ~) I.โนฮท (pโ โโ ฮณaโ ,oโ qโ [ ฮณaโ ]โ) ฮณaโ

    Boolโ      : Tyโ I.Bool
    trueโ      : โ{ฮ}{ฮโ : Conโ ฮ} โ Tmโ ฮโ Boolโ (I.true {ฮ})
    falseโ     : โ{ฮ}{ฮโ : Conโ ฮ} โ Tmโ ฮโ Boolโ (I.false {ฮ})
    iteโ       : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ I.Bool}{u v : I.Tm ฮ A} โ Tmโ ฮโ Boolโ t โ Tmโ ฮโ Aโ u โ Tmโ ฮโ Aโ v โ Tmโ ฮโ Aโ (I.ite t u v)
    iteฮฒโโ     : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{u v : I.Tm ฮ A}{uโ : Tmโ ฮโ Aโ u}{vโ : Tmโ ฮโ Aโ v} โ 
                (Tmโ ฮโ Aโ ~) I.iteฮฒโ (iteโ trueโ uโ vโ) uโ
    iteฮฒโโ     : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{u v : I.Tm ฮ A}{uโ : Tmโ ฮโ Aโ u}{vโ : Tmโ ฮโ Aโ v} โ
                (Tmโ ฮโ Aโ ~) I.iteฮฒโ (iteโ falseโ uโ vโ) vโ
    true[]โ    : โ{ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ (Tmโ ฮโ Boolโ ~) I.true[] (trueโ [ ฮณโ ]โ) trueโ
    false[]โ   : โ{ฮ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ (Tmโ ฮโ Boolโ ~) I.false[] (falseโ [ ฮณโ ]โ) falseโ
    ite[]โ     : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ I.Bool}{u v : I.Tm ฮ A}{tโ : Tmโ ฮโ Boolโ t}{uโ : Tmโ ฮโ Aโ u}{vโ : Tmโ ฮโ Aโ v}
                {ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ
                (Tmโ ฮโ Aโ ~) I.ite[] ((iteโ tโ uโ vโ) [ ฮณโ ]โ) (iteโ (tโ [ ฮณโ ]โ) (uโ [ ฮณโ ]โ) (vโ [ ฮณโ ]โ))

    Natโ       : Tyโ I.Nat
    numโ       : โ{ฮ}{ฮโ : Conโ ฮ}(n : โ) โ Tmโ ฮโ Natโ (I.num {ฮ} n)
    isZeroโ    : โ{ฮ}{ฮโ : Conโ ฮ}{t : I.Tm ฮ I.Nat} โ Tmโ ฮโ Natโ t โ Tmโ ฮโ Boolโ (I.isZero t)
    _+oโ_      : โ{ฮ}{ฮโ : Conโ ฮ}{u v : I.Tm ฮ I.Nat} โ Tmโ ฮโ Natโ u โ Tmโ ฮโ Natโ v โ Tmโ ฮโ Natโ (u I.+o v)
    isZeroฮฒโโ  : โ{ฮ}{ฮโ : Conโ ฮ} โ (Tmโ ฮโ Boolโ ~) I.isZeroฮฒโ (isZeroโ (numโ {ฮ}{ฮโ} 0)) trueโ
    isZeroฮฒโโ  : โ{ฮ n}{ฮโ : Conโ ฮ} โ (Tmโ ฮโ Boolโ ~) I.isZeroฮฒโ (isZeroโ (numโ {ฮ}{ฮโ} (1 + n))) falseโ
    +ฮฒโ        : โ{ฮ m n}{ฮโ : Conโ ฮ} โ (Tmโ ฮโ Natโ ~) I.+ฮฒ (numโ {ฮ}{ฮโ} m +oโ numโ n) (numโ (m + n))
    num[]โ     : โ{ฮ n ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ (Tmโ ฮโ Natโ ~) I.num[] (numโ n [ ฮณโ ]โ) (numโ n)
    isZero[]โ  : โ{ฮ}{ฮโ : Conโ ฮ}{t : I.Tm ฮ I.Nat}{tโ : Tmโ ฮโ Natโ t}{ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ
                (Tmโ ฮโ Boolโ ~) I.isZero[] (isZeroโ tโ [ ฮณโ ]โ) (isZeroโ (tโ [ ฮณโ ]โ))
    +[]โ       : โ{ฮ}{ฮโ : Conโ ฮ}{u v : I.Tm ฮ I.Nat}{uโ : Tmโ ฮโ Natโ u}{vโ : Tmโ ฮโ Natโ v}{ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ
                (Tmโ ฮโ Natโ ~) I.+[] ((uโ +oโ vโ) [ ฮณโ ]โ) ((uโ [ ฮณโ ]โ) +oโ (vโ [ ฮณโ ]โ))

    _โโ_       : โ{A B} โ Tyโ A โ Tyโ B โ Tyโ (A I.โ B)
    lamโ       : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm (ฮ I.โน A) B} โ
                  Tmโ {ฮ I.โน A} (ฮโ โนโ Aโ) Bโ t โ Tmโ ฮโ (Aโ โโ Bโ) (I.lam t)
    _$โ_       : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm ฮ (A I.โ B)}{u : I.Tm ฮ A} โ
                  Tmโ {ฮ} ฮโ {A I.โ B} (Aโ โโ Bโ) t โ Tmโ ฮโ Aโ u โ Tmโ ฮโ Bโ (t I.$ u)
    โฮฒโ        : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm (ฮ I.โน A) B}{u : I.Tm ฮ A}{tโ : Tmโ (ฮโ โนโ Aโ) Bโ t}{uโ : Tmโ ฮโ Aโ u} โ
                  (Tmโ ฮโ Bโ ~) I.โฮฒ (lamโ tโ $โ uโ) (tโ [ idโ ,oโ uโ ]โ)
    โฮทโ        : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm ฮ (A I.โ B)}{tโ : Tmโ ฮโ {A I.โ B} (Aโ โโ Bโ) t} โ
                  (Tmโ ฮโ (Aโ โโ Bโ) ~) I.โฮท (lamโ (tโ [ pโ ]โ $โ qโ)) tโ
    lam[]โ     : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm (ฮ I.โน A) B}{tโ : Tmโ (ฮโ โนโ Aโ) Bโ t}
                {ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ
                (Tmโ ฮโ (Aโ โโ Bโ) ~) I.lam[] ((lamโ tโ) [ ฮณโ ]โ) (lamโ (tโ [ ฮณโ โโ pโ ,oโ qโ ]โ))
    $[]โ       : โ{ฮ A B}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{Bโ : Tyโ B}{t : I.Tm ฮ (A I.โ B)}{u : I.Tm ฮ A}{tโ : Tmโ ฮโ {A I.โ B} (Aโ โโ Bโ) t}{uโ : Tmโ ฮโ Aโ u}
                {ฮ}{ฮโ : Conโ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮณโ : Subโ ฮโ ฮโ ฮณ} โ
                (Tmโ ฮโ Bโ ~) I.$[] ((tโ $โ uโ) [ ฮณโ ]โ) (tโ [ ฮณโ ]โ $โ uโ [ ฮณโ ]โ)

  โฆ_โงT : (A : I.Ty) โ Tyโ A
  โฆ I.Nat โงT = Natโ
  โฆ I.Bool โงT = Boolโ
  โฆ A I.โ B โงT = โฆ A โงT โโ โฆ B โงT

  โฆ_โงC : (ฮ : I.Con) โ Conโ ฮ
  โฆ I.โ โงC = โโ
  โฆ ฮ I.โน A โงC = โฆ ฮ โงC โนโ โฆ A โงT

  postulate
    โฆ_โงS      : โ{ฮ ฮ}(ฮณ : I.Sub ฮ ฮ) โ Subโ โฆ ฮ โงC  โฆ ฮ โงC  ฮณ
    โฆ_โงt      : โ{ฮ A}(t : I.Tm ฮ A)  โ Tmโ  โฆ ฮ โงC  โฆ A โงT  t
    โฆโโง       : โ{ฮ ฮ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ} โ 
                         โฆ ฮณ I.โ ฮด โงS     โ โฆ ฮณ โงS โโ โฆ ฮด โงS
    โฆidโง      : โ{ฮ} โ   โฆ I.id {ฮ} โงS    โ idโ
    โฆฮตโง       : โ{ฮ} โ   โฆ I.ฮต {ฮ} โงS     โ ฮตโ
    โฆ[]โง      : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ t I.[ ฮณ ] โงt   โ โฆ t โงt [ โฆ ฮณ โงS ]โ
    โฆ,โง       : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ ฮณ I.,o t โงS    โ โฆ ฮณ โงS ,oโ โฆ t โงt
    โฆpโง       : โ{ฮ A} โ โฆ I.p {ฮ}{A} โงS  โ pโ
    โฆqโง       : โ{ฮ A} โ โฆ I.q {ฮ}{A} โงt  โ qโ
    {-# REWRITE โฆโโง โฆidโง โฆฮตโง โฆ[]โง โฆ,โง โฆpโง โฆqโง #-}

    โฆtrueโง    : โ{ฮ} โ   โฆ I.true {ฮ} โงt  โ trueโ
    โฆfalseโง   : โ{ฮ} โ   โฆ I.false {ฮ} โงt โ falseโ
    โฆiteโง     : โ{ฮ A}{t : I.Tm ฮ I.Bool}{u v : I.Tm ฮ A} โ
                         โฆ I.ite t u v โงt โ iteโ โฆ t โงt โฆ u โงt โฆ v โงt
    {-# REWRITE โฆtrueโง โฆfalseโง โฆiteโง #-}

    โฆnumโง     : โ{ฮ n} โ โฆ I.num {ฮ} n โงt โ numโ n
    โฆisZeroโง  : โ{ฮ}{t : I.Tm ฮ I.Nat} โ
                         โฆ I.isZero t โงt  โ isZeroโ โฆ t โงt
    โฆ+โง       : โ{ฮ}{u v : I.Tm ฮ I.Nat} โ
                         โฆ u I.+o v โงt    โ โฆ u โงt +oโ โฆ v โงt
    {-# REWRITE โฆnumโง โฆisZeroโง โฆ+โง #-}

    โฆlamโง     : โ{ฮ A B}{t : I.Tm (ฮ I.โน A) B} โ
                         โฆ I.lam t โงt     โ lamโ โฆ t โงt
    โฆ$โง       : โ{ฮ A B}{t : I.Tm ฮ (A I.โ B)}{u : I.Tm ฮ A} โ
                         โฆ t I.$ u โงt     โ โฆ t โงt $โ โฆ u โงt
    {-# REWRITE โฆlamโง โฆ$โง #-}

module โvsโ {i j k l}(M : Model {i}{j}{k}{l})(A B : Model.Ty M) where
  open Model M
  EXT = ฮฃsp (โ ฮ โ Tm ฮ A โ Tm ฮ B) ฮป f โ โ{ฮ ฮ ฮณ a} โ f ฮ a [ ฮณ ] โก f ฮ (a [ ฮณ ])
  INT = Tm โ (A โ B)
  toINT : EXT โ INT
  toINT f = lam (ฯโ f (โ โน A) q)
  toEXT : INT โ EXT
  toEXT t = (ฮป ฮ a โ t [ ฮต ] $ a) , ฮป {ฮ}{ฮ}{ฮณ}{a} โ 
    (t [ ฮต ] $ a) [ ฮณ ]
                             โกโจ $[] โฉ
    t [ ฮต ] [ ฮณ ] $ a [ ฮณ ]
                             โกโจ cong (_$ a [ ฮณ ]) ([โ] โปยน) โฉ
    t [ ฮต โ ฮณ ] $ a [ ฮณ ]
                             โกโจ cong (ฮป x โ t [ x ] $ a [ ฮณ ]) โฮท โฉ
    t [ ฮต ] $ a [ ฮณ ]
                             โ
  extRoundtrip : (f : EXT) โ toEXT (toINT f) โก f
  extRoundtrip f = (funext ฮป ฮ โ funext ฮป a โ
    lam (ฯโ f (โ โน A) q) [ ฮต ] $ a
                                                  โกโจ cong (_$ a) lam[] โฉ
    lam (ฯโ f (โ โน A) q [ ฮต โ p ,o q ]) $ a
                                                  โกโจ cong (ฮป x โ lam x $ a) (ฯโ f) โฉ
    lam (ฯโ f (ฮ โน A) (q [ ฮต โ p ,o q ])) $ a
                                                  โกโจ cong (ฮป x โ lam (ฯโ f (ฮ โน A) x) $ a) โนฮฒโ โฉ
    lam (ฯโ f (ฮ โน A) q) $ a
                                                  โกโจ โฮฒ โฉ
    ฯโ f (ฮ โน A) q [ id ,o a ]
                                                  โกโจ ฯโ f โฉ
    ฯโ f ฮ (q [ id ,o a ])
                                                  โกโจ cong (ฯโ f ฮ) โนฮฒโ โฉ
    ฯโ f ฮ a
                                                  โ) ,=-
  intRoundtrip : (t : INT) โ toINT (toEXT t) โก t
  intRoundtrip t = cong (ฮป ฮณ โ lam (t [ ฮณ ] $ q)) (โฮท โปยน) โพ โฮท

St : Model
St = record
  { Con       = Set
  ; Sub       = ฮป ฮ ฮ โ ฮ โ ฮ
  ; _โ_       = ฮป ฮณ ฮด ฮธ* โ ฮณ (ฮด ฮธ*)
  ; ass       = ฮป {ฮ}{ฮ}{ฮ}{ฮ} โ refl {A = ฮ โ ฮ}
  ; id        = ฮป ฮณ* โ ฮณ*
  ; idl       = ฮป {ฮ}{ฮ} โ refl {A = ฮ โ ฮ}
  ; idr       = ฮป {ฮ}{ฮ} โ refl {A = ฮ โ ฮ}
  
  ; โ         = Lift โค
  ; ฮต         = _
  ; โฮท        = ฮป {ฮ}{ฯ} โ refl {A = ฮ โ Lift โค}
  
  ; Ty        = Set
  
  ; Tm        = ฮป ฮ A โ ฮ โ A
  ; _[_]      = ฮป a ฮณ ฮด* โ a (ฮณ ฮด*) 
  ; [โ]       = ฮป {ฮ}{ฮ}{ฮ}{A} โ refl {A = ฮ โ A}
  ; [id]      = ฮป {ฮ}{A}{a} โ refl {A = ฮ โ A}
  ; _โน_       = _ร_
  ; _,o_      = ฮป ฮณ t ฮด* โ ฮณ ฮด* , t ฮด*
  ; p         = ฯโ
  ; q         = ฯโ
  ; โนฮฒโ       = ฮป {ฮ}{ฮ} โ refl {A = ฮ โ ฮ}
  ; โนฮฒโ       = ฮป {ฮ}{ฮ}{A} โ refl {A = ฮ โ A}
  ; โนฮท        = ฮป {ฮ}{ฮ}{A} โ refl {A = ฮ โ ฮ ร A}

  ; Bool      = ๐
  ; true      = ฮป _ โ tt
  ; false     = ฮป _ โ ff
  ; ite       = ฮป t u v ฮณ* โ if t ฮณ* then u ฮณ* else v ฮณ*
  ; iteฮฒโ     = refl
  ; iteฮฒโ     = refl
  ; true[]    = refl
  ; false[]   = refl
  ; ite[]     = refl

  ; Nat       = โ
  ; num       = ฮป n ฮณ* โ n
  ; isZero    = ฮป t ฮณ* โ iteโ tt (ฮป _ โ ff) (t ฮณ*)
  ; _+o_      = ฮป m n ฮณ* โ m ฮณ* + n ฮณ*
  ; isZeroฮฒโ  = refl
  ; isZeroฮฒโ  = refl
  ; +ฮฒ        = refl
  ; num[]     = refl
  ; isZero[]  = refl
  ; +[]       = refl
  
  ; _โ_       = ฮป A B โ A โ B
  ; lam       = ฮป t ฮณ* ฮฑ* โ t (ฮณ* , ฮฑ*)
  ; _$_       = ฮป t u ฮณ* โ t ฮณ* (u ฮณ*)
  ; โฮฒ        = refl
  ; โฮท        = refl
  ; lam[]     = refl
  ; $[]       = refl
  }
module St = Model St

open I public

data Var : Con โ Ty โ Set where
  vz : โ{ฮ A} โ Var (ฮ โน A) A
  vs : โ{ฮ A B} โ Var ฮ A โ Var (ฮ โน B) A

data Ne (ฮ : Con) : Ty โ Set
data Nf (ฮ : Con) : Ty โ Set

data Ne ฮ where
  var       : โ{A} โ Var ฮ A โ Ne ฮ A
  _$Ne_     : โ{A B} โ Ne ฮ (A โ B) โ Nf ฮ A โ Ne ฮ B
  iteNe     : โ{A} โ Ne ฮ Bool โ Nf ฮ A โ Nf ฮ A โ Ne ฮ A
  isZeroNe  : Ne ฮ Nat โ Ne ฮ Bool
  _+NeNe_   : Ne ฮ Nat โ Ne ฮ Nat โ Ne ฮ Nat
  _+NeNf_   : Ne ฮ Nat โ โ โ Ne ฮ Nat
  _+NfNe_   : โ โ Ne ฮ Nat โ Ne ฮ Nat
  
data Nf ฮ where
  neuBool   : Ne ฮ Bool โ Nf ฮ Bool
  neuNat    : Ne ฮ Nat โ Nf ฮ Nat
  lamNf     : โ{A B} โ Nf (ฮ โน A) B โ Nf ฮ (A โ B)
  trueNf    : Nf ฮ Bool
  falseNf   : Nf ฮ Bool
  numNf     : (n : โ) โ Nf ฮ Nat

โ_โV : โ{ฮ A} โ Var ฮ A โ Tm ฮ A
โ vz โV = q
โ vs x โV = โ x โV [ p ]
โ_โNe : โ{ฮ A} โ Ne ฮ A โ Tm ฮ A
โ_โNf : โ{ฮ A} โ Nf ฮ A โ Tm ฮ A
โ var x โNe = โ x โV
โ t $Ne a โNe = โ t โNe $ โ a โNf
โ iteNe t a a' โNe = ite โ t โNe โ a โNf โ a' โNf
โ isZeroNe t โNe = isZero โ t โNe
โ t +NeNe t' โNe = โ t โNe +o โ t' โNe
โ t +NeNf n' โNe = โ t โNe +o num n'
โ n +NfNe t' โNe = num n +o โ t' โNe
โ neuBool t โNf = โ t โNe
โ neuNat t โNf = โ t โNe
โ lamNf t โNf = lam โ t โNf
โ trueNf โNf = true
โ falseNf โNf = false
โ numNf n โNf = num n

