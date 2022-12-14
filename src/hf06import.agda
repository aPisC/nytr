{-# OPTIONS --prop --rewriting #-}

module hf06import where

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
  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty

  data Con  : Set where
    โ       : Con              -- \di2
    _โน_     : Con โ Ty โ Con   -- \t6

  infixl 6 _โ_
  infixl 6 _[_]
  infixl 5 _โน_
  infixl 5 _,o_
  infixl 7 _+o_

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
    isZero[]  : โ{ฮ t ฮ}{ฮณ : Sub ฮ ฮ} โ (isZero t) [ ฮณ ] โก isZero (t [ ฮณ ])
    +[]       : โ{ฮ u v ฮ}{ฮณ : Sub ฮ ฮ} โ (u +o v) [ ฮณ ] โก (u [ ฮณ ]) +o (v [ ฮณ ])

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
  v4 : {ฮ : Con} โ {A B C D E : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E) A
  v4 = q [ p โ p โ p โ p ]
  v5 : {ฮ : Con} โ {A B C D E F : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F) A
  v5 = q [ p โ p โ p โ p โ p ]
  v6 : {ฮ : Con} โ {A B C D E F G : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F โน G) A
  v6 = q [ p โ p โ p โ p โ p โ p ]
  v7 : {ฮ : Con} โ {A B C D E F G H : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F โน G โน H) A
  v7 = q [ p โ p โ p โ p โ p โ p โ p ]

  ,โ : โ{ฮ ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A}{ฮด : Sub ฮ ฮ} โ
    (ฮณ ,o t) โ ฮด โก ฮณ โ ฮด ,o t [ ฮด ]
  ,โ {ฮ}{ฮ}{ฮ}{A}{ฮณ}{t}{ฮด} =
    (ฮณ ,o t) โ ฮด
      โกโจ  โนฮท โปยน โฉ
    (p โ ((ฮณ ,o t) โ ฮด) ,o q [ (ฮณ ,o t) โ ฮด ])
      โกโจ cong {A = Sub ฮ ฮ ร Tm ฮ A} (ฮป w โ ฯโ w ,o ฯโ w) (ass โปยน ,ร= [โ]) โฉ
    ((p โ (ฮณ ,o t)) โ ฮด ,o q [ ฮณ ,o t ] [ ฮด ])
      โกโจ cong {A = Sub ฮ ฮ ร Tm ฮ A} (ฮป w โ ฯโ w ,o ฯโ w)
           (cong (_โ ฮด) โนฮฒโ ,ร= cong (_[ ฮด ]) โนฮฒโ) โฉ
    ฮณ โ ฮด ,o t [ ฮด ]
      โ

record DepModel {i j k l} : Set (lsuc (i โ j โ k โ l)) where
  infixl 6 _โโ_
  infixl 6 _[_]โ
  infixl 5 _โนโ_
  infixl 5 _,oโ_

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

    Tmโ        : โ{ฮ A} โ Conโ ฮ โ Tyโ A โ I.Tm ฮ A โ Set l
    _[_]โ      : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{ฮณ : I.Sub ฮ ฮ} โ Tmโ ฮโ Aโ t โ Subโ ฮโ ฮโ ฮณ โ Tmโ ฮโ Aโ (t I.[ ฮณ ])
    [โ]โ       : โ{ฮ ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ}
                 {tโ : Tmโ ฮโ Aโ t}{ฮณโ : Subโ ฮโ ฮโ ฮณ}{ฮดโ : Subโ ฮโ ฮโ ฮด} โ
                (Tmโ ฮโ Aโ ~) I.[โ] (tโ [ ฮณโ โโ ฮดโ ]โ) (tโ [ ฮณโ ]โ [ ฮดโ ]โ)
    [id]โ      : โ{ฮ A}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{t : I.Tm ฮ A}{tโ : Tmโ ฮโ Aโ t} โ (Tmโ ฮโ Aโ ~) I.[id] (tโ [ idโ ]โ) tโ
    _โนโ_       : โ{ฮ A} โ Conโ ฮ โ Tyโ A โ Conโ (ฮ I.โน A)
    _,oโ_      : โ{ฮ ฮ A}{ฮโ : Conโ ฮ}{ฮโ : Conโ ฮ}{Aโ : Tyโ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ Subโ ฮโ ฮโ ฮณ โ Tmโ ฮโ Aโ t โ Subโ ฮโ (ฮโ โนโ Aโ) (ฮณ I.,o t)
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

  โฆ_โงT : (A : I.Ty) โ Tyโ A
  โฆ I.Nat โงT = Natโ
  โฆ I.Bool โงT = Boolโ

  โฆ_โงC : (ฮ : I.Con) โ Conโ ฮ
  โฆ I.โ โงC = โโ
  โฆ ฮ I.โน A โงC = โฆ ฮ โงC โนโ โฆ A โงT

  postulate
    โฆ_โงs      : โ{ฮ ฮ}(ฮณ : I.Sub ฮ ฮ) โ Subโ โฆ ฮ โงC  โฆ ฮ โงC  ฮณ
    โฆ_โงt      : โ{ฮ A}(t : I.Tm ฮ A)  โ Tmโ  โฆ ฮ โงC  โฆ A โงT  t
    โฆโโง       : โ{ฮ ฮ ฮ}{ฮณ : I.Sub ฮ ฮ}{ฮด : I.Sub ฮ ฮ} โ 
                         โฆ ฮณ I.โ ฮด โงs     โ โฆ ฮณ โงs โโ โฆ ฮด โงs
    โฆidโง      : โ{ฮ} โ   โฆ I.id {ฮ} โงs    โ idโ
    โฆฮตโง       : โ{ฮ} โ   โฆ I.ฮต {ฮ} โงs     โ ฮตโ
    โฆ[]โง      : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ t I.[ ฮณ ] โงt   โ โฆ t โงt [ โฆ ฮณ โงs ]โ
    โฆ,โง       : โ{ฮ ฮ A}{ฮณ : I.Sub ฮ ฮ}{t : I.Tm ฮ A} โ
                         โฆ ฮณ I.,o t โงs    โ โฆ ฮณ โงs ,oโ โฆ t โงt
    โฆpโง       : โ{ฮ A} โ โฆ I.p {ฮ}{A} โงs  โ pโ
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
record Model {i j k l} : Set (lsuc (i โ j โ k โ l)) where
  infixl 6 _โ_
  infixl 6 _[_]
  infixl 5 _โน_
  infixl 5 _,o_
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
  v4 : {ฮ : Con} โ {A B C D E : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E) A
  v4 = q [ p โ p โ p โ p ]
  v5 : {ฮ : Con} โ {A B C D E F : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F) A
  v5 = q [ p โ p โ p โ p โ p ]
  v6 : {ฮ : Con} โ {A B C D E F G : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F โน G) A
  v6 = q [ p โ p โ p โ p โ p โ p ]
  v7 : {ฮ : Con} โ {A B C D E F G H : Ty} โ Tm (ฮ โน A โน B โน C โน D โน E โน F โน G โน H) A
  v7 = q [ p โ p โ p โ p โ p โ p โ p ]
  โนฮท' : โ{ฮ A} โ p ,o q โก id {ฮ โน A}
  โนฮท' {ฮ}{A} =
    p ,o q
      โกโจ cong {A = Sub (ฮ โน A) ฮ ร Tm (ฮ โน A) A} (ฮป w โ ฯโ w ,o ฯโ w) (idr ,ร= [id]) โปยน โฉ
    p โ id ,o q [ id ]
      โกโจ โนฮท โฉ
    id
      โ

  ,โ : โ{ฮ ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A}{ฮด : Sub ฮ ฮ} โ
    (ฮณ ,o t) โ ฮด โก ฮณ โ ฮด ,o t [ ฮด ]
  ,โ {ฮ}{ฮ}{ฮ}{A}{ฮณ}{t}{ฮด} =
    (ฮณ ,o t) โ ฮด
      โกโจ  โนฮท โปยน โฉ
    (p โ ((ฮณ ,o t) โ ฮด) ,o q [ (ฮณ ,o t) โ ฮด ])
      โกโจ cong {A = Sub ฮ ฮ ร Tm ฮ A} (ฮป w โ ฯโ w ,o ฯโ w) (ass โปยน ,ร= [โ]) โฉ
    ((p โ (ฮณ ,o t)) โ ฮด ,o q [ ฮณ ,o t ] [ ฮด ])
      โกโจ cong {A = Sub ฮ ฮ ร Tm ฮ A} (ฮป w โ ฯโ w ,o ฯโ w)
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
  D : DepModel
  D = record
    { Conโ = ฮป _ โ Con
    ; Subโ = ฮป ฮ ฮ _ โ Sub ฮ ฮ
    ; _โโ_ = _โ_
    ; assโ = ฮป where {ฮณ = ฮณ}{ฮด = ฮด}{ฮธ = ฮธ} โ transpconst {B = Sub _ _}{e = I.ass {ฮณ = ฮณ}{ฮด = ฮด}{ฮธ = ฮธ}} โพ ass
    ; idโ = id
    ; idlโ = ฮป where {ฮณ = ฮณ} โ transpconst {B = Sub _ _}{e = I.idl {ฮณ = ฮณ}} โพ idl
    ; idrโ = ฮป where {ฮณ = ฮณ} โ transpconst {B = Sub _ _}{e = I.idr {ฮณ = ฮณ}} โพ idr
    ; โโ = โ
    ; ฮตโ = ฮต
    ; โฮทโ = ฮป where {ฯ = ฯ} โ transpconst {B = Sub _ _}{e = I.โฮท {ฯ = ฯ}} โพ โฮท
    ; Tyโ = ฮป _ โ Ty
    ; Tmโ = ฮป ฮ A _ โ Tm ฮ A
    ; _[_]โ = _[_]
    ; [โ]โ = ฮป where {t = t}{ฮณ}{ฮด} โ transpconst {B = Tm _ _}{e = I.[โ] {t = t}{ฮณ}{ฮด}} โพ [โ]
    ; [id]โ = ฮป where{t = t} โ transpconst {B = Tm _ _}{e = I.[id] {t = t}} โพ [id]
    ; _โนโ_ = _โน_
    ; _,oโ_ = _,o_
    ; pโ = p
    ; qโ = q
    ; โนฮฒโโ = ฮป where {ฮณ = ฮณ}{t} โ transpconst {B = Sub _ _}{e = I.โนฮฒโ {ฮณ = ฮณ}{t}} โพ โนฮฒโ
    ; โนฮฒโโ = ฮป where {ฮณ = ฮณ}{t} โ transpconst {B = Tm _ _}{e = I.โนฮฒโ {ฮณ = ฮณ}{t}} โพ โนฮฒโ
    ; โนฮทโ = ฮป where {ฮณa = ฮณa} โ transpconst {B = Sub _ _}{e = I.โนฮท {ฮณa = ฮณa}} โพ โนฮท
    ; Boolโ = Bool
    ; trueโ = true
    ; falseโ = false
    ; iteโ = ite
    ; iteฮฒโโ = ฮป where {u = u}{v} โ transpconst {B = Tm _ _}{e = I.iteฮฒโ {u = u}{v = v}} โพ iteฮฒโ
    ; iteฮฒโโ = ฮป where {u = u}{v} โ transpconst {B = Tm _ _}{e = I.iteฮฒโ {u = u}{v = v}} โพ iteฮฒโ
    ; true[]โ = transpconst {B = Tm _ _}{e = I.true[]} โพ true[]
    ; false[]โ = transpconst {B = Tm _ _}{e = I.false[]} โพ false[]
    ; ite[]โ = transpconst {B = Tm _ _}{e = I.ite[]} โพ ite[]
    ; Natโ = Nat
    ; numโ = num
    ; isZeroโ = isZero
    ; _+oโ_ = _+o_
    ; isZeroฮฒโโ = transpconst {B = Tm _ _}{e = I.isZeroฮฒโ} โพ isZeroฮฒโ
    ; isZeroฮฒโโ = transpconst {B = Tm _ _}{e = I.isZeroฮฒโ} โพ isZeroฮฒโ
    ; +ฮฒโ = transpconst {B = Tm _ _}{e = I.+ฮฒ} โพ +ฮฒ
    ; num[]โ = transpconst {B = Tm _ _}{e = I.num[]} โพ num[]
    ; isZero[]โ = transpconst {B = Tm _ _}{e = I.isZero[]} โพ isZero[]
    ; +[]โ = transpconst {B = Tm _ _}{e = I.+[]} โพ +[]
    }
  module D = DepModel D

  โฆ_โงT : I.Ty โ Ty
  โฆ_โงT = D.โฆ_โงT

  โฆ_โงC : I.Con โ Con
  โฆ_โงC = D.โฆ_โงC

  โฆ_โงs : โ{ฮ ฮ} โ I.Sub ฮ ฮ โ Sub โฆ ฮ โงC โฆ ฮ โงC
  โฆ_โงs = D.โฆ_โงs
  
  โฆ_โงt : โ{ฮ A} โ I.Tm  ฮ A โ Tm  โฆ ฮ โงC โฆ A โงT
  โฆ_โงt = D.โฆ_โงt

-- could be also called PrimitiveModel or ConstDepModel
record ParaModel {i j k l} : Set (lsuc (i โ j โ k โ l)) where
  infixl 6 _โโ_ _โ_
  infixl 6 _[_]โ _[_]
  infixl 5 _โนโ_ _โน_
  infixl 5 _,oโ_ _,o_

  field
    Conโ       : Set i
  Con          : Set i
  Con          = I.Con ร Conโ
  field
    Subโ       : Con โ Con โ Set j
  Sub          : Con โ Con โ Set j
  Sub ฮ ฮ      = I.Sub (ฯโ ฮ) (ฯโ ฮ) ร Subโ ฮ ฮ
  field
    _โโ_       : โ{ฮ ฮ ฮ} โ Sub ฮ ฮ โ Sub ฮ ฮ โ Subโ ฮ ฮ
  _โ_          : โ{ฮ ฮ ฮ} โ Sub ฮ ฮ โ Sub ฮ ฮ โ Sub ฮ ฮ
  ฮณ โ ฮด        = ฯโ ฮณ I.โ ฯโ ฮด , ฮณ โโ ฮด
  field
    assโ       : โ{ฮ ฮ ฮ ฮ}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ}{ฮธ : Sub ฮ ฮ} โ ฯโ ((ฮณ โ ฮด) โ ฮธ) โก ฯโ (ฮณ โ (ฮด โ ฮธ))
    idโ        : โ{ฮ} โ Subโ ฮ ฮ
  id           : โ{ฮ} โ Sub ฮ ฮ
  id {ฮ}       = I.id {ฯโ ฮ} , idโ {ฮ}
  field  
    idlโ       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (id โ ฮณ) โก ฯโ ฮณ
    idrโ       : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (ฮณ โ id) โก ฯโ ฮณ

    โโ         : Conโ
  โ            : Con
  โ            = I.โ , โโ
  field
    ฮตโ         : โ{ฮ} โ Subโ ฮ โ
  ฮต            : โ{ฮ} โ Sub ฮ โ
  ฮต            = I.ฮต , ฮตโ
  field
    โฮทโ        : โ{ฮ}{ฯ : Sub ฮ โ} โ ฯโ ฯ โก ฯโ (ฮต {ฮ})
    Tyโ        : Set k
  Ty           : Set k
  Ty           = I.Ty ร Tyโ
  field
    Tmโ        : Con โ Ty โ Set l
  Tm           : Con โ Ty โ Set l
  Tm ฮ A       = I.Tm (ฯโ ฮ) (ฯโ A) ร Tmโ ฮ A
  field
    _[_]โ      : โ{ฮ ฮ A} โ Tm ฮ A โ Sub ฮ ฮ โ Tmโ ฮ A
  _[_]         : โ{ฮ ฮ A} โ Tm ฮ A โ Sub ฮ ฮ โ Tm ฮ A
  a [ ฮณ ]      = ฯโ a I.[ ฯโ ฮณ ] , a [ ฮณ ]โ
  field
    [โ]โ       : โ{ฮ ฮ ฮ A}{t : Tm ฮ A}{ฮณ : Sub ฮ ฮ}{ฮด : Sub ฮ ฮ} โ
                 ฯโ (t [ ฮณ โ ฮด ]) โก ฯโ (t [ ฮณ ] [ ฮด ])
    [id]โ      : โ{ฮ A}{t : Tm ฮ A} โ ฯโ (t [ id ]) โก ฯโ t
    _โนโ_       : Con โ Ty โ Conโ
  _โน_          : Con โ Ty โ Con
  ฮ โน A        = ฯโ ฮ I.โน ฯโ A , ฮ โนโ A
  field
    _,oโ_      : โ{ฮ ฮ A} โ Sub ฮ ฮ โ Tm ฮ A โ Subโ ฮ (ฮ โน A)
  _,o_         : โ{ฮ ฮ A} โ Sub ฮ ฮ โ Tm ฮ A โ Sub ฮ (ฮ โน A)
  ฮณ ,o a       = ฯโ ฮณ I.,o ฯโ a , ฮณ ,oโ a
  field
    pโ         : โ{ฮ A} โ Subโ (ฮ โน A) ฮ
  p            : โ{ฮ A} โ Sub (ฮ โน A) ฮ
  p            = I.p , pโ
  field
    qโ         : โ{ฮ A} โ Tmโ (ฮ โน A) A
  q            : โ{ฮ A} โ Tm (ฮ โน A) A
  q            = I.q , qโ
  field    
    โนฮฒโโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ ฯโ (p โ (ฮณ ,o t)) โก ฯโ ฮณ
    โนฮฒโโ       : โ{ฮ ฮ A}{ฮณ : Sub ฮ ฮ}{t : Tm ฮ A} โ ฯโ (q [ ฮณ ,o t ]) โก ฯโ t
    โนฮทโ        : โ{ฮ ฮ A}{ฮณa : Sub ฮ (ฮ โน A)} โ ฯโ (p โ ฮณa ,o q [ ฮณa ]) โก ฯโ ฮณa

  field
    Boolโ      : Tyโ
  Bool         : Ty
  Bool         = I.Bool , Boolโ
  field
    trueโ      : โ{ฮ} โ Tmโ ฮ Bool
  true         : โ{ฮ} โ Tm ฮ Bool
  true         = I.true , trueโ
  field
    falseโ     : โ{ฮ} โ Tmโ ฮ Bool
  false        : โ{ฮ} โ Tm ฮ Bool
  false        = I.false , falseโ
  field
    iteโ       : โ{ฮ A} โ Tm ฮ Bool โ Tm ฮ A โ Tm ฮ A โ Tmโ ฮ A
  ite          : โ{ฮ A} โ Tm ฮ Bool โ Tm ฮ A โ Tm ฮ A โ Tm ฮ A
  ite t a a'   = I.ite (ฯโ t) (ฯโ a) (ฯโ a') , iteโ t a a'
  field
    iteฮฒโโ     : โ{ฮ A u v} โ ฯโ (ite {ฮ}{A} true u v) โก ฯโ u
    iteฮฒโโ     : โ{ฮ A u v} โ ฯโ (ite {ฮ}{A} false u v) โก ฯโ v
    true[]โ    : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (true [ ฮณ ]) โก ฯโ (true {ฮ})
    false[]โ   : โ{ฮ ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (false [ ฮณ ]) โก ฯโ (false {ฮ})
    ite[]โ     : โ{ฮ A t u v ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ ((ite {ฮ}{A} t u v) [ ฮณ ]) โก ฯโ (ite (t [ ฮณ ]) (u [ ฮณ ]) (v [ ฮณ ]))
    
  field
    Natโ       : Tyโ
  Nat          : Ty
  Nat          = I.Nat , Natโ
  field
    numโ       : โ{ฮ} โ โ โ Tmโ ฮ Nat
  num          : โ{ฮ} โ โ โ Tm ฮ Nat
  num n        = I.num n , numโ n
  field
    isZeroโ    : โ{ฮ} โ Tm ฮ Nat โ Tmโ ฮ Bool
  isZero       : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Bool
  isZero t     = I.isZero (ฯโ t) , isZeroโ t
  field
    _+oโ_      : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Nat โ Tmโ ฮ Nat
  _+o_         : โ{ฮ} โ Tm ฮ Nat โ Tm ฮ Nat โ Tm ฮ Nat
  t +o t'      = ฯโ t I.+o ฯโ t' , t +oโ t'
  field
    isZeroฮฒโโ  : โ{ฮ} โ ฯโ (isZero (num {ฮ} 0)) โก ฯโ (true {ฮ})
    isZeroฮฒโโ  : โ{ฮ n} โ ฯโ (isZero (num {ฮ} (1 + n))) โก ฯโ (false {ฮ})
    +ฮฒโ        : โ{ฮ m n} โ ฯโ (num {ฮ} m +o num n) โก ฯโ (num (m + n))

    num[]โ     : โ{ฮ n ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (num n [ ฮณ ]) โก ฯโ (num n)
    isZero[]โ  : โ{ฮ t ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ (isZero t [ ฮณ ]) โก ฯโ (isZero (t [ ฮณ ]))
    +[]โ       : โ{ฮ u v ฮ}{ฮณ : Sub ฮ ฮ} โ ฯโ ((u +o v) [ ฮณ ]) โก ฯโ ((u [ ฮณ ]) +o (v [ ฮณ ]))

  D : DepModel -- we use ฮ instead of I.ฮ for metavariables
  D = record
    { Conโ = ฮป _ โ Conโ
    ; Subโ = ฮป {ฮ} ฮโ {ฮ} ฮโ _ โ Subโ (ฮ , ฮโ) (ฮ , ฮโ)
    ; _โโ_ = ฮป where {ฮณ = ฮณ}{ฮด} ฮณโ ฮดโ โ (ฮณ , ฮณโ) โโ (ฮด , ฮดโ)
    ; assโ = ฮป where {ฮณ = ฮณ}{ฮด = ฮด}{ฮธ = ฮธ} โ transpconst {B = Subโ _ _}{e = I.ass {ฮณ = ฮณ}{ฮด = ฮด}{ฮธ = ฮธ}} โพ assโ
    ; idโ = idโ
    ; idlโ = ฮป where {ฮณ = ฮณ} โ transpconst {B = Subโ _ _}{e = I.idl {ฮณ = ฮณ}} โพ idlโ
    ; idrโ = ฮป where {ฮณ = ฮณ} โ transpconst {B = Subโ _ _}{e = I.idr {ฮณ = ฮณ}} โพ idrโ
    ; โโ = โโ
    ; ฮตโ = ฮตโ
    ; โฮทโ = ฮป where {ฯ = ฯ} โ transpconst {B = Subโ _ _}{e = I.โฮท {ฯ = ฯ}} โพ โฮทโ {ฯ = ฯ , _}
    ; Tyโ = ฮป _ โ Tyโ
    ; Tmโ = ฮป {ฮ}{A} ฮโ Aโ _ โ Tmโ (ฮ , ฮโ) (A , Aโ)
    ; _[_]โ = ฮป where {t = t}{ฮณ} tโ ฮณโ โ (t , tโ) [ ฮณ , ฮณโ ]โ
    ; [โ]โ = ฮป where {t = t}{ฮณ}{ฮด} โ transpconst {B = Tmโ _ _}{e = I.[โ] {t = t}{ฮณ}{ฮด}} โพ [โ]โ
    ; [id]โ = ฮป where{t = t} โ transpconst {B = Tmโ _ _}{e = I.[id] {t = t}} โพ [id]โ
    ; _โนโ_ = ฮป {ฮ}{A} ฮโ Aโ โ (ฮ , ฮโ) โนโ (A , Aโ)
    ; _,oโ_ = ฮป where {ฮณ = ฮณ}{t} ฮณโ tโ โ (ฮณ , ฮณโ) ,oโ (t , tโ)
    ; pโ = pโ
    ; qโ = qโ
    ; โนฮฒโโ = ฮป where {ฮณ = ฮณ}{t} โ transpconst {B = Subโ _ _}{e = I.โนฮฒโ {ฮณ = ฮณ}{t}} โพ โนฮฒโโ
    ; โนฮฒโโ = ฮป where {ฮณ = ฮณ}{t} โ transpconst {B = Tmโ _ _}{e = I.โนฮฒโ {ฮณ = ฮณ}{t}} โพ โนฮฒโโ
    ; โนฮทโ = ฮป where {ฮณa = ฮณa} โ transpconst {B = Subโ _ _}{e = I.โนฮท {ฮณa = ฮณa}} โพ โนฮทโ
    ; Boolโ = Boolโ
    ; trueโ = trueโ
    ; falseโ = falseโ
    ; iteโ = ฮป where {t = t}{a}{a'} tโ aโ a'โ โ iteโ (t , tโ) (a , aโ) (a' , a'โ)
    ; iteฮฒโโ = ฮป where {u = u}{v} โ transpconst {B = Tmโ _ _}{e = I.iteฮฒโ {u = u}{v = v}} โพ iteฮฒโโ
    ; iteฮฒโโ = ฮป where {u = u}{v} โ transpconst {B = Tmโ _ _}{e = I.iteฮฒโ {u = u}{v = v}} โพ iteฮฒโโ
    ; true[]โ = transpconst {B = Tmโ _ _}{e = I.true[]} โพ true[]โ
    ; false[]โ = transpconst {B = Tmโ _ _}{e = I.false[]} โพ false[]โ
    ; ite[]โ = transpconst {B = Tmโ _ _}{e = I.ite[]} โพ ite[]โ
    ; Natโ = Natโ
    ; numโ = numโ
    ; isZeroโ = ฮป where {t = t} tโ โ isZeroโ (t , tโ)
    ; _+oโ_ = ฮป where {u = u}{v} uโ vโ โ (u , uโ) +oโ (v , vโ)
    ; isZeroฮฒโโ = transpconst {B = Tmโ _ _}{e = I.isZeroฮฒโ} โพ isZeroฮฒโโ
    ; isZeroฮฒโโ = transpconst {B = Tmโ _ _}{e = I.isZeroฮฒโ} โพ isZeroฮฒโโ
    ; +ฮฒโ = transpconst {B = Tmโ _ _}{e = I.+ฮฒ} โพ +ฮฒโ
    ; num[]โ = transpconst {B = Tmโ _ _}{e = I.num[]} โพ num[]โ
    ; isZero[]โ = transpconst {B = Tmโ _ _}{e = I.isZero[]} โพ isZero[]โ
    ; +[]โ = transpconst {B = Tmโ _ _}{e = I.+[]} โพ +[]โ
    }
  module D = DepModel D

  โฆ_โงT : I.Ty โ Tyโ
  โฆ_โงT = D.โฆ_โงT

  โฆ_โงC : I.Con โ Conโ
  โฆ_โงC = D.โฆ_โงC

  โฆ_โงs : โ{ฮ ฮ} โ I.Sub ฮ ฮ โ Subโ (ฮ , โฆ ฮ โงC) (ฮ , โฆ ฮ โงC)
  โฆ_โงs = D.โฆ_โงs
  
  โฆ_โงt : โ{ฮ A} โ I.Tm  ฮ A โ Tmโ (ฮ , โฆ ฮ โงC) (A , โฆ A โงT)
  โฆ_โงt = D.โฆ_โงt

I : Model
I = record { Con = I.Con ; Sub = I.Sub ; _โ_ = I._โ_ ; ass = I.ass ; id = I.id ; idl = I.idl ; idr = I.idr ; โ = I.โ  ; ฮต = I.ฮต ; โฮท = I.โฮท ; Ty = I.Ty ; Tm = I.Tm ; _[_] = I._[_] ; [โ] = I.[โ] ; [id] = I.[id] ; _โน_ = I._โน_  ; _,o_ = I._,o_ ; p =  I.p  ; q = I.q ; โนฮฒโ = I.โนฮฒโ ; โนฮฒโ = I.โนฮฒโ ; โนฮท = I.โนฮท ; Bool = I.Bool ; true = I.true ; false = I.false ; ite = I.ite ; iteฮฒโ = I.iteฮฒโ ; iteฮฒโ = I.iteฮฒโ ; true[] = I.true[] ; false[] = I.false[] ; ite[] = I.ite[] ; Nat = I.Nat ; num = I.num ; isZero = I.isZero ; _+o_ = I._+o_ ; isZeroฮฒโ = I.isZeroฮฒโ ; isZeroฮฒโ = I.isZeroฮฒโ ; +ฮฒ = I.+ฮฒ ; num[] = I.num[] ; isZero[] = I.isZero[] ; +[] = I.+[] }

open I public

infixl 6 _โNf_
infixl 6 _[_]V _[_]Ne _[_]Nf
infixl 5 _,Nf_
infixl 7 _+NeNe_ _+NeNf_ _+NfNe_ _+NfNf_

data Var : Con โ Ty โ Set where
  vz : โ{ฮ A} โ Var (ฮ โน A) A
  vs : โ{ฮ A B} โ Var ฮ A โ Var (ฮ โน B) A

data Ne (ฮ : Con) : Ty โ Set
data Nf (ฮ : Con) : Ty โ Set

data Ne ฮ where
  var       : โ{A} โ Var ฮ A โ Ne ฮ A
  iteNe     : โ{A} โ Ne ฮ Bool โ Nf ฮ A โ Nf ฮ A โ Ne ฮ A
  isZeroNe  : Ne ฮ Nat โ Ne ฮ Bool
  _+NeNe_   : Ne ฮ Nat โ Ne ฮ Nat โ Ne ฮ Nat
  _+NeNf_   : Ne ฮ Nat โ โ โ Ne ฮ Nat
  _+NfNe_   : โ โ Ne ฮ Nat โ Ne ฮ Nat

data Nf ฮ where
  neu       : โ{A} โ Ne ฮ A โ Nf ฮ A
  trueNf    : Nf ฮ Bool
  falseNf   : Nf ฮ Bool
  numNf     : (n : โ) โ Nf ฮ Nat

โ_โV : โ{ฮ A} โ Var ฮ A โ Tm ฮ A
โ vz โV = q
โ vs x โV = โ x โV [ p ]

โ_โNe : โ{ฮ A} โ Ne ฮ A โ Tm ฮ A
โ_โNf : โ{ฮ A} โ Nf ฮ A โ Tm ฮ A
โ var x โNe = โ x โV
โ iteNe t a a' โNe = ite โ t โNe โ a โNf โ a' โNf
โ isZeroNe t โNe = isZero โ t โNe
โ t +NeNe t' โNe = โ t โNe +o โ t' โNe
โ t +NeNf n' โNe = โ t โNe +o num n'
โ n +NfNe t' โNe = num n +o โ t' โNe
โ neu t โNf = โ t โNe
โ trueNf โNf = true
โ falseNf โNf = false
โ numNf n โNf = num n

data Nfs (ฮ : Con) : Con โ Set where
  ฮตNf       : Nfs ฮ โ
  _,Nf_     : โ{ฮ A} โ Nfs ฮ ฮ โ Nf ฮ A โ Nfs ฮ (ฮ โน A)

โ_โNfs : โ{ฮ ฮ} โ Nfs ฮ ฮ โ Sub ฮ ฮ
โ ฮตNf โNfs = ฮต
โ ฮณ ,Nf a โNfs = โ ฮณ โNfs ,o โ a โNf

iteNf : โ{ฮ A} โ Nf ฮ Bool โ Nf ฮ A โ Nf ฮ A โ Nf ฮ A
iteNf (neu t) a a' = neu (iteNe t a a')
iteNf trueNf a a' = a
iteNf falseNf a a' = a'

_+NfNf_ : โ{ฮ} โ Nf ฮ Nat โ Nf ฮ Nat โ Nf ฮ Nat
neu tn +NfNf neu tn' = neu (tn +NeNe tn')
neu tn +NfNf numNf n = neu (tn +NeNf n)
numNf n +NfNf neu tn = neu (n +NfNe tn)
numNf n +NfNf numNf n' = numNf (n + n')

isZeroNf : โ{ฮ} โ Nf ฮ Nat โ Nf ฮ Bool
isZeroNf (neu n) = neu (isZeroNe n)
isZeroNf (numNf zero) = trueNf
isZeroNf (numNf (suc n)) = falseNf

_[_]V : โ{ฮ A} โ Var ฮ A โ โ{ฮ} โ Nfs ฮ ฮ โ Nf ฮ A
vz [ ฮณ ,Nf a ]V = a
vs x [ ฮณ ,Nf a ]V = x [ ฮณ ]V

_[_]Ne : โ{ฮ A} โ Ne ฮ A โ โ{ฮ} โ Nfs ฮ ฮ โ Nf ฮ A
_[_]Nf : โ{ฮ A} โ Nf ฮ A โ โ{ฮ} โ Nfs ฮ ฮ โ Nf ฮ A
var x [ ฮณ ]Ne = x [ ฮณ ]V
iteNe t a a' [ ฮณ ]Ne = iteNf (t [ ฮณ ]Ne) (a [ ฮณ ]Nf) (a' [ ฮณ ]Nf)
(t +NeNe t') [ ฮณ ]Ne = (t [ ฮณ ]Ne) +NfNf (t' [ ฮณ ]Ne)
(t +NeNf n') [ ฮณ ]Ne = (t [ ฮณ ]Ne) +NfNf numNf n'
(n +NfNe t') [ ฮณ ]Ne = numNf n +NfNf (t' [ ฮณ ]Ne)
isZeroNe t [ ฮณ ]Ne = isZeroNf (t [ ฮณ ]Ne)
neu a [ ฮณ ]Nf = a [ ฮณ ]Ne
trueNf [ ฮณ ]Nf = trueNf
falseNf [ ฮณ ]Nf = falseNf
numNf n [ ฮณ ]Nf = numNf n

iteNf[] : โ{ฮ A t u v ฮ}{ฮณ : Nfs ฮ ฮ} โ
  (iteNf {ฮ}{A} t u v) [ ฮณ ]Nf โก iteNf (t [ ฮณ ]Nf) (u [ ฮณ ]Nf) (v [ ฮณ ]Nf)
iteNf[] {t = neu t} = refl
iteNf[] {t = trueNf} = refl
iteNf[] {t = falseNf} = refl

+NfNf[] : โ{ฮ u v ฮ}{ฮณ : Nfs ฮ ฮ} โ (u +NfNf v) [ ฮณ ]Nf โก (u [ ฮณ ]Nf) +NfNf (v [ ฮณ ]Nf)
+NfNf[] {u = neu   t} {v = neu   t'} = refl
+NfNf[] {u = neu   t} {v = numNf n'} = refl
+NfNf[] {u = numNf n} {v = neu   t'} = refl
+NfNf[] {u = numNf n} {v = numNf n'} = refl

isZeroNf[]  : โ{ฮ t ฮ}{ฮณ : Nfs ฮ ฮ} โ isZeroNf t [ ฮณ ]Nf โก isZeroNf (t [ ฮณ ]Nf)
isZeroNf[] {t = neu t} = refl
isZeroNf[] {t = numNf zero} = refl
isZeroNf[] {t = numNf (suc n)} = refl

_โNf_ : โ{ฮ ฮ ฮ} โ Nfs ฮ ฮ โ Nfs ฮ ฮ โ Nfs ฮ ฮ
ฮตNf โNf ฮด = ฮตNf
(ฮณ ,Nf t) โNf ฮด = (ฮณ โNf ฮด) ,Nf (t [ ฮด ]Nf)

[โ]V : โ{ฮ ฮ ฮ A}{x : Var ฮ A}{ฮณ : Nfs ฮ ฮ}{ฮด : Nfs ฮ ฮ} โ
  x [ ฮณ โNf ฮด ]V โก x [ ฮณ ]V [ ฮด ]Nf
[โ]V {x = vz}{ฮณ = ฮณ ,Nf a} = refl
[โ]V {x = vs x}{ฮณ = ฮณ ,Nf a} = [โ]V {x = x}

[โ]Ne : โ{ฮ ฮ ฮ A}{t : Ne ฮ A}{ฮณ : Nfs ฮ ฮ}{ฮด : Nfs ฮ ฮ} โ
  t [ ฮณ โNf ฮด ]Ne โก t [ ฮณ ]Ne [ ฮด ]Nf
[โ]Nf : โ{ฮ ฮ ฮ A}{t : Nf ฮ A}{ฮณ : Nfs ฮ ฮ}{ฮด : Nfs ฮ ฮ} โ
  t [ ฮณ โNf ฮด ]Nf โก t [ ฮณ ]Nf [ ฮด ]Nf
[โ]Ne {t = var x} = [โ]V {x = x}
[โ]Ne {t = iteNe t a a'}{ฮณ} = congโ iteNf ([โ]Ne {t = t}) ([โ]Nf {t = a}) ([โ]Nf {t = a'}) โพ
  iteNf[] {t = t [ ฮณ ]Ne} โปยน
[โ]Ne {t = t +NeNe t'}{ฮณ} = congโ _+NfNf_ ([โ]Ne {t = t}) ([โ]Ne {t = t'}) โพ
  +NfNf[] {u = t [ ฮณ ]Ne}{v = t' [ ฮณ ]Ne} โปยน
[โ]Ne {t = t +NeNf n'}{ฮณ} = cong (_+NfNf numNf n') ([โ]Ne {t = t}) โพ
  +NfNf[] {u = t [ ฮณ ]Ne}{v = numNf n'} โปยน
[โ]Ne {t = n +NfNe t'}{ฮณ} = cong (numNf n +NfNf_) ([โ]Ne {t = t'}) โพ
  +NfNf[] {u = numNf n}{v = t' [ ฮณ ]Ne} โปยน
[โ]Ne {t = isZeroNe t}{ฮณ} = cong isZeroNf ([โ]Ne {t = t}) โพ isZeroNf[] {t = t [ ฮณ ]Ne} โปยน
[โ]Nf {t = neu t} = [โ]Ne {t = t}
[โ]Nf {t = trueNf} = refl
[โ]Nf {t = falseNf} = refl
[โ]Nf {t = numNf n} = refl

assNf : โ{ฮ ฮ ฮ ฮ}{ฮณ : Nfs ฮ ฮ}{ฮด : Nfs ฮ ฮ}{ฮธ : Nfs ฮ ฮ} โ
  (ฮณ โNf ฮด) โNf ฮธ โก ฮณ โNf (ฮด โNf ฮธ)
assNf {ฮณ = ฮตNf} {ฮด} {ฮธ} = refl
assNf {ฮณ = ฮณ ,Nf a} {ฮด} {ฮธ} = congโ _,Nf_ (assNf {ฮณ = ฮณ}) ([โ]Nf {t = a} โปยน)

wkNe : โ{ฮ A B} โ Ne ฮ A โ Ne (ฮ โน B) A
wkNf : โ{ฮ A B} โ Nf ฮ A โ Nf (ฮ โน B) A
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

wk : โ{ฮ ฮ} โ Nfs ฮ ฮ โ โ{A} โ Nfs (ฮ โน A) ฮ
wk ฮตNf       = ฮตNf
wk (ฮณ ,Nf a) = wk ฮณ ,Nf wkNf a

wk-iteNf : โ{ฮ A}{t : Nf ฮ Bool}{a a' : Nf ฮ A}{B} โ
  wkNf {B = B} (iteNf t a a') โก iteNf (wkNf t) (wkNf a) (wkNf a')
wk-iteNf {t = neu t} = refl
wk-iteNf {t = trueNf} = refl
wk-iteNf {t = falseNf} = refl

wk-+NfNf : โ{ฮ}{t t' : Nf ฮ Nat}{B} โ
  wkNf {B = B} (t +NfNf t') โก wkNf t +NfNf wkNf t'
wk-+NfNf {t = neu   t}{t' = neu   t'} = refl
wk-+NfNf {t = neu   t}{t' = numNf n'} = refl
wk-+NfNf {t = numNf n}{t' = neu   t'} = refl
wk-+NfNf {t = numNf n}{t' = numNf n'} = refl

wk-isZeroNf : โ{ฮ}{t : Nf ฮ Nat}{B} โ wkNf {B = B} (isZeroNf t) โก isZeroNf (wkNf t)
wk-isZeroNf {t = neu x} = refl
wk-isZeroNf {t = numNf zero} = refl
wk-isZeroNf {t = numNf (suc n)} = refl

wkNe[] : โ{ฮ A}{a : Ne ฮ A}{ฮ}{ฮณ : Nfs ฮ ฮ}{B}{b : Nf ฮ B} โ
  wkNe a [ ฮณ ,Nf b ]Ne โก a [ ฮณ ]Ne
wkNf[] : โ{ฮ A}{a : Nf ฮ A}{ฮ}{ฮณ : Nfs ฮ ฮ}{B}{b : Nf ฮ B} โ
  wkNf a [ ฮณ ,Nf b ]Nf โก a [ ฮณ ]Nf
wkNe[] {a = var x} = refl
wkNe[] {a = iteNe t a a'} = congโ iteNf (wkNe[] {a = t}) (wkNf[] {a = a}) (wkNf[] {a = a'})
wkNe[] {a = t +NeNe t'} = congโ _+NfNf_ (wkNe[] {a = t}) (wkNe[] {a = t'})
wkNe[] {a = t +NeNf n'} = cong (_+NfNf numNf n') (wkNe[] {a = t})
wkNe[] {a = n +NfNe t'} = cong (numNf n +NfNf_) (wkNe[] {a = t'})
wkNe[] {a = isZeroNe t} = cong isZeroNf (wkNe[] {a = t})
wkNf[] {a = neu a} = wkNe[] {a = a}
wkNf[] {a = trueNf} = refl
wkNf[] {a = falseNf} = refl
wkNf[] {a = numNf n} = refl

wkโ : โ{ฮ ฮ}{ฮณ : Nfs ฮ ฮ}{ฮ}{ฮด : Nfs ฮ ฮ}{A}{a : Nf ฮ A} โ
  wk ฮณ โNf (ฮด ,Nf a) โก ฮณ โNf ฮด
wkโ {ฮณ = ฮตNf} = refl
wkโ {ฮณ = ฮณ ,Nf a}{ฮด = ฮด} = congโ _,Nf_ (wkโ {ฮณ = ฮณ}) (wkNf[] {a = a})

idNf : โ{ฮ} โ Nfs ฮ ฮ
idNf {โ} = ฮตNf
idNf {ฮ โน A} = wk (idNf {ฮ}) ,Nf neu (var vz)

wk[]V : โ{ฮ A}{x : Var ฮ A}{ฮ}{ฮณ : Nfs ฮ ฮ}{B} โ
  wkNf {B = B} (x [ ฮณ ]V) โก x [ wk ฮณ ]V
wk[]V {x = vz  }{ฮณ = ฮณ ,Nf a} = refl
wk[]V {x = vs x}{ฮณ = ฮณ ,Nf a} = wk[]V {x = x}{ฮณ = ฮณ}

wk[]Ne : โ{ฮ A}{t : Ne ฮ A}{ฮ}{ฮณ : Nfs ฮ ฮ}{B} โ
  wkNf {B = B} (t [ ฮณ ]Ne) โก t [ wk ฮณ ]Ne
wk[]Nf : โ{ฮ A}{t : Nf ฮ A}{ฮ}{ฮณ : Nfs ฮ ฮ}{B} โ
  wkNf {B = B} (t [ ฮณ ]Nf) โก t [ wk ฮณ ]Nf
wk[]Ne {t = var x} = wk[]V {x = x}
wk[]Ne {t = iteNe t a a'}{ฮณ = ฮณ} = wk-iteNf {t = t [ ฮณ ]Ne} โพ
  congโ iteNf (wk[]Ne {t = t}) (wk[]Nf {t = a}) (wk[]Nf {t = a'})
wk[]Ne {t = t +NeNe t'} = wk-+NfNf โพ congโ _+NfNf_ (wk[]Ne {t = t}) (wk[]Ne {t = t'})
wk[]Ne {t = t +NeNf n'} = wk-+NfNf โพ cong (_+NfNf numNf n') (wk[]Ne {t = t})
wk[]Ne {t = n +NfNe t'} = wk-+NfNf โพ cong (numNf n +NfNf_) (wk[]Ne {t = t'})
wk[]Ne {t = isZeroNe t} = wk-isZeroNf โพ cong isZeroNf (wk[]Ne {t = t})
wk[]Nf {t = neu t} = wk[]Ne {t = t}
wk[]Nf {t = trueNf} = refl
wk[]Nf {t = falseNf} = refl
wk[]Nf {t = numNf n} = refl

[id]V : โ{ฮ A}{x : Var ฮ A} โ x [ idNf ]V โก neu (var x)
[id]V {x = vz} = refl
[id]V {x = vs x} = wk[]V {x = x} โปยน โพ cong wkNf ([id]V {x = x})

[id]Ne : โ{ฮ A}{t : Ne ฮ A} โ t [ idNf ]Ne โก neu t
[id]Nf : โ{ฮ A}{t : Nf ฮ A} โ t [ idNf ]Nf โก t
[id]Ne {t = var x} = [id]V {x = x}
[id]Ne {t = iteNe t a a'} = congโ iteNf ([id]Ne {t = t}) ([id]Nf {t = a}) ([id]Nf {t = a'})
[id]Ne {t = t +NeNe t'} = congโ _+NfNf_ ([id]Ne {t = t}) ([id]Ne {t = t'})
[id]Ne {t = t +NeNf n'} = cong (_+NfNf numNf n') ([id]Ne {t = t})
[id]Ne {t = n +NfNe t'} = cong (numNf n +NfNf_) ([id]Ne {t = t'})
[id]Ne {t = isZeroNe t} = cong isZeroNf ([id]Ne {t = t})
[id]Nf {t = neu t} = [id]Ne {t = t}
[id]Nf {t = trueNf} = refl
[id]Nf {t = falseNf} = refl
[id]Nf {t = numNf n} = refl

idlNf : โ{ฮ ฮ}{ฮณ : Nfs ฮ ฮ} โ idNf โNf ฮณ โก ฮณ
idlNf {ฮ = โ}{ฮณ = ฮตNf} = refl
idlNf {ฮ = ฮ โน A}{ฮณ = ฮณ ,Nf a} = cong (_,Nf a) (wkโ {ฮณ = idNf} โพ idlNf {ฮ = ฮ})

idrNf : โ{ฮ ฮ}{ฮณ : Nfs ฮ ฮ} โ ฮณ โNf idNf โก ฮณ
idrNf {ฮณ = ฮตNf} = refl
idrNf {ฮณ = ฮณ ,Nf a} = congโ _,Nf_ (idrNf {ฮณ = ฮณ}) [id]Nf

pNf : โ{ฮ A} โ Nfs (ฮ โน A) ฮ
pNf = wk idNf

โนฮฒโNf : โ{ฮ ฮ A}{ฮณ : Nfs ฮ ฮ}{t : Nf ฮ A} โ pNf โNf (ฮณ ,Nf t) โก ฮณ
โนฮฒโNf = wkโ โพ idlNf

โนฮทNf : โ{ฮ ฮ A}{ฮณa : Nfs ฮ (ฮ โน A)} โ pNf โNf ฮณa ,Nf vz [ ฮณa ]V โก ฮณa
โนฮทNf {ฮณa = ฮณ ,Nf a} = cong (_,Nf a) (wkโ โพ idlNf)

N : ParaModel
N = record
  { Conโ = Lift โค
  ; Subโ = ฮป ฮ ฮ โ Nfs (ฯโ ฮ) (ฯโ ฮ)
  ; _โโ_ = ฮป ฮณ ฮด โ ฯโ ฮณ โNf ฯโ ฮด
  ; assโ = assNf
  ; idโ = idNf
  ; idlโ = idlNf
  ; idrโ = idrNf
  ; โโ = _
  ; ฮตโ = ฮตNf
  ; โฮทโ = ฮป { {_}{_ , ฮตNf} โ refl }
  ; Tyโ = Lift โค
  ; Tmโ = ฮป ฮ A โ Nf (ฯโ ฮ) (ฯโ A)
  ; _[_]โ = ฮป a ฮณ โ ฯโ a [ ฯโ ฮณ ]Nf
  ; [โ]โ = ฮป where {t = t} โ [โ]Nf {t = ฯโ t}
  ; [id]โ = [id]Nf
  ; _โนโ_ = _
  ; _,oโ_ = ฮป ฮณ a โ ฯโ ฮณ ,Nf ฯโ a
  ; pโ = pNf
  ; qโ = neu (var vz)
  ; โนฮฒโโ = โนฮฒโNf
  ; โนฮฒโโ = refl
  ; โนฮทโ = โนฮทNf
  ; Boolโ = _
  ; trueโ = trueNf
  ; falseโ = falseNf
  ; iteโ = ฮป t a a' โ iteNf (ฯโ t) (ฯโ a) (ฯโ a')
  ; iteฮฒโโ = refl
  ; iteฮฒโโ = refl
  ; true[]โ = refl
  ; false[]โ = refl
  ; ite[]โ = ฮป where {t = t} โ iteNf[] {t = ฯโ t}
  ; Natโ = _
  ; numโ = numNf
  ; isZeroโ = ฮป t โ isZeroNf (ฯโ t)
  ; _+oโ_ = ฮป t t' โ ฯโ t +NfNf ฯโ t'
  ; isZeroฮฒโโ = refl
  ; isZeroฮฒโโ = refl
  ; +ฮฒโ = refl
  ; num[]โ = refl
  ; isZero[]โ = ฮป where {t = t} โ isZeroNf[] {t = ฯโ t}
  ; +[]โ = ฮป where {u = u} โ +NfNf[] {u = ฯโ u}
  }

module N = ParaModel N

norm : โ{ฮ A} โ Tm ฮ A โ Nf ฮ A
norm = N.โฆ_โงt

โiteโ : โ{ฮ A}{t : Nf ฮ Bool}{a a' : Nf ฮ A} โ
  โ iteNf t a a' โNf โก ite โ t โNf โ a โNf โ a' โNf
โiteโ {t = neu t} = refl
โiteโ {t = trueNf} = iteฮฒโ โปยน
โiteโ {t = falseNf} = iteฮฒโ โปยน

โisZeroโ : โ{ฮ}{t : Nf ฮ Nat} โ โ isZeroNf t โNf โก isZero โ t โNf
โisZeroโ {t = neu t} = refl
โisZeroโ {t = numNf zero} = isZeroฮฒโ โปยน
โisZeroโ {t = numNf (suc n)} = isZeroฮฒโ โปยน

โ+โ : โ{ฮ}{t t' : Nf ฮ Nat} โ โ t +NfNf t' โNf โก โ t โNf +o โ t' โNf
โ+โ {t = neu t} {t' = neu t'} = refl
โ+โ {t = neu t} {t' = numNf n'} = refl
โ+โ {t = numNf n} {t' = neu t'} = refl
โ+โ {t = numNf n} {t' = numNf n'} = +ฮฒ โปยน

โ[]Vโ : โ{ฮ ฮ A}{x : Var ฮ A}{ฮณ : Nfs ฮ ฮ} โ โ x [ ฮณ ]V โNf โก โ x โV [ โ ฮณ โNfs ]
โ[]Vโ {x = vz}{ฮณ = ฮณ ,Nf a} = โนฮฒโ โปยน
โ[]Vโ {x = vs x}{ฮณ = ฮณ ,Nf a} = โ[]Vโ {x = x} โพ cong (โ x โV [_]) (โนฮฒโ โปยน) โพ [โ]

โ[]Neโ : โ{ฮ ฮ A}{a : Ne ฮ A}{ฮณ : Nfs ฮ ฮ} โ โ a [ ฮณ ]Ne โNf โก โ a โNe [ โ ฮณ โNfs ]
โ[]Nfโ : โ{ฮ ฮ A}{a : Nf ฮ A}{ฮณ : Nfs ฮ ฮ} โ โ a [ ฮณ ]Nf โNf โก โ a โNf [ โ ฮณ โNfs ]

โ[]Neโ {a = var x} = โ[]Vโ {x = x}
โ[]Neโ {a = iteNe t a a'} = โiteโ {t = t [ _ ]Ne}{a = a [ _ ]Nf}{a' = a' [ _ ]Nf} โพ congโ ite (โ[]Neโ {a = t}) (โ[]Nfโ {a = a}) (โ[]Nfโ {a = a'}) โพ ite[] โปยน
โ[]Neโ {a = isZeroNe t} = โisZeroโ {t = t [ _ ]Ne} โพ cong isZero (โ[]Neโ {a = t}) โพ isZero[] โปยน
โ[]Neโ {a = t +NeNe t'} = โ+โ {t = t [ _ ]Ne}{t' = t' [ _ ]Ne} โพ congโ _+o_ (โ[]Neโ {a = t}) (โ[]Neโ {a = t'}) โพ +[] โปยน
โ[]Neโ {a = t +NeNf n'} = โ+โ {t = t [ _ ]Ne}{t' = numNf n'} โพ congโ _+o_ (โ[]Neโ {a = t}) (num[] โปยน) โพ +[] โปยน
โ[]Neโ {a = n +NfNe t'} = โ+โ {t = numNf n}{t' = t' [ _ ]Ne} โพ congโ _+o_ (num[] โปยน) (โ[]Neโ {a = t'}) โพ +[] โปยน
โ[]Nfโ {a = neu a} = โ[]Neโ {a = a}
โ[]Nfโ {a = trueNf} = true[] โปยน
โ[]Nfโ {a = falseNf} = false[] โปยน
โ[]Nfโ {a = numNf n} = num[] โปยน

โwkNeโ : โ{ฮ A}{a : Ne ฮ A}{B} โ โ wkNe {B = B} a โNe โก โ a โNe [ p ]
โwkNfโ : โ{ฮ A}{a : Nf ฮ A}{B} โ โ wkNf {B = B} a โNf โก โ a โNf [ p ]
โwkNeโ {a = var x} = refl
โwkNeโ {a = iteNe t a a'} = congโ ite (โwkNeโ {a = t}) (โwkNfโ {a = a}) (โwkNfโ {a = a'}) โพ ite[] โปยน
โwkNeโ {a = isZeroNe t} = cong isZero (โwkNeโ {a = t}) โพ isZero[] โปยน
โwkNeโ {a = t +NeNe t'} = congโ _+o_ (โwkNeโ {a = t}) (โwkNeโ {a = t'}) โพ +[] โปยน
โwkNeโ {a = t +NeNf n'} = congโ _+o_ (โwkNeโ {a = t}) (num[] โปยน) โพ +[] โปยน
โwkNeโ {a = n +NfNe t'} = congโ _+o_ (num[] โปยน) (โwkNeโ {a = t'}) โพ +[] โปยน
โwkNfโ {a = neu a} = โwkNeโ {a = a}
โwkNfโ {a = trueNf} = true[] โปยน
โwkNfโ {a = falseNf} = false[] โปยน
โwkNfโ {a = numNf n} = num[] โปยน

โwkโ : โ{ฮ ฮ}{ฮณ : Nfs ฮ ฮ}{A} โ โ wk ฮณ {A = A} โNfs โก โ ฮณ โNfs โ p
โwkโ {ฮณ = ฮตNf} = โฮท โปยน
โwkโ {ฮณ = ฮณ ,Nf a} = congโ _,o_ (โwkโ {ฮณ = ฮณ}) (โwkNfโ {a = a}) โพ ,โ โปยน

โidโ : โ{ฮ} โ โ idNf {ฮ} โNfs โก id
โidโ {โ} = โฮท โปยน
โidโ {ฮ โน A} = congโ _,o_ (โwkโ โพ (cong (_โ p) (โidโ {ฮ}) โพ idl โพ idr โปยน)) ([id] โปยน) โพ โนฮท

โโโ : โ{ฮ ฮ ฮ}{ฮณ : Nfs ฮ ฮ}{ฮด : Nfs ฮ ฮ} โ โ ฮณ โNf ฮด โNfs โก โ ฮณ โNfs โ โ ฮด โNfs
โโโ {ฮณ = ฮตNf} = โฮท โปยน
โโโ {ฮณ = ฮณ ,Nf a} = congโ _,o_ (โโโ {ฮณ = ฮณ}) (โ[]Nfโ {a = a}) โพ ,โ โปยน

C : DepModel
C = record
  { Conโ = ฮป _ โ Lift โค
  ; Subโ = ฮป {ฮ} _ {ฮ} _ ฮณ โ Lift (โ N.โฆ ฮณ โงs โNfs โก ฮณ)
  ; _โโ_ = ฮป ฮณ= ฮด= โ mk (โโโ โพ congโ _โ_ (un ฮณ=) (un ฮด=))
  ; assโ = refl
  ; idโ = mk โidโ
  ; idlโ = refl
  ; idrโ = refl
  ; โโ = _
  ; ฮตโ = mk refl
  ; โฮทโ = refl
  ; Tyโ = ฮป _ โ Lift โค
  ; Tmโ = ฮป {ฮ}{A} _ _ a โ Lift (โ N.โฆ a โงt โNf โก a)
  ; _[_]โ = ฮป where {t = a} a= ฮณ= โ mk (โ[]Nfโ {a = N.โฆ a โงt} โพ congโ _[_] (un a=) (un ฮณ=))
  ; [โ]โ = refl
  ; [id]โ = refl
  ; _โนโ_ = _
  ; _,oโ_ = ฮป where {ฮณ = ฮณ}{a} ฮณ= a= โ mk (congโ _,o_ (un ฮณ=) (un a=))
  ; pโ = mk (โwkโ {ฮณ = idNf} โพ cong (_โ p) โidโ โพ idl)
  ; qโ = mk refl
  ; โนฮฒโโ = refl
  ; โนฮฒโโ = refl
  ; โนฮทโ = refl
  ; Boolโ = _
  ; trueโ = mk refl
  ; falseโ = mk refl
  ; iteโ = ฮป where {t = t}{a}{a'} t= a= a'= โ mk (โiteโ {t = N.โฆ t โงt} โพ congโ ite (un t=) (un a=) (un a'=))
  ; iteฮฒโโ = refl
  ; iteฮฒโโ = refl
  ; true[]โ = refl
  ; false[]โ = refl
  ; ite[]โ = refl
  ; Natโ = _
  ; numโ = ฮป _ โ mk refl
  ; isZeroโ = ฮป where {t = t} t= โ mk (โisZeroโ {t = N.โฆ t โงt} โพ cong isZero (un t=))
  ; _+oโ_ = ฮป where {u = t}{t'} t= t'= โ mk (โ+โ {t = N.โฆ t โงt}{t' = N.โฆ t' โงt} โพ congโ _+o_ (un t=) (un t'=))
  ; isZeroฮฒโโ = refl
  ; isZeroฮฒโโ = refl
  ; +ฮฒโ = refl
  ; num[]โ = refl
  ; isZero[]โ = refl
  ; +[]โ = refl
  }
module C = DepModel C

compl : โ{ฮ A}(t : Tm ฮ A) โ โ norm t โNf โก t
compl t = un C.โฆ t โงt
