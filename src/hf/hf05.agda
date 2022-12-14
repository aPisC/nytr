{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

module hf05 where

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to β)
open import Agda.Builtin.Bool public renaming (Bool to π; true to tt; false to ff)
open import Agda.Builtin.Sigma public renaming (fst to Οβ; snd to Οβ)

infix  4 _β‘_
infix  3 _β
infixr 2 _β‘β¨_β©_
infixl 2 _βΎ_
infix 5 _β»ΒΉ
infixr 2 _Γ_
infixr 4 _,Γ=_

data _β‘_ {β}{A : Set β}(a : A) : A β Prop β where
  refl : a β‘ a

{-# BUILTIN EQUALITY _β‘_ #-}

cong : β{β}{A : Set β}{β'}{B : Set β'}(f : A β B){a a' : A} β a β‘ a' β f a β‘ f a'
cong f refl = refl

congβ : β{β β' β''}{A : Set β}{B : Set β'}{C : Set β''}
        {a c : A}{b d : B}(f : A β B β C)(p : a β‘ c)(q : b β‘ d) β
        f a b β‘ f c d
congβ f refl refl = refl

congβ : β{β β' β'' β'''}{A : Set β}{B : Set β'}{C : Set β''}{D : Set β'''}
        {a d : A}{b e : B}{c f : C}(g : A β B β C β D)(p : a β‘ d)(q : b β‘ e)(r : c β‘ f) β
        g a b c β‘ g d e f
congβ g refl refl refl = refl

_βΎ_ : β{β}{A : Set β}{a a' : A} β a β‘ a' β β{a''} β a' β‘ a'' β a β‘ a''
refl βΎ refl = refl

_β»ΒΉ : β{β}{A : Set β}{a a' : A} β a β‘ a' β a' β‘ a
refl β»ΒΉ = refl

_β‘β¨_β©_ : β{β}{A : Set β}(x : A){y z : A} β x β‘ y β y β‘ z β x β‘ z
x β‘β¨ xβ‘y β© yβ‘z = xβ‘y βΎ yβ‘z

_β‘β‘_ : β{β}{A : Set β}(x : A){y} β x β‘ y β x β‘ y
x β‘β‘ xβ‘y = xβ‘y

_β : β{β}{A : Set β}(a : A) β a β‘ a
a β = refl

_Γ_ : β{β}{β'}(A : Set β)(B : Set β') β Set (β β β')
A Γ B = Ξ£ A (Ξ» _ β B)

_,Γ=_ : β{β}{A : Set β}{β'}{B : Set β'}{a a' : A}(e : a β‘ a') β {b b' : B} β b  β‘ b' β (a , b) β‘ (a' , b')
_,Γ=_ refl refl = refl

module I where
  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty

  data Con  : Set where
    β       : Con              -- \di2
    _βΉ_     : Con β Ty β Con   -- \t6

  infixl 6 _β_
  infixl 6 _[_]
  infixl 5 _βΉ_
  infixl 5 _,o_
  infixl 7 _+o_

  postulate
    Sub       : Con β Con β Set
    _β_       : β{Ξ Ξ Ξ} β Sub Ξ Ξ β Sub Ξ Ξ β Sub Ξ Ξ
    ass       : β{Ξ Ξ Ξ Ξ}{Ξ³ : Sub Ξ Ξ}{Ξ΄ : Sub Ξ Ξ}{ΞΈ : Sub Ξ Ξ} β (Ξ³ β Ξ΄) β ΞΈ β‘ Ξ³ β (Ξ΄ β ΞΈ)
    id        : β{Ξ} β Sub Ξ Ξ
    idl       : β{Ξ Ξ}{Ξ³ : Sub Ξ Ξ} β id β Ξ³ β‘ Ξ³
    idr       : β{Ξ Ξ}{Ξ³ : Sub Ξ Ξ} β Ξ³ β id β‘ Ξ³

    Ξ΅         : β{Ξ} β Sub Ξ β
    βΞ·        : β{Ξ}{Ο : Sub Ξ β} β Ο β‘ Ξ΅

    Tm        : Con β Ty β Set
    _[_]      : β{Ξ Ξ A} β Tm Ξ A β Sub Ξ Ξ β Tm Ξ A
    [β]       : β{Ξ Ξ Ξ A}{t : Tm Ξ A}{Ξ³ : Sub Ξ Ξ}{Ξ΄ : Sub Ξ Ξ} β  t [ Ξ³ β Ξ΄ ] β‘ t [ Ξ³ ] [ Ξ΄ ]
    [id]      : β{Ξ A}{t : Tm Ξ A} β t [ id ] β‘ t
    _,o_      : β{Ξ Ξ A} β Sub Ξ Ξ β Tm Ξ A β Sub Ξ (Ξ βΉ A)
    p         : β{Ξ A} β Sub (Ξ βΉ A) Ξ
    q         : β{Ξ A} β Tm (Ξ βΉ A) A
    βΉΞ²β       : β{Ξ Ξ A}{Ξ³ : Sub Ξ Ξ}{t : Tm Ξ A} β p β (Ξ³ ,o t) β‘ Ξ³
    βΉΞ²β       : β{Ξ Ξ A}{Ξ³ : Sub Ξ Ξ}{t : Tm Ξ A} β q [ Ξ³ ,o t ] β‘ t
    βΉΞ·        : β{Ξ Ξ A}{Ξ³a : Sub Ξ (Ξ βΉ A)} β p β Ξ³a ,o q [ Ξ³a ] β‘ Ξ³a

    true      : β{Ξ} β Tm Ξ Bool
    false     : β{Ξ} β Tm Ξ Bool
    ite       : β{Ξ A} β Tm Ξ Bool β Tm Ξ A β Tm Ξ A β Tm Ξ A
    iteΞ²β     : β{Ξ A u v} β ite {Ξ}{A} true u v β‘ u
    iteΞ²β     : β{Ξ A u v} β ite {Ξ}{A} false u v β‘ v
    true[]    : β{Ξ Ξ}{Ξ³ : Sub Ξ Ξ} β true [ Ξ³ ] β‘ true
    false[]   : β{Ξ Ξ}{Ξ³ : Sub Ξ Ξ} β false [ Ξ³ ] β‘ false
    ite[]     : β{Ξ A t u v Ξ}{Ξ³ : Sub Ξ Ξ} β (ite {Ξ}{A} t u v) [ Ξ³ ] β‘ ite (t [ Ξ³ ]) (u [ Ξ³ ]) (v [ Ξ³ ])

    num       : β{Ξ} β β β Tm Ξ Nat
    isZero    : β{Ξ} β Tm Ξ Nat β Tm Ξ Bool
    _+o_      : β{Ξ} β Tm Ξ Nat β Tm Ξ Nat β Tm Ξ Nat
    isZeroΞ²β  : β{Ξ} β isZero (num {Ξ} 0) β‘ true
    isZeroΞ²β  : β{Ξ n} β isZero (num {Ξ} (1 + n)) β‘ false
    +Ξ²        : β{Ξ m n} β num {Ξ} m +o num n β‘ num (m + n)
    num[]     : β{Ξ n Ξ}{Ξ³ : Sub Ξ Ξ} β num n [ Ξ³ ] β‘ num n
    isZero[]  : β{Ξ t Ξ}{Ξ³ : Sub Ξ Ξ} β isZero t [ Ξ³ ] β‘ isZero (t [ Ξ³ ])
    +[]       : β{Ξ u v Ξ}{Ξ³ : Sub Ξ Ξ} β (u +o v) [ Ξ³ ] β‘ (u [ Ξ³ ]) +o (v [ Ξ³ ])

  v0 : {Ξ : Con} β {A : Ty} β Tm (Ξ βΉ A) A
  v0 = q
  v1 : {Ξ : Con} β {A B : Ty} β Tm (Ξ βΉ A βΉ B) A
  v1 = q [ p ]
  v2 : {Ξ : Con} β {A B C : Ty} β Tm (Ξ βΉ A βΉ B βΉ C) A
  v2 = q [ p β p ]
  v3 : {Ξ : Con} β {A B C D : Ty} β Tm (Ξ βΉ A βΉ B βΉ C βΉ D) A
  v3 = q [ p β p β p ]
  v4 : {Ξ : Con} β {A B C D E : Ty} β Tm (Ξ βΉ A βΉ B βΉ C βΉ D βΉ E) A
  v4 = q [ p β p β p β p ]
  v5 : {Ξ : Con} β {A B C D E F : Ty} β Tm (Ξ βΉ A βΉ B βΉ C βΉ D βΉ E βΉ F) A
  v5 = q [ p β p β p β p β p ]
  v6 : {Ξ : Con} β {A B C D E F G : Ty} β Tm (Ξ βΉ A βΉ B βΉ C βΉ D βΉ E βΉ F βΉ G) A
  v6 = q [ p β p β p β p β p β p ]
  v7 : {Ξ : Con} β {A B C D E F G H : Ty} β Tm (Ξ βΉ A βΉ B βΉ C βΉ D βΉ E βΉ F βΉ G βΉ H) A
  v7 = q [ p β p β p β p β p β p β p ]

  def : β{Ξ A B} β Tm Ξ A β Tm (Ξ βΉ A) B β Tm Ξ B
  def t u = u [ id ,o t ]

open I

{- END FIX -}
eq-1 : def true (ite v0 ((num 3) +o (num 1)) (num 2)) β‘ num {β} 4
eq-1 = 
  def true (ite v0 ((num 3) +o (num 1)) (num 2))
         β‘β¨ refl β©
  (ite q ((num 3) +o (num 1)) (num 2)) [ id ,o true ]
         β‘β¨ ite[] β©
  ite (q [ id ,o true ]) (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])
         β‘β¨ cong (Ξ» z β (ite z (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])))  βΉΞ²β β©
  ite (true) (num 3 +o num 1 [ id ,o true ]) (num 2 [ id ,o true ])
         β‘β¨ iteΞ²β β©
  ((num 3 +o num 1) [ id ,o true ])
         β‘β¨ cong (Ξ» z β z [ id ,o true ]) +Ξ² β©
  (num 4 [ id ,o true ])
         β‘β¨ num[] β©
  num 4 
         β

v1Ξ² : β{Ξ Ξ A B}{Ξ³ : Sub Ξ Ξ}{a : Tm Ξ A}{b : Tm Ξ B} β v1 [ Ξ³ ,o a ,o b ] β‘ a
v1Ξ² {Ξ} {Ξ} {A} {B} {Ξ³} {a} {b} = 
    q [ p ] [ Ξ³ ,o a ,o b ]
        β‘β¨ ([β])β»ΒΉ β©
    q [ p β (Ξ³ ,o a ,o b) ]
        β‘β¨ cong (Ξ» z β q [ z ]) βΉΞ²β β©
    q [ Ξ³ ,o a ]
        β‘β¨ βΉΞ²β β©
    a
        β

v2Ξ² : β{Ξ Ξ A B C}{Ξ³ : Sub Ξ Ξ}{a : Tm Ξ A}{b : Tm Ξ B}{c : Tm Ξ C} β v2 [ Ξ³ ,o a ,o b ,o c ] β‘ a
v2Ξ² {Ξ} {Ξ} {A} {B} {C} {Ξ³} {a} {b} {c} = 
    q [ p β p ] [ Ξ³ ,o a ,o b ,o c ] 
        β‘β¨ ([β])β»ΒΉ β©
    q [ (p β p) β (Ξ³ ,o a ,o b ,o c) ]
        β‘β¨ cong (Ξ» z β q [ z ]) ass β© 
    q [ p β (p β (Ξ³ ,o a ,o b ,o c)) ]
        β‘β¨ cong (Ξ» z β q [ p β z ]) βΉΞ²β β©
    q [ p β (Ξ³ ,o a ,o b) ]
        β‘β¨ cong (Ξ» z β q [ z ]) βΉΞ²β β©
    q [ Ξ³ ,o a ]
        β‘β¨ βΉΞ²β β©
    a 
        β

eq-2 : ite v1 (isZero v0) false [ Ξ΅ ,o true ,o num 0 ] β‘ true {β}
eq-2 = 
    ite (q [ p ]) (isZero q) false [ Ξ΅ ,o true ,o num zero ] 
        β‘β¨ ite[] β© 
    ite (q [ p ] [ Ξ΅ ,o true ,o num zero ]) (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ]) 
        β‘β¨ cong (Ξ» z β ite z (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ])) (([β])β»ΒΉ) β© 
    ite (q [ p β (Ξ΅ ,o true ,o num zero) ]) (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ])
        β‘β¨ cong (Ξ» z β ite (q [ z ]) (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ]))  βΉΞ²β β© 
    ite (q [ (Ξ΅ ,o true ) ]) (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ])
        β‘β¨ cong (Ξ» z β ite z (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ])) βΉΞ²β β© 
    ite true (isZero q [ Ξ΅ ,o true ,o num zero ]) (false [ Ξ΅ ,o true ,o num zero ])
        β‘β¨ iteΞ²β β© 
    (isZero q) [ Ξ΅ ,o true ,o num zero ]
        β‘β¨ isZero[] β© 
    isZero (q [ Ξ΅ ,o true ,o num zero ])
        β‘β¨ cong (Ξ» z β isZero z) βΉΞ²β β© 
    isZero (num zero)
        β‘β¨ isZeroΞ²β β© 
    true 
        β

eq-3 : isZero (ite v0 (num 1) v1) [ Ξ΅ ,o num 0 ,o false ] β‘ true {β}
eq-3 = {!!}

sub-eq-1 : {Ξ : Con} β {Ο Ξ΄ : Sub Ξ β} β Ο β‘ Ξ΄
sub-eq-1 {Ξ} {Ο} {Ξ΄} = Ο β‘β¨ (βΞ· {Ξ} {Ο}) β© Ξ΅ β‘β¨ (βΞ· {Ξ} {Ξ΄})β»ΒΉ β© Ξ΄ β

sub-eq-2 : {Ξ Ξ : Con} β {Ο : Sub Ξ Ξ} β Ξ΅ β Ο β‘ Ξ΅
sub-eq-2 = βΞ·

sub-eq-3 : Ξ΅ β‘ id
sub-eq-3 = (βΞ·)β»ΒΉ

sub-eq-4 : {Ξ : Con}{A : Ty} β (p ,o q) β‘ id {Ξ βΉ A}
sub-eq-4 = {!!}

sub-eq-5 : β{Ξ A} β (id β p ,o q) β‘ id {Ξ βΉ A}
sub-eq-5 = {!!}
