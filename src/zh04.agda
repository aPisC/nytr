{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

module zh04 where

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

open I

zh1 : (A : Ty)(Ξ : Con)(a : Tm Ξ A) β a [ id β id ] β‘ a
zh1 A Ξ a =
{- END FIX -}
  a [ id β id ]
                  β‘β¨ cong (Ξ» z β a [ z ]) idl β©
  a [ id ]
                  β‘β¨ [id] β©
  a
                  β

{- BEGIN FIX -}
zh2 : (A : Ty)(B : Ty)(Ξ : Con)(a : Tm Ξ A)(b : Tm Ξ B) β (p β p) β (id ,o a ,o b) β‘ id
zh2 A B Ξ a b =
{- END FIX -}
  (p β p) β (id ,o a ,o b)
                  β‘β¨ ass β©
  p β (p β (id ,o a ,o b))
                  β‘β¨ cong (Ξ» z β p β z) βΉΞ²β β©
  p β (id ,o a)
                  β‘β¨ βΉΞ²β β©
  id
                  β
