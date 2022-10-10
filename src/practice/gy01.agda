{-# OPTIONS --prop --rewriting #-}

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-w : save (write) file
-- C-x C-c : close Emacs
-- C-space : start selecting text
-- M-w : Copy
-- C-w : Cut
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-\       : Switch Agda mode on-off
-- C-c C-l   : Typecheck
-- C-c C-n   : Normalise (use definitions as much as possible)
-- C-c C-d   : Deduce type
-- C-c C-,   : Goal type and context (variants: C-u C-u C-c C-, and C-u C-c C-, where you normalise or do not normalise the goal at all)
-- C-c C-.   : Goal type and context + inferred type of current expr
-- C-c C-SPC : Fill goal
-- C-c C-x = : Describe character at point
-- C-c C-c = : Pattern match


module gy01 where

open import Lib

-- Booleans

-- data 𝟚 : Set where
--   tt ff : 𝟚

example-bool : 𝟚
example-bool = tt

another-bool : 𝟚
another-bool = ff

-- idb

idb : 𝟚 → 𝟚
idb x = x

idb-test-1 : idb tt ≡ tt
idb-test-1 = refl

idb-test-2 : idb ff ≡ ff
idb-test-2 = refl

-- neg

neg : 𝟚 → 𝟚
neg x = if x then ff else tt

neg-test-1 : neg tt ≡ ff
neg-test-1 = refl

neg-test-2 : neg ff ≡ tt
neg-test-2 = refl

-- How many 𝟚 → 𝟚 functions are there?

-- or

or : 𝟚 → 𝟚 → 𝟚
or a b = if a then tt else b



or-test-1 : or tt tt ≡ tt
or-test-1 = refl

or-test-2 : or tt ff ≡ tt
or-test-2 = refl

or-test-3 : or ff tt ≡ tt
or-test-3 = refl

or-test-4 : or ff ff ≡ ff
or-test-4 = refl


-- and

and : 𝟚 → 𝟚 → 𝟚
and a b = if a then b else ff

and-test-1 : and tt tt ≡ tt
and-test-1 = refl

and-test-2 : and tt ff ≡ ff
and-test-2 = refl

and-test-3 : and ff tt ≡ ff
and-test-3 = refl

and-test-4 : and ff ff ≡ ff
and-test-4 = refl

-- xor

xor : 𝟚 → 𝟚 → 𝟚
xor = λ x → λ y → and (or x y) (neg (and x y))

xor-test-1 : xor tt tt ≡ ff
xor-test-1 = refl

xor-test-2 : xor tt ff ≡ tt
xor-test-2 = refl

xor-test-3 : xor ff tt ≡ tt
xor-test-3 = refl

xor-test-4 : xor ff ff ≡ ff
xor-test-4 = refl

-- Natural numbers

addTwo : ℕ → ℕ
addTwo =  2 +_

addTwo-test-1 : addTwo 0 ≡ 2
addTwo-test-1 = refl

addTwo-test-2 : addTwo 3 ≡ 5
addTwo-test-2 = refl

_*2+1 : ℕ → ℕ
n *2+1 = {!   !}

*2+1-test-1 : 3 *2+1 ≡ 7
*2+1-test-1 = refl

plus : {!!}
plus = {!!}

plus-idl : (n : ℕ) → plus 0 n ≡ n
plus-idl n = {!!}

plus-idr : (n : ℕ) → plus n 0 ≡ n
plus-idr n = {!!}

-- NatBool nyelv AST szinten

open import NatBoolAST

t1 : I.Tm
t1 = {!!}

t1-test : height t1 ≡ 3
t1-test = refl

t2 : I.Tm
t2 = {!!}

t2-test-1 : height t2 ≡ 3
t2-test-1 = refl

t2-test-2 : ¬ (t1 ≡ t2)
t2-test-2 ()

-- ird le ezeket data-val!

-- T ::= op0 | op1 T | op2 T T | op3 T T T | op4 T T T T

-- A ::= a | fb B
-- B ::= fa A

-- V ::= vzero | vsuc V
-- E ::= num N | E < E | E = E | var V
-- C ::= V := E | while E S | if E then S else S
-- S ::= empty | C colon S

-- kovetkezo: NatBoolAST modelleket megadni.
 