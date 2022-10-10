{- BEGIN FIX -}

{- Toltsd ki a lyukakat! Csak a BEGIN FIX, END FIX regiokon kivuli reszekre irhatsz! -}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Agda.Builtin.Equality

data Tm : Set where
  true  : Tm
  false : Tm
  ite   : Tm → Tm → Tm → Tm
  num   : ℕ → Tm
  _+o_  : Tm → Tm → Tm
  _>o_  : Tm → Tm → Tm

left : Tm → Tm
left (t1 +o t2) = t1
left (t1 >o t2) = t1
left _          = true

right : Tm → Tm
right (t1 +o t2) = t2
right (t1 >o t2) = t2
right _          = true

t1 : Tm
{-
        +o
        / \
       /   \
t1 = true   >o
            / \
           /   \
        false  num 1
-}
{- END FIX -}
t1 = true +o (false >o num 1)
{- BEGIN FIX -}
test-t1-1 : left t1 ≡ true
test-t1-1 = refl
test-t1-2 : left (right t1) ≡ false
test-t1-2 = refl
test-t1-3 : right (right t1) ≡ num 1
test-t1-3 = refl

t2 : Tm
{-
             >o
             / \
            /   \
          +o     >o
t2 =     / \     / \    
        /   \   /   \
     true   >o true true
           / \
          /   \
       false  true
-}
{- END FIX -}
t2 = (true +o (false >o true)) >o (true >o true)
{- BEGIN FIX -}
test-t2-1 : left (left t2) ≡ true
test-t2-1 = refl
test-t2-2 : left (right t2) ≡ true
test-t2-2 = refl
test-t2-3 : right (right t2) ≡ true
test-t2-3 = refl
test-t2-4 : left (right (left t2)) ≡ false
test-t2-4 = refl
test-t2-5 : right (right (left t2)) ≡ true
test-t2-5 = refl

if_then_else_ : {A : Set} → 𝟚 → A → A → A
if tt then a else a' = a
if ff then a else a' = a'
to𝟚 : ℕ → 𝟚
to𝟚 0 = ff
to𝟚 _ = tt
eval : Tm → ℕ
eval true = 1
eval false = 0
eval (ite t t' t'') = if to𝟚 (eval t) then eval t' else eval t''
eval (num n) = n
eval (t +o t') = eval t + eval t'
eval (t >o t') = if eval t' < eval t then 1 else 0

isZero : Tm → Tm
{- END FIX -}
isZero (num zero) = true
isZero (num (suc x)) = false
isZero _ = false
{- BEGIN FIX -}
test-isZero-1 : eval (isZero (num 0)) ≡ 1
test-isZero-1 = refl
test-isZero-2 : eval (isZero (num 1)) ≡ 0
test-isZero-2 = refl
test-isZero-3 : eval (isZero (num 2)) ≡ 0
test-isZero-3 = refl
test-isZero-4 : eval (isZero (num 100)) ≡ 0
test-isZero-4 = refl

_≤o_ : Tm → Tm → Tm
{- END FIX -}
num zero ≤o num zero = true
num zero ≤o num (suc x₁) = true
num (suc x) ≤o num zero = false
num (suc x) ≤o num (suc x₁) = num x ≤o  num x₁
_ ≤o _ = false
{- BEGIN FIX -}
test-<o-1 : eval (num 3 ≤o num 3) ≡ 1
test-<o-1 = refl
test-<o-2 : eval (num 3 ≤o num 2) ≡ 0
test-<o-2 = refl
test-<o-3 : eval (num 0 ≤o num 100) ≡ 1
test-<o-3 = refl
test-<o-4 : eval (num 3 ≤o num 4) ≡ 1
test-<o-4 = refl
{- END FIX -}
