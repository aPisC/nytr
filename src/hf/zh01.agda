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

t : Tm
{-
             >o
             / \
            /   \
          >o     >o
t =      / \     / \    
        /   \   /   \
     false  >o true  +o
           / \       / \
          /   \     /   \
      num 1  true  true num 2
-}
{- END FIX -}
t = (false >o (num 1 >o true)) >o (true >o (true >o num 2))
{- BEGIN FIX -}
test-t-1 : left (left t) ≡ false
test-t-1 = refl
test-t-2 : left (right t) ≡ true
test-t-2 = refl
test-t-3 : right (right (right t)) ≡ num 2
test-t-3 = refl
test-t-4 : left (right (left t)) ≡ num 1
test-t-4 = refl
test-t-5 : right (right (left t)) ≡ true
test-t-5 = refl
test-t-6 : right (right (right t)) ≡ num 2
test-t-6 = refl
test-t-7 : left (right (right t)) ≡ true
test-t-7 = refl
{- END FIX -}
