{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

open import hf07import

open I

neg : {Γ : Con} → Tm Γ (Bool ⇒ Bool)
{- END FIX -}
neg = lam (ite v0 false true)

{- BEGIN FIX -}
xor : {Γ : Con} → Tm Γ (Bool ⇒ Bool ⇒ Bool)
{- END FIX -}
xor = lam (lam (ite v0 (neg $ v1) v1))

{- BEGIN FIX -}
isNotZero : ∀{Γ} → Tm Γ (Nat ⇒ Bool)
{- END FIX -}
isNotZero = lam  (neg $ (isZero v0) )

{- BEGIN FIX -}
get1 : ∀{Γ Δ Θ A B} → Sub Δ (Γ ▹ A ▹ B) → Sub Θ Δ → Tm Θ A
{- END FIX -}
get1 = {!!}

{- BEGIN FIX -}
get2 : ∀{Γ Δ Θ A B} → Sub Δ (Γ ▹ A ▹ B) → Sub Θ Δ → Tm Θ B
{- END FIX -}
get2 = {!!}

{- BEGIN FIX -}
module Tests where

  eval : {A : Ty} → Tm ◇ A → St.⟦ A ⟧T
  eval t = St.⟦ t ⟧t (mk triv)

  neg-test : eval (neg $ true) ≡ ff
  neg-test = refl
  neg-test' : eval (neg $ false) ≡ tt
  neg-test' = refl

  xor-test : eval (xor $ true $ true) ≡ ff
  xor-test = refl
  xor-test' : eval (xor $ false $ true) ≡ tt
  xor-test' = refl
  xor-test'' : eval (xor $ false $ false) ≡ ff
  xor-test'' = refl
  xor-test''' : eval (xor $ true $ false) ≡ tt
  xor-test''' = refl

  isNoteZero-test : eval (isNotZero $ num 0) ≡ ff
  isNoteZero-test = refl
  isNoteZero-test' : eval (isNotZero $ num 1) ≡ tt
  isNoteZero-test' = refl
  isNoteZero-test'' : eval (isNotZero $ num 2) ≡ tt
  isNoteZero-test'' = refl

  get1-test : eval (get1 (ε ,o num 1 ,o num 2) ε) ≡ 1
  get1-test = refl
  get1-test' : eval (get1 (ε ,o q ,o num 2) (ε ,o num 3)) ≡ 3
  get1-test' = refl

  get2-test : eval (get2 (ε ,o num 1 ,o num 2) ε) ≡ 2
  get2-test = refl
  get2-test' : eval (get2 (ε ,o num 1 ,o q) (ε ,o num 3 ,o num 2)) ≡ 2
  get2-test' = refl
  get2-test'' : eval (get2 (ε ,o num 1 ,o q [ p ]) (ε ,o num 3 ,o num 2)) ≡ 3
  get2-test'' = refl
{- END FIX -}
