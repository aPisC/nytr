{- BEGIN FIX -}
{-# OPTIONS --prop --rewriting #-}

open import hf06import

{- BEGIN FIX -}
zh01 : isZero (ite v0 (num 1) v1) [ ε ,o num 0 ,o false ] ≡ ite (isZero (num 1)) false (true {◇})
{- END FIX -}
zh01 = {!!}

{- BEGIN FIX -}
zh02-helper : ∀{Γ}{t : Ne Γ Bool} → ¬ (neu t ≡ falseNf)
{- END FIX -}
zh02-helper e = {!!}

{- BEGIN FIX -}
zh02 : ¬ (ite (q {◇}) false false ≡ false)
{- END FIX -}
zh02 e = {!!}
