{-# OPTIONS --prop --rewriting #-}

open import hf06import

-- hogy tudjuk a teljesseget hasznalni?

-- ezt peldakent megadjuk
e0 : num 3 +o ((num 2 +o num 9) +o num 1) ≡ num {◇} 15
e0 = compl (num 3 +o ((num 2 +o num 9) +o num 1)) ⁻¹

e1 : def true (ite v0 (num 3) (num 2) +o (num 1)) ≡ num {◇} 4
e1 = {!!}

e2 : ite v1 (isZero v0) false [ ε ,o true ,o num 0 ] ≡ true {◇}
e2 = {!!}

e3 : isZero (ite v0 (num 1) v1) [ ε ,o num 0 ,o false ] ≡ true {◇}
e3 = {!!}

-- ujabb pelda
e4 : num 3 +o num 2 ≡ num 1 +o num {◇} 4
e4 =
  num 3 +o num 2
                     ≡⟨ compl (num 3 +o num 2) ⁻¹ ⟩
  num 5
                     ≡⟨ compl (num 1 +o num 4) ⟩
  num 1 +o num 4
                     ∎

e5 : isZero (ite v0 (num 1) v1) [ ε ,o num 0 ,o false ] ≡ ite (isZero (num 0)) (true {◇}) false
e5 = {!!}

e6 : ite (isZero (num 2)) (num 3) (num 12) ≡ ite (isZero (num 0 +o num 0)) (num 12) (num {◇} 3)
e6 = {!!}

-- ha nem egyenlok
e7-helper : ¬ (numNf 5 ≡ numNf {◇} 3)
e7-helper ()

e7 : ¬ (num 2 +o num 3 ≡ num 1 +o num {◇} 2)
e7 e = e7-helper (cong norm e)

e8-helper : ∀{Γ : Con}{t : Ne Γ Bool} → ¬ (falseNf ≡ neu t)
e8-helper e = {!!}

e8 : ¬ (ite (isZero (num 1)) false false ≡ ite (q {◇}) false false)
e8 e = {!!}

e9-helper : {!!}
e9-helper = {!!}

e9 : ¬ (q {◇}{Nat} [ p ] ≡ q)
e9 e = {!!}
