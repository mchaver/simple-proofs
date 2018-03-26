module Parity where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (succ n) + m = succ (n + m)

  -- encode judgement even
  -- post fix argument
  data _even : ℕ → Set where
    Zero : zero even
    -- Step is a dependent type. It depends on its parameters
    -- Step : (x : ℕ) → x even → succ (succ x) even
    Even-Step : ∀ {x} → x even → succ (succ x) even

  private
    zero-is-zero-proof : zero even
    zero-is-zero-proof = Zero

    2-is-2-proof : succ (succ zero) even
    2-is-2-proof = Even-Step Zero

    1+1-is-2-proof : ((succ zero) + (succ zero)) even
    1+1-is-2-proof = Even-Step Zero

    2+2-is-4-proof : ((succ (succ zero)) + (succ (succ zero))) even
    2+2-is-4-proof = Even-Step (Even-Step Zero)

    even-plus-even-proof : {n m : ℕ} → n even → m even → (n + m) even
    even-plus-even-proof Zero b = b
    even-plus-even-proof (Even-Step x) b = Even-Step (even-plus-even-proof x b)

  data _odd : ℕ → Set where
    One  : (succ zero) odd
    Odd-Step : ∀ {x} → x odd → succ (succ x) odd

  private
    one-is-one-proof : succ zero odd
    one-is-one-proof = One

    3-is-3-proof : succ (succ (succ zero)) odd
    3-is-3-proof = Odd-Step One

    0+1-is-1-proof : (zero + (succ zero)) odd
    0+1-is-1-proof = One

    2+3-is-5-proof : ((succ (succ zero)) + (succ (succ (succ zero)))) odd
    2+3-is-5-proof = Odd-Step (Odd-Step One)

    odd-plus-odd-proof : {n m : ℕ} → n odd → m odd → (n + m) even
    odd-plus-odd-proof One One = Even-Step Zero
    odd-plus-odd-proof One (Odd-Step x) = Even-Step (odd-plus-odd-proof One x)
    odd-plus-odd-proof (Odd-Step x) b = Even-Step (odd-plus-odd-proof x b)


