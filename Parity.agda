-- parity
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
    ZERO : zero even
    -- STEP is a dependent type. It depends on its parameters
    -- STEP : (x : ℕ) → x even → succ (succ x) even
    STEP : ∀ {x} → x even → succ (succ x) even

  private
    even-proof : {n m : ℕ} → n even → m even → (n + m) even
    even-proof ZERO b = b
    even-proof (STEP x) b = STEP (even-proof x b)

  data _odd : ℕ → Set where
    ONE  : (succ zero) odd
    STEP : ∀ {x} → x odd → succ (succ x) odd
{-
  _o+_ : {n m : ℕ} → n odd → n odd → (n + m) even
  ONE o+ ONE = succ (succ zero) even
  -- ONE o+ ONE = ((succ zero) + (succ zero)) even
  -- ONE o+ b = (ONE o+ b)
  -- STEP x o+ b = (x o+ b)
  -}
