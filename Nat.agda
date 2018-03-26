module Nat where
  -- propisitional equality
  infix 4 _≡_
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  -- _≡_ is symmetric
  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  -- _≡_ is transitive
  trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  -- _≡_ is congruent
  cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
  cong f refl = refl

  -- \bot ⊥
  -- False proposition
  data ⊥ : Set where

  -- input for ⊤ is \top
  -- True proposition
  record ⊤ : Set where

  -- ⊥ implies anything at any universe level
  ⊥-elim : ∀ {α} {A : Set α} → ⊥ → A
  ⊥-elim ()

  ¬ : ∀ {α} → Set α → Set α
  ¬ P = P → ⊥

  -- input for ∘ is \o
  -- Dependent composition
  _∘_ : ∀ {α β γ}
      → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ}
      → (f : {x : A} → (y : B x) → C y)
      → (g : (x : A) → B x)
      → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  -- Simple composition
  _∘′_ : ∀ {α β γ}
      → {A : Set α} {B : Set β} {C : Set γ}
      → (B → C) → (A → B) → (A → C)
  f ∘′ g = f ∘ g

  flip : ∀ {α β γ}
       → {A : Set α} {B : Set β} {C : A → B → Set γ} 
       → ((x : A) → (y : B) → C x y)
       → ((y : B) → (x : A) → C x y)
  flip f x y = f y x

  module DummyAB {α β} {A : Set α} {B : Set β} where
    contradiction : A → ¬ A → B
    contradiction a ¬a = ⊥-elim (¬a a)

    contraposition : (A → B) → (¬ B → ¬ A)
    contraposition = flip _∘′_

    contraposition¬ : (A → ¬ B) → (B → ¬ A)
    contraposition¬ = flip
  open DummyAB
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  infix 4 _≤_ _<_ _>_

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n}   → zero ≤ n
    s≤s : ∀ {n m} → n ≤ m → succ n ≤ succ m

  _<_ : ℕ → ℕ → Set
  n < m = succ n ≤ m

  _>_ : ℕ → ℕ → Set
  n > m = m < n

  
  ≤-unsucc : ∀ {n m} → succ n ≤ succ m → n ≤ m
  ≤-unsucc (s≤s a) = a

  -- a number is not less than itself
  <-¬refl : ∀ n → ¬ (n < n)
  <-¬refl zero ()
  <-¬refl (succ n) (s≤s p) = <-¬refl n p

  -- equality implies that it is also leq
  ≡→≤ : ∀ {n m} → n ≡ m → n ≤ m
  ≡→≤ {zero}   refl = z≤n
  ≡→≤ {succ n} refl = s≤s (≡→≤ {n} refl)

  -- equality implies it is not less than
  ≡→¬< : ∀ {n m} → n ≡ m → ¬ (n < m)
  ≡→¬< refl = <-¬refl _

  ≡→¬> : ∀ {n m} → n ≡ m → ¬ (n > m)
  ≡→¬> refl = <-¬refl _

  <→¬≡ : ∀ {n m} → n < m → ¬ (n ≡ m)
  <→¬≡ = contraposition¬ ≡→¬<

  >→¬≡ : ∀ {n m} → n > m → ¬ (n ≡ m)
  >→¬≡ = contraposition¬ ≡→¬>

  <→¬> : ∀ {n m} → n < m → ¬ (n > m)
  <→¬> {zero} (s≤s z≤n) ()
  <→¬> {succ n} (s≤s p<) p> = <→¬> p< (≤-unsucc p>)

  >→¬< : ∀ {n m} → n > m → ¬ (n < m)
  >→¬< = contraposition¬ <→¬>



  pred : ℕ → ℕ
  pred zero = zero
  pred (succ n) = n

  infixl 6 _+_
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  succ n + m = succ (n + m)

  infixr 7 _*_
  _*_ : ℕ → ℕ → ℕ
  zero   * m = zero
  succ n * m = m + (n * m)

  {-# BUILTIN EQUALITY _≡_ #-}
  
  private
    lemma-+zero : ∀ a → a + zero ≡ a
    lemma-+zero zero = refl
    lemma-+zero (succ a) rewrite lemma-+zero a = refl

--    l-zero : {n : ℕ} → (n + zero) → n
--    l-zero : ∀ {a : ℕ} → a + zero → a
--    l-zero (zero + zero) = zero
    -- l-zero ((succ a) + zero) = succ a


  data Bool : Set where
    true false : Bool

  -- 0 ≤ y is true for every y
  -- succ(x) ≤ y is false for every x
  -- succ(x) ≤ succ(y) is true if and only if x ≤ y
  -- x ≤ y is ∃z : x + z = y
  -- x < y is x ≤ y ∧ x ≠ y
  leq : ℕ → ℕ → Bool
  leq zero     zero     = true
  leq zero     (succ a) = true
  leq (succ a) zero     = false
  leq (succ a) (succ b) = leq a b
