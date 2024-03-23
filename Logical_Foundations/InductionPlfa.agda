module InductionPlfa where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

--Lemma: ∀ m ∈ ℕ :  m + zero = m ----------------------------------------------
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m)⟩
    suc m
  ∎

--Lemma ∀ m n ∈ ℕ : m + suc n = suc (n + m) ------------------------------------
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

--Proposition: ∀ m n ∈ ℕ : m + n = n + m ------------------------------------
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

--We can use rewrite in order to simplify the proofs: --------------------------
+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p  rewrite +-assoc' m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity′ m = refl
+-comm' m (suc n) rewrite +-suc′ m n | +-comm' m n = refl

--Exercice: m + (n + p) ≡ n + (m + p) ------------------------------------------
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p =
  begin
    (suc m) + (n + p)
  ≡⟨(+-comm' (suc m) (n + p))⟩
    (n + p) + (suc m)
  ≡⟨(+-assoc' n p (suc m))⟩
    n + (p + (suc m))
  ≡⟨ cong (n +_) (+-comm' p (suc m))⟩
    refl

--Using rewrite: ---------------------------------------------------------------
+-swap' : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap' zero n p = refl
+-swap' (suc m) n p
  rewrite
    +-comm' (suc m) (n + p)
    | +-assoc' n p (suc m)
    | +-comm p (suc m) = refl

--Exercise: prove distributivity-----------------------------------------------
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p)⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    refl

--Exercise: prove that multiplication is associative------------------------------
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ (*-distrib-+ n (m * n) p) ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p)⟩
   n * p + m * (n * p)
  ≡⟨⟩
  refl

--Exercise: prove that multiplication is commutative---------------------------

--Lemma: ∀ n ∈ ℕ : n * 0 = 0 --------------------------------------------
*-identity : ∀ (n : ℕ) → n * zero ≡ zero
*-identity zero = refl
*-identity (suc n) rewrite *-identity n = refl

--Lemma: ∀ n m ∈ ℕ : m * (n + 1) = m * n + m-----------------------------------
*-suc : ∀ (m n : ℕ) → m * suc n ≡ (m * n) + m
*-suc zero n = refl
*-suc (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-suc m n)⟩
    (suc n) + ((m * n) + m)
  ≡⟨⟩
    suc (n + ((m * n) + m))
  ≡⟨ sym (+-suc n ((m * n) + m))⟩
    n + suc (m * n + m)
  ≡⟨ cong (n +_) (sym (+-suc (m * n) m))⟩
    n + (m * n + suc m)
  ≡⟨ sym (+-assoc n (m * n) (suc m))⟩
    n + (m * n) + suc m
  ≡⟨⟩
    (suc m) * n + suc m
  ≡⟨⟩
    refl


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n  rewrite *-identity n = refl
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n)⟩
    n + n * m
  ≡⟨(+-comm n (n * m))⟩
    n * m + n
  ≡⟨ sym (*-suc n m)⟩
    n * suc m
  ≡⟨⟩
    refl

*-comm' : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm' zero n rewrite *-identity n = refl
*-comm' (suc m) n
  rewrite
   *-comm' m n
   | +-comm n (n * m)
   | *-suc n m
   = refl
