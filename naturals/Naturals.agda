module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


infixl 6  _+_  _∸_
infixl 7  _*_

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n


--Natural Numbers as binaries--------------------------------------------------

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

one : ℕ
one = suc zero

two : ℕ
two = suc (suc zero)

inc : Bin -> Bin
inc ⟨⟩ = _I ⟨⟩
inc (_O x) = _I x
inc (_I x) = _O (inc x)

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (_O x) = two * from x
from (_I x) = two * from x + one
