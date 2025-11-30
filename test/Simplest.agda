module Simplest where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

plus : Nat → Nat → Nat
plus zero y = y
plus (suc x) y = suc (plus x y)