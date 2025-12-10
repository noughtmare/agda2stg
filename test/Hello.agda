{-# OPTIONS --erasure #-}

-- erased things need no bindings
postulate
  @0 IO : Set → Set
  @0 ⊤ : Set
  @0 Char : Set

data String : Set where
  [] : String
  _∷_ : Char → String → String

-- interact is built in (for now)
postulate interact : (String → String) → IO ⊤

reverse : String → String → String
reverse s [] = s
reverse s (x ∷ xs) = reverse (x ∷ s) xs

main : IO ⊤
main = interact (reverse [])