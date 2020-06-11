{-# OPTIONS --safe --without-K #-}
module Categories.Examples.Functor.Sets where

open import Categories.Functor using (Endofunctor)
open import Categories.Category.Instance.Sets

open import Function using (id; λ-; _$-)

import Data.List as List
import Data.List.Properties

ListFunctor : ∀ {o} → Endofunctor (Sets o)
ListFunctor = record
  { F₀ = List.List
  ; F₁ = List.map
  ; identity = map-id $-
  ; homomorphism = map-compose $-
  ; F-resp-≈ = λ f≈g → map-cong (λ- f≈g) $-
  }
  where
    open Data.List.Properties
