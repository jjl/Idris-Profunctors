module Data.Profunctor.Codensity

import Data.Profunctor
import Data.Profunctor.Composition

record Codense : (Type -> Type -> Type) -> Type -> Type -> Type where
  Codensity : {a : Type} -> {b : Type} -> {x : Type} -> (runCodensity : p x a -> p x b) -> Codense p a b

instance Profunctor p => Profunctor (Codense p) where
  dimap ca bd f = Codensity $ rmap bd . runCodensity f . rmap ca
  lmap  ca    f = Codensity $           runCodensity f . rmap ca
  rmap     bd f = Codensity $ rmap bd . runCodensity f

instance Profunctor p => Functor (Codense p a) where
  map bd f = Codensity $ rmap bd . runCodensity f
