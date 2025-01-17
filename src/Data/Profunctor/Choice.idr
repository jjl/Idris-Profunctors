module Data.Profunctor.Choice

import Data.Profunctor
import Control.Category
import Control.Arrow
import Data.Morphisms

%default total

-- }}}
-- Choice
-- {{{

||| Generalized DownStar of a Costrong Functor
public export
interface Profunctor p => Choice (0 p : Type -> Type -> Type) where
  ||| Like first' but with sum rather than product types
  |||
  ||| ````idris example
  ||| left' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  left' : p a b -> p (Either a c) (Either b c)
  left' = dimap mirror mirror . right'

  ||| Like second' but with sum rather than product types
  |||
  ||| ````idris example
  ||| right' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  right' : p a b -> p (Either c a) (Either c b)
  right' = dimap mirror mirror . left'

export
Monad m => Choice (Kleislimorphism m) where
  left'  f = Kleisli $ either (applyKleisli       $ f        >>> arrow Left)
                              (applyKleisli       $ arrow id >>> arrow Right)
  right' f = Kleisli $ either (applyKleisli {f=m} $ arrow id >>> arrow Left)
                              (applyKleisli       $ f        >>> arrow Right)

export
Choice Morphism where
  left'  (Mor f) = Mor $ either (Left . f) Right
  right' (Mor f) = Mor $ either Left (Right . f)

export
Choice Tagged where
  left'  = Tag . Left  . runTagged
  right' = Tag . Right . runTagged

export
Applicative f => Choice (UpStarred f) where
  left'  (UpStar f) = UpStar $ either (map Left . f   ) (map Right . pure)
  right' (UpStar f) = UpStar $ either (map Left . pure) (map Right . f   )

export
Monoid r => Choice (Forgotten r) where
  left'  (Forget k) = Forget .      either k $ const neutral
  right' (Forget k) = Forget . flip either k $ const neutral
