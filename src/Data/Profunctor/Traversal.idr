module Data.Profunctor.Fold

import Data.Profunctor
import Data.Profunctor.Wander
import Data.Profunctor.Iso
import Data.Morphisms
import Data.Bitraversable
import Control.Monad.Identity

%default total

public export
Traversal : Wander p => Type -> Type -> Type -> Type -> Type
Traversal {p} = preIso {p}

||| A Traversal that does not change types
public export
Traversal' : Wander p => Type -> Type -> Type
Traversal' {p} = Simple $ Traversal {p}

public export
traversed : (Wander p, Traversable t) => Traversal {p} (t a) (t b) a b
traversed {t} = wander $ traverse {f=f1} {t}

public export
both : Bitraversable r => Traversal {p=Morphism} (r a a) (r b b) a b
both (Mor f) = Mor $ runIdentity . bitraverse {f=Identity} (Id . f) (Id . f) 
