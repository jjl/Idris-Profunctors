module Data.Profunctor.Iso

import Data.Profunctor

-- infixl 1 &&
-- export
-- (&&) : a -> (a -> b) -> b
-- a && f = f a


||| A type-level function to make it easier to talk about "simple" `Lens`,
||| `Prism`, and `Iso`s
|||
||| ````idris example
||| fstStrLens : Profunctor p => Simple (Lens {p}) (String, String) String
||| fstStrLens = _1
||| ````
|||
export
Simple : (Type -> Type -> Type -> Type -> Type) -> Type -> Type -> Type
Simple t s a = t s s a a

export
preIso : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
preIso {p} s t a b = p a b -> p s t

||| An isomorphism family.
export
Iso : Profunctor p => Type -> Type -> Type -> Type -> Type
Iso = preIso

||| An isomorphism family that does not change types
export
Iso' : Profunctor p => Type -> Type -> Type
Iso' = Simple $ Iso {p}

||| Turns a coavariant and contravariant function into an `Iso`
export
iso : Profunctor p => (s -> a) -> (b -> t) -> Iso {p} s t a b
iso = dimap {p}

||| Builds an `Iso` useful for constructing a `Lens`
export
lensIso : Profunctor p =>
          (s -> a) -> (s -> b -> t) -> Iso {p} s t (a, s) (b, s)
lensIso gt = iso (\s => (gt s, s)) . uncurry . flip

--- TODO
-- ||| Builds an `Iso` useful for constructing a `Prism`
-- export
-- prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
--                            Iso {p} s t (Either t a) (Either t b)
-- prismIso = flip iso . either id . Delay

||| Convert an element of the first half of an iso to the second
export
forwards : Profunctor p => Iso {p=Forgotten a} s t a b -> s -> a
forwards i = runForget . i $ Forget id

||| Convert an element of the second half of an iso to the first
export
backwards : Profunctor p => Iso {p=Tagged} s t a b -> b -> t
backwards i = runTagged . i . Tag

||| An `Iso` between a function and it's arguments-flipped version
export
flipped : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                  (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

||| An `Iso` between a function and it's curried version
export
curried : Profunctor p => Iso {p} ((a, b) -> c) ((d, e) -> f)
                                  (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

||| An `Iso` between a function and it's uncurried version
export
uncurried : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                    ((a, b) -> c) ((d, e) -> f)
uncurried = iso uncurry curry

||| An `Iso` between a list and its reverse
export
reversed : Profunctor p => Iso {p} (List a) (List b) (List a) (List b)
reversed = iso reverse reverse

||| An `Iso` between a string and a list of its characters
export
packed : Profunctor p => Iso' {p} String (List Char)
packed = iso unpack pack

||| An `Iso` between a list of characters and its string
export
unpacked : Profunctor p => Iso' {p} (List Char) String
unpacked = iso pack unpack

-- TODO
-- ||| An `Iso` between a lazy variable and its strict form
-- export
-- motivated : Profunctor p => Iso {p} a b (Lazy a) (Lazy b)
-- motivated = iso Delay Force

-- TODO
-- ||| An `Iso` between a strict variable and its lazy form
-- export
-- unmotivated : Profunctor p => Iso {p} (Lazy a) (Lazy b) a b
-- unmotivated = iso Force Delay

-- TODO
-- ||| An `Iso` between an enumerable value and it's `Nat` representation
-- export
-- enum : (Profunctor p, Enum a) => Iso' {p} Nat a
-- enum = iso fromNat toNat

-- TODO
-- ||| An `Iso` between a `Nat` and its enumerable representation
-- export
-- denum : (Profunctor p, Enum a) => Iso' {p} a Nat
-- denum = iso toNat fromNat

-- TODO
-- export
-- mirrored : Profunctor p => Iso {p} (Either a b) (Either c d)
--                                    (Either b a) (Either d c)
-- mirrored = iso mirror mirror
