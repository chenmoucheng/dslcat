{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

-- | DSL with a categoric semantics

module Language.DSLCat
  ( DSLCat(..)
  , DSLSym(..)
  , Term
  , toHask
  , dynApp'
  , Sem(..)
  , toCat'
  ) where

import           Prelude hiding (curry, fst, id, lookup, snd, uncurry)
import qualified Prelude as P

import           Control.Category                  ((>>>), id)
import           Control.Category.Cartesian        (Cartesian(..))
import           Control.Category.Cartesian.Closed (CCC(..))
import           Control.Category.Monoidal         (Monoidal(..))
import           Data.Constraint                   (Dict(..))
import           Data.Dynamic                      (Dynamic(..), toDyn)
import           Data.Kind                         (Type)
import           Type.Reflection                   ( (:~~:)(..)
                                                   , Typeable
                                                   , TypeRep
                                                   , pattern App
                                                   , pattern Fun
                                                   , eqTypeRep
                                                   , typeOf
                                                   , typeRep
                                                   , typeRepKind
                                                   , withTypeable
                                                   )
import           Language.Syntactic.Functional     (BindingT(..), Let(..), Literal(..))
import           Language.Syntactic.Interpretation (Equality(..))
import           Language.Syntactic.Syntax         ((:->), (:+:)(..), AST(..), Full, DenResult, Signature, Symbol, Typed(..))
import GHC.IO.Handle.Types (Handle__)

--



-- | A semantics category @hom@ for our DSL

class
  ( CCC hom
  , Typeable hom
  , Typeable (Exp hom)
  , Typeable (Product hom)
  , Typeable (Id hom (Product hom))
  ) => DSLCat hom where

  -- | Embed a Haskell value into @hom@.
  primitiveO
    :: Typeable a
    => a
    -> hom ctx a

  -- | Embed a Haskell function into @hom@.
  primitiveA
    :: (Typeable a, Typeable b)
    => (a -> b)
    -> hom ctx (Exp hom a b)

instance DSLCat (->) where
  primitiveO = const
  primitiveA = const . ($)

-- | A symbol @sym@ with a categorical semantics

class Symbol sym => DSLSym sym where
  toCat :: (Signature sig, Typeable (DenResult sig), DSLCat hom) => sym sig -> Sem hom

-- | Examples:
--
-- >>> import Language.Syntactic.Syntax (injT)
-- >>> lam = injT @_ @BindingT $ LamT @Int @Int 1
-- >>> var = injT @_ @BindingT $ VarT @Int 1
-- >>> SemFull term = toCat' $ lam :$ var
-- >>> import Data.Dynamic (fromDynamic)
-- >>> fromDynamic @Int . dynApp' (toHask term) $ toDyn (42 :: Int)
-- Just 42

instance DSLSym BindingT where
  toCat (t :: BindingT sig) = case t of
    VarT _ -> SemFull $ TermAtom (`lookup` t) where
      lookup :: (DSLCat hom, Typeable as, Typeable a) => Ctx hom as -> Var a -> hom as a
      lookup Ctx1 _ = error "lookup: failed"
      lookup (Ctx vs v) u = case (eqTypeRep (typeOf v) (typeOf u), equal v u) of
        (Just HRefl, True) -> snd
        _ -> fst >>> lookup vs u
    LamT n -> case typeRep @(DenResult sig) of
      Fun (_ :: TypeRep a) _ -> SemMore $ elimTerm $ \b -> SemFull $ TermExpo $ curry . b . (`Ctx` VarT @a n)
      App (App arrow (_ :: TypeRep a)) _
        | Just HRefl <- eqTypeRep (typeRep @(->)) arrow
        -> SemMore $ elimTerm $ \b -> SemFull $ TermExpo $ curry . b . (`Ctx` VarT @a n)
      _ -> error "toCat @BindingT: failed"

-- | Example:
--
-- >>> import Language.Syntactic.Syntax (injT)
-- >>> zero = injT @_ @(Let :+: Literal) $ Literal @Int 0
-- >>> succ = injT @_ @(Let :+: Literal) $ Literal @(Int -> Int) (+ 1)
-- >>> app' = injT @_ @(Let :+: Literal) $ Let ""
-- >>> f |$| x = app' :$ x :$ f
-- >>> SemFull term = toCat' $ succ |$| zero
-- >>> import Data.Dynamic (fromDynamic)
-- >>> fromDynamic @Int $ toHask term
-- Just 1

instance DSLSym Let where
  toCat _ = SemMore $ elimTerm f where
    f :: (DSLCat hom, Typeable a) => Figure hom a -> Sem hom
    f a = SemMore $ \(TermExpo exp_ab) -> SemFull $ g $ h a exp_ab
    g :: forall hom b. (DSLCat hom, Typeable b) => Figure hom b -> Term hom
    g = TermAtom
    h :: forall hom a' a b. (DSLCat hom, Typeable a', Typeable a, Typeable b)
      => Figure hom a' -> Figure hom (Exp hom a b) -> Figure hom b
    h a exp_ab = case eqTypeRep (typeRep @a) (typeRep @a') of
      Just HRefl -> \ctx -> id &&& a ctx >>> uncurry (exp_ab ctx)
      _ -> error "toCat @Let: failed"

-- | Examples:
--
-- >>> SemFull term = toCat . Literal $ Prelude.id @Int
-- >>> :t term
-- term :: DSLCat hom => Term hom
-- >>> import Data.Dynamic (fromDynamic)
-- >>> fromDynamic @Int . dynApp' (toHask term) $ toDyn (42 :: Int)
-- Just 42
-- 

instance DSLSym Literal where
  toCat (Literal x) = case typeOf x of
    Fun (ta :: TypeRep a) (tb :: TypeRep b)
      | Just HRefl <- eqTypeRep (typeRep @Type) (typeRepKind ta)
      , Just HRefl <- eqTypeRep (typeRep @Type) (typeRepKind tb)
      , Dict <- withTypeable ta $ Dict @(Typeable a)
      , Dict <- withTypeable tb $ Dict @(Typeable b)
      -> SemFull $ TermExpo $ const $ primitiveA x
    App (App arrow (ta :: TypeRep a)) (tb :: TypeRep b)
      | Just HRefl <- eqTypeRep (typeRep @(->)) arrow
      , Just HRefl <- eqTypeRep (typeRep @Type) (typeRepKind tb)
      , Dict <- withTypeable ta $ Dict @(Typeable a)
      , Dict <- withTypeable tb $ Dict @(Typeable b)
      -> SemFull $ TermExpo $ const $ primitiveA x
    _ -> SemFull $ TermAtom $ const $ primitiveO x

instance (DSLSym sym1, DSLSym sym2) => DSLSym (sym1 :+: sym2) where
  toCat (InjL s) = toCat s
  toCat (InjR s) = toCat s

-- | (Typed) variables

type Var a = Typeable a => BindingT (Full a)

-- | Contexts in a semantics category @hom@ are proudcts @as@ of typed variables,
--   with the terminal object @Id@ representing the empty context.

data Ctx hom as where
  Ctx1 :: DSLCat hom => Ctx hom (Id hom (Product hom))
  Ctx :: (DSLCat hom, Typeable as, Typeable a) => Ctx hom as -> Var a -> Ctx hom (Product hom as a)

-- | A figure of type @a@ in a semantics category @hom@

type Figure hom a = forall as. (DSLCat hom, Typeable as, Typeable a) => Ctx hom as -> hom as a

-- | A term in a semantics category @hom@ is just an existential figure in @hom@.

data Term hom where
  TermAtom :: (DSLCat hom, Typeable a)             => Figure hom                a  -> Term hom
  TermExpo :: (DSLCat hom, Typeable a, Typeable b) => Figure hom     (Exp hom a b) -> Term hom
  TermProd :: (DSLCat hom, Typeable a, Typeable b) => Figure hom (Product hom a b) -> Term hom

instance DSLCat hom => Show (Term hom) where show = elimTerm $ show . typeOf . ($ Ctx1)

elimTerm :: DSLCat hom => (forall a. Typeable a => Figure hom a -> r) -> Term hom -> r
elimTerm f (TermAtom a) = f a
elimTerm f (TermExpo a) = f a
elimTerm f (TermProd a) = f a

-- | Bring a term back to Haskell.

toHask :: Term (->) -> Dynamic
toHask = elimTerm $ toDyn . ($ ()) . ($ Ctx1)

dynApp' :: Dynamic -> Dynamic -> Dynamic
dynApp' (Dynamic tf f) (Dynamic tx x) = case tf of
  Fun ta tb
    | Just HRefl <- eqTypeRep ta tx
    , Just HRefl <- eqTypeRep (typeRep @Type) (typeRepKind tb)
    -> Dynamic tb (f x)
  App (App arrow ta) tb
    | Just HRefl <- eqTypeRep ta tx
    , Just HRefl <- eqTypeRep (typeRep @(->)) arrow
    , Just HRefl <- eqTypeRep (typeRep @Type) (typeRepKind tb)
    -> Dynamic tb (f x)
  _ -> error "dynApp': failed"

-- | Semantics type of our DSL in its semantics category @hom@

data Sem hom where
  SemFull :: DSLCat hom =>  Term hom             -> Sem hom 
  SemMore :: DSLCat hom => (Term hom -> Sem hom) -> Sem hom

-- | Semantics of an abstract syntax tree in its semantics category @hom@

toCat' :: (DSLSym sym, Signature sig, DSLCat hom) => AST (Typed sym) sig -> Sem hom
toCat' (Sym (Typed s)) = toCat s
toCat' (s :$ t) = f x where
  SemMore f = toCat' s
  SemFull x = toCat' t
