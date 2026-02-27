module Idris.FunctorAsCFunctor

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategoryExtensional
import Utils

public export
functorOnMorphisms :
     {f : Type -> Type} -> VerifiedFunctor f
  => (a, b : Type)
  -> ExtensionalTypeMorphism a b
  -> ExtensionalTypeMorphism (f a) (f b)
functorOnMorphisms _ _ (MkExtensionalTypeMorphism g) = MkExtensionalTypeMorphism (map g)

public export
functorPreserveId :
     {f : Type -> Type} -> VerifiedFunctor f
  => (a : Type)
  -> functorOnMorphisms a a (extIdentity a) = extIdentity (f a)
functorPreserveId a = funExt (\x => functorIdentity id (\v => Refl) x)

public export
functorPreserveCompose :
     {f : Type -> Type} -> VerifiedFunctor f
  => (a, b, c : Type)
  -> (g : ExtensionalTypeMorphism a b)
  -> (h : ExtensionalTypeMorphism b c)
  -> functorOnMorphisms a c (extCompose a b c g h)
   = extCompose (f a) (f b) (f c) (functorOnMorphisms a b g) (functorOnMorphisms b c h)
functorPreserveCompose _ _ _ (MkExtensionalTypeMorphism g') (MkExtensionalTypeMorphism h')
  = funExt (\x => functorComposition x g' h')

public export
functorToCFunctor :
     {f : Type -> Type} ->
     VerifiedFunctor f
  => CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
              TypesAsCategoryExtensional.typesAsCategoryExtensional
functorToCFunctor = MkCFunctor
  f
  functorOnMorphisms
  functorPreserveId
  functorPreserveCompose
