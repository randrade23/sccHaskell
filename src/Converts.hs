module Converts where

import CoreSyn
import DynFlags
import Control.Monad ((<=<))
import Outputable
import Literal
import PrimOp
import Name
import NameEnv
import DataCon
import Id
import Var
import Unique
import Data.List (intersperse)
import GHC
import GHC.Paths (libdir)
import HscTypes (mg_binds)
import Contract
import AExpData

okContract :: AExp
okContract = let e = (mkFCallName (mkUnique 'e' 0) "e")
                 b = (mkFCallName (mkUnique 'b' 0) "b")
                 u = (mkFCallName (mkUnique 'u' 0) "u")
             in (ALam e (ALam b (ALam u (AVar e))))

toADecls :: ContractEnv -> [CoreBind] -> [ADecl]
toADecls contracts binds
 = foldr (++) [] (map (toADecl contracts binds) binds)

toADecl :: ContractEnv -> [CoreBind] -> CoreBind -> [ADecl]
toADecl cEnv _ (NonRec f e)
  = let n = (idName f)
        c = lookupContractEnv cEnv n
  in
     case c of
     Nothing -> [ADef n (toAExp e) Nothing]
     Just x ->  [ADef n (toAExp e) (Just (toAExp x))]


toADecl cEnv _ (Rec fs)
  = map (\(f,e) ->  let n = (idName f)
                        c = lookupContractEnv cEnv n
                        t = case c of
                             Nothing -> Nothing
                             Just x -> Just (toAExp x)
                    in (ADef n (toAExp e) t)) fs

toAExp :: CoreExpr -> AExp
toAExp (Var i)
  | Just c <- isDataConWorkId_maybe i = AConApp c []
  | Just op <- isPrimOpId_maybe i     = APrimOp op []
  | isGlobalId i                      = case (showSDocUnsafe $ ppr i) == "error" of {True -> ABad Me; False -> AGlobal i}
  | isLocalId i                       = AVar (idName i)
  | otherwise                         = AVar (idName i)

toAExp (Lit i) = ALit i
toAExp (App e1 e2) =
  case e2 of
    Type _ -> toAExp e1
    _ -> case toAExp e1 of
          AConApp c es -> AConApp c (es ++ [toAExp e2])
          APrimOp op es -> APrimOp op (es ++ [toAExp e2])
          others -> AApp others (toAExp e2)
toAExp (Lam x e) | isTyVar x = toAExp e
                 | otherwise = ALam (idName x) (toAExp e)
toAExp (Let b e) = case b of
                     NonRec i a -> let n = (idName i)
                                   in ALet n (toAExp a) (toAExp e)
                     Rec xs -> ALetrec (map (\(a,b)->ADef (idName a) (toAExp b) Nothing) xs) (toAExp e)

toAExp (Case e n _ alts) = ACase (toAExp e) (idName n) (map toAAlt alts)
toAExp (Cast e _) = toAExp e
toAExp (Tick _ e) = toAExp e

toAAlt :: CoreAlt ->  AAlt
toAAlt (c,xs,e) = (c, map idName xs, toAExp e)
