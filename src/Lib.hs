module Lib where

import GHC
import GHC.Paths (libdir)
import HscTypes (mg_binds)
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
import Annotations

compileToCore :: String -> IO ([CoreBind])
compileToCore modName = runGhc (Just libdir) $ do
    setSessionDynFlags =<< getSessionDynFlags
    target <- guessTarget (modName) Nothing
    setTargets [target]
    load LoadAllTargets
    ds <- desugarModule <=< typecheckModule <=< parseModule <=< getModSummary $ mkModuleName modName
    return (mg_binds . coreModule $ ds)
