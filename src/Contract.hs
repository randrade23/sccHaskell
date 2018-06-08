module Contract where

import CoreSyn
import DsMonad
import Name ( Name, NamedThing, getName, nameOccName, nameModule, mkSystemName, mkFCallName )
import NameEnv
import Outputable
import Language.Haskell.Meta
import Data.Either
import Language.Haskell.TH.Syntax
import OccName
import Unique
import Data.List ( delete, union )
import TysPrim
import Id
import MkId
import Literal
import Type
import PrimOp
import CoreUtils
import MkCore
import DataCon
import AExpData
import TysWiredIn

data HsContract
  = HsParContract HsContract -- (contract)
  | HsBaseContract String String -- {x | x > 0}
  | HsFunContract (Maybe String) HsContract HsContract -- x:{x | x > 0} -> {y | y = x + y}
  deriving (Show)

data Contract = C String HsContract  -- fname
  deriving Show

fst3 (a, _, _) = a
unRight (Right e) = e

contractToCoreContract :: [Name.Name] -> [ADecl] -> Contract -> CoreContract
contractToCoreContract ns bs (C fname c) = FullContract { contract_name = find ns fname, contract_body = fst3 $ desugarContract c uniquesL [] bs}
  where
    find [] fn = error (fn ++ " function has a contract, but is not declared")
    find (n:ns') fn = if (showSDocUnsafe $ ppr n) == fn then n else find ns' fn

mkLocalN i uni = (mkFCallName uni (show i))
mkLocalI n = mkLocalId n (mkTyVarTy alphaTyVar)

desugarContract :: HsContract -> [Unique] -> [(String, Unique)] -> [ADecl] -> (CoreExpr, [Unique], [(String, Unique)])
desugarContract (HsParContract c) uniques nbs bs = desugarContract c uniques nbs bs
desugarContract (HsBaseContract var ex) uniques nbs bs =
  let
    -- Select a new code unless the variable already exists, and create a new
    -- variable. Once it is created, remove the used code from the remaining
    -- codes list. This will ensure variables can be compared without any
    -- unexpected substitutions, since their codes will all be... unique.
    th = unFix $ unRight (parseExp ex)
    varOcc = mkVarOcc var
    uni = fromRight (uniques !! 0) (checkVar var nbs)
    remUnis' = delete uni uniques
    nv = mkSystemName uni varOcc
    x = mkLocalId nv (mkTyVarTy alphaTyVar)
    newBinds = (nbs ++ [(var, uni)])
    a = thToCore th newBinds bs
    eUni = remUnis' !! 0
    bUni = remUnis' !! 1
    uUni = remUnis' !! 2
    remUnis = tail $ tail $ tail remUnis'
    eV = mkSystemName eUni (mkVarOcc "e")
    bV = mkSystemName bUni (mkVarOcc "b")
    uV = mkSystemName uUni (mkVarOcc "u")
    e = mkLocalId eV (mkTyVarTy alphaTyVar)
    b = mkLocalId bV (mkTyVarTy alphaTyVar)
    u = mkLocalId uV (mkTyVarTy alphaTyVar)
    bt = mkApps (Var b) [Type (mkTyVarTy alphaTyVar)]
  in
    (mkLams [e,b,u] (mkIfThenElse (mkApps (mkLams [x] a) [Var e]) (Var e) bt), remUnis, newBinds)
desugarContract (HsFunContract m c1 c2) uniques nbs bs =
  let
    xUni = u2 !! 4
    nb = nbs ++ (case m of Just x -> [(x, xUni)]; Nothing -> [])
    (ds1, u1, b1) = desugarContract c1 uniques nb bs
    (ds2, u2, b2) = desugarContract c2 u1 b1 bs
    eUni = u2 !! 0
    bUni = u2 !! 1
    uUni = u2 !! 2
    vUni = u2 !! 3
    remUnis = tail $ tail $ tail $ tail $ tail u2
    e = mkLocalI $ mkLocalN "e" eUni
    b = mkLocalI $ mkLocalN "b" bUni
    u = mkLocalI $ mkLocalN "u" uUni
    v = mkLocalId (mkSystemName vUni (mkVarOcc "v")) (mkTyVarTy alphaTyVar)
    bt = Var b
    ut = Var u
  in
    case m of
      Just x -> let x' = mkLocalId (mkSystemName xUni (mkVarOcc x)) (mkTyVarTy alphaTyVar) in (mkLams [e,b,u,v] (mkLets [NonRec x' (mkApps ds1 [(Var v), ut, bt])] (mkApps ds2 [(mkApps (Var e) [Var x']), bt, ut])), remUnis, b2)
      Nothing -> (let x = mkApps ds1 [(Var v), ut, bt] in mkLams [e,b,u,v] (mkApps ds2 [(mkApps (Var e) [x]), bt, ut]), remUnis, b2)

checkVar :: String -> [(String, Unique)] -> Either String Unique
checkVar v [] = Left (v ++ " not found")
checkVar v (b:bs) = if v == fst b then Right (snd b) else checkVar v bs

unFix :: Exp -> Exp -- fixing fixity
unFix (ParensE x) = unFix x
unFix (UInfixE e1 op e2) = AppE (AppE op (unFix e1)) (unFix e2)
unFix (AppE e1 e2) = AppE (unFix e1) (unFix e2)
unFix e = e

transformLit (CharL c) = MachChar c
transformLit (IntegerL i) = MachInt i

isPrimOp :: String -> Bool
isPrimOp x = x `elem` ["+", "-", "*", ">", ">=", "==", "/=", "<", "<=", "not", "or", "and", "xor"]

matchWithOp :: String -> PrimOp
matchWithOp op = case op of
  "+" -> IntAddOp
  "-" -> IntSubOp
  "*" -> IntMulOp
  ">" -> IntGtOp
  ">=" -> IntGeOp
  "==" -> IntEqOp
  "/=" -> IntNeOp
  "<" -> IntLtOp
  "<=" -> IntLeOp
  "not" -> NotOp
  "or" -> OrOp
  "and" -> AndOp
  "xor" -> XorOp

thToCore :: Exp -> [(String, Unique)] -> [ADecl] -> CoreExpr
thToCore (VarE v) nbs bs = if (isPrimOp (show v)) then Var (mkPrimOpId (matchWithOp $ show v))
  else
    let
      unRight (Left x) = error x
      unRight (Right e) = e
      var = show v
      varOcc = mkVarOcc var
      findFName x [] = Left (x ++ " is not a function")
      findFName x (a:as) = if x == (showSDocUnsafe $ ppr $ getAName a) then Right $ mkVanillaGlobal (getAName a) (mkTyVarTy alphaTyVar)  else findFName x as
    in case (checkVar var nbs) of
      Right uni ->
        let
          nv = mkSystemName uni varOcc
          i = mkLocalId nv (mkTyVarTy alphaTyVar)
        in
          Var i
      Left _ ->  let nv = unRight $ (findFName var bs) in Var nv
  -- check if var v has already been instantiated (has its own unique code), if it does, we use it, otherwise make a new one
thToCore (LitE l) nbs _ = Lit (transformLit l)
thToCore (AppE e1 e2) nbs bs =
  let
    e1' = thToCore e1 nbs bs
    e2' = thToCore e2 nbs bs
  in
    App e1' e2'
thToCore (ConE x) _ _ = Var (dataConWorkId d)
  where
    d = case show x of
      "True" -> trueDataCon
      "False" -> falseDataCon
thToCore e _ _ = error (show e)

uniquesL = [mkUniqueGrimily x | x <- muls2] -- unique codes to generate new Core variables
muls2 = [2*x | x <- [9000..9100]]

data CoreContract = FullContract { contract_name :: Name.Name, contract_body :: CoreExpr }

type ContractEnv = NameEnv CoreContract

emptyContractEnv    :: ContractEnv
lookupContractEnv   :: ContractEnv -> Name.Name -> Maybe CoreExpr
extendContractEnv   :: ContractEnv -> Name.Name -> CoreExpr -> ContractEnv

emptyContractEnv = emptyNameEnv
extendContractEnv env name c = extendNameEnv env name (FullContract {contract_name = name, contract_body = c})
lookupContractEnv env name = case lookupNameEnv env name of
    Nothing -> Nothing
    Just c -> case c of (FullContract { contract_name = name, contract_body = body}) -> Just body

extendContractEnvList   :: ContractEnv -> [CoreContract] -> ContractEnv
extendContractEnvList env [] = env
extendContractEnvList env ((FullContract { contract_name = a, contract_body = b}):xs) = extendContractEnvList (extendContractEnv env a b) xs
