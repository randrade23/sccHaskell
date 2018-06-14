module Main where

import Lib
import System.Environment
import Outputable
import Converts
import AExpData
import Contract
import Ppr
import DataCon
import TyCon
import CoreSyn
import PprCore
import Name
import TysWiredIn
import ParseContract
import Id
import PrimOp
import Prover
import MkCore
import Data.List ((\\), permutations)
import Control.Monad (replicateM)

main :: IO ()
main = do
  args <- getArgs
  -- stage one: parse core
  let mdl = (args !! 0)
  binds <- compileToCore mdl
  -- stage two: convert binds to different representation -- ADecl (AExp)
  -- this pass is redone in stage two but with the contracts.
  -- the reason we do this pass twice is that, in the first pass,
  -- it lets us get the Names associated with each function
  -- these Names come directly from GHC and we cannot "simulate" them.
  -- they are important to create the contract environment adequately
  let adeclsWithoutContracts = toADecls emptyContractEnv binds
  -- stage three: get contracts & match them with their functions
  contractFile <- readFile (mdl ++ ".cont")
  let funcNames = getANames adeclsWithoutContracts
  let parsedC = parseString contractFile
  let coreContracts = map (contractToCoreContract funcNames adeclsWithoutContracts) parsedC
  let cEnv = extendContractEnvList emptyContractEnv coreContracts
  let adeclsWithContracts = toADecls cEnv binds
  let unrolledAndSimplified = checkAndBuild cEnv 0 adeclsWithContracts adeclsWithContracts
  let badBranches = getBadPaths unrolledAndSimplified
  putStrLn (toString $ unrolledAndSimplified)
  putStrLn (toString $ badBranches)

getBadPaths :: [ADecl] -> [(Name, [[AExp]])]
getBadPaths = map (\(ADef f e t) -> (f, toBAD e))

simplDecl :: [ADecl] -> ADecl -> ADecl
simplDecl ds (ADef n e c) = (ADef n (fst $ simplify e [] ds) c)

type Eval = (AExp, CEnv)
type CEnv = [(AExp, AExp)] -- binding variables and scrutinees for constructor substitution

simplify e ds = simplify' e ds -- dummy for tracing.

simplify' :: AExp -> CEnv -> [ADecl] -> Eval
simplify' (AGlobal i) ce _ = (AGlobal i, ce)
simplify' (ALit l) ce _ = (ALit l, ce)
simplify' (NoTouch e) ce _ = (NoTouch e, ce)
simplify' (AVar v) ce _ = case lookup (AVar v) ce of
  Just e -> (NoTouch e,ce) -- prevent substitution into itself
  Nothing -> (AVar v, ce)
simplify' (AApp a1 a2) ce ds =
  let {a1' = (fst $ simplify a1 ce ds) ; a2' = (fst $ simplify a2 ce ds) }
  in
  (case a1' of
    ACase sc var alts -> (ACase (fst $ simplify sc ce ds) var (map (\(c, vs, r) -> (c, vs, fst$ simplify (AApp r a2') ce ds)) alts)) -- [CaseOut]
    _ -> case a2' of
      ACase sc var alts -> (ACase (fst $ simplify sc ce ds) var (map (\(c, vs, r) -> (c, vs, fst$ simplify (AApp a1' r) ce ds)) alts))
      NoTouch e -> apply a1' $! e
      _ -> apply a1' $! a2', ce)
simplify' (ALam n e) ce ds = let (a,b) = simplify e ce ds in (ALam n a, ce)
simplify' a@(APrimOp op es) ce ds = let es' = (map (fst . (\e -> simplify e ce ds)) es) in
  case es of
    ((ACase _ _ _) : _) -> simplify (pushIntoCase a) ce ds
    _ -> case hasUNR es' of
      True -> (AUnr Me,ce)
      False -> case hasBAD es' of
        True -> (ABad Me,ce)
        False -> (APrimOp op es',ce)
simplify' (AConApp dc es) ce ds = let es' = (map (fst . (\e -> simplify e ce ds)) es) in
  case hasUNR es' of
    True -> (AUnr Me, ce)
    False -> (AConApp dc es', ce)
simplify' ex@(ACase sc var as) ce ds = let alts = map (\(c,vs,r) -> (c,vs,fst $ simplify r ce' ds)) (filter notUnr as); (sc', ce') = simplify sc ce ds in
  case alts of
    [] -> (AUnr Me, ce')
    _ -> case sc of
        (NoTouch e) -> simplify' (ACase e var as) ce ds
        a@(AUnr _) -> (a, ce') -- [Ex-Case]
        a@(ABad _) -> (a, ce') -- [Ex-Case]
        ACase e0 n pis -> simplify (ACase e0 var (map (\(c,vs,r) -> (c, vs, fst $ simplify (ACase r n alts) ce ds)) pis)) ce ds
        AConApp c xs -> simplify (runDataAlt (DataAlt c) xs alts) ce' ds
        _ -> case Main.isFormula sc' of -- we'll leave formulas for later, when prover is on
          True -> (ACase sc' var alts, ce')
          False -> case lookup sc' ce' of -- is it solved? (in CEnv)
            Just (AConApp dc _) -> simplify (runDataAlt (DataAlt dc) [] alts) ce' ds
            Nothing -> rebuildCase var sc' alts ce' ds
simplify' (ALet n e' e) ce ds = simplify (subst e n e') ce ds -- reduce let into exp
simplify' p@(ARequires n e c) ce ds = simplify (projection p) ce ds
simplify' p@(AEnsures e c) ce ds = simplify (projection p) ce ds
simplify' e ce _ = (e,ce)

pushIntoCase (APrimOp op ((ACase e0 x alts):es)) = ACase e0 x (map (\(a,b,e1) -> (a,b,APrimOp op (e1:es))) alts)

projection (ARequires f e t) = (AApp (AApp (AApp t e) (AUnr (CallOf f))) (ABad (CallOf f)))
projection (AEnsures e t) = (AApp (AApp (AApp t e) (ABad Me)) (AUnr Me))

apply (ALam x e) v = subst e x v
apply e1 e2 = AApp e1 e2

subst a@(AGlobal _) _ _ = a
subst l@(ALit _) _ _ = l
subst (AVar y) x t
  | x == y = t
  | otherwise = AVar y
subst (ALam y e) x t
  | x == y = ALam y e
  | otherwise = ALam y (subst e x t)
subst (AApp e1 e2) x t = AApp (subst e1 x t) (subst e2 x t)
subst (APrimOp op es) x t = APrimOp op (map (\sub -> subst sub x t) es)
subst (AConApp dc es) x t = AConApp dc (map (\sub -> subst sub x t) es)
subst (ACase sc n alts) x t = ACase (subst sc x t) n (map (\(alt, name, exp) -> (alt, name, subst exp x t)) alts)
subst (ALetrec ds e) x t = ALetrec ds (subst e x t) -- might need changing
subst (ALet n e' e) x t = ALet n (subst e' x t) (subst e x t)
subst (ARequires n e c) x t = ARequires n (subst e x t) c
subst (AEnsures e c) x t = AEnsures (subst e x t) c
subst e _ _ = e

mSubst e [] = e
mSubst e ((a,b):xs) = mSubst (subst e a b) xs

findAlt :: AltCon -> [AAlt] -> Maybe AAlt
findAlt c alts = case [alt | alt@(c',_,_) <- alts, c==c'] of
       []     -> Nothing
       (alt:_) -> Just alt

runDataAlt c as alts = case findAlt c alts of
  Just (_, ns, r) -> mSubst r (zip ns as)
  _ -> case findAlt DEFAULT alts of
    Just (_, ns, r) -> mSubst r (zip ns as)
    _ -> AUnr Me

rebuildCase x e [(DEFAULT, _, r)] ce ds = (ACase e x [(DEFAULT, [], fst $ simplify r ce ds)], ce)
rebuildCase x e alts ce ds =
  (case filter notUnr alts' of
    [] -> AUnr Me
    _alts -> ACase e x _alts, nce)
      where
        (alts', nce) = simpl_alt' alts
        covered_cons = [c | (c,_,_) <- alts, c /= DEFAULT]
        afirst@(DataAlt first) = head covered_cons
        isLit = case afirst of LitAlt {} -> True; _ -> False
        all_cons = tyConDataCons (dataConTyCon first)
        missing_cons = all_cons \\ [dc | DataAlt dc <- covered_cons]
        simpl_alt' a = (map (fst . simpl_alt) a, concatMap (snd . simpl_alt) a)
        simpl_alt :: AAlt -> (AAlt, [(AExp, AExp)])
        simpl_alt (DEFAULT, ns, rhs)
          | isLit || length missing_cons > 1 -- if it's a literal, e.g. integer, it's out of our reach -- until we use a prover
          = ((DEFAULT, [], fst $ simplify rhs ce ds), ce)
          | null missing_cons -- no missing constructors & didn't match -- unreachable
          = ((DEFAULT, [], AUnr Me), ce)
          | otherwise
          = let [last_con] = missing_cons; nce' = (extendScrut ce ns e (DataAlt last_con))
            in ((DataAlt last_con, ns, fst (simplify rhs nce' ds)), nce)
        simpl_alt x@(c, ns, rhs) = ((c, ns, fst (simplify rhs' (extendScrut ce ns e c) ds)), snd (simplify rhs' (extendScrut ce ns e c) ds))
          where
            rhs' = rhs
        extendScrut :: [(AExp, AExp)] -> [Name] -> AExp -> AltCon -> [(AExp, AExp)]
        extendScrut ce ns scrut con@(DataAlt dcon) = case lookup scrut ce of
              Nothing -> ce ++ [(scrut, AConApp dcon (map AVar ns))]
              Just _ -> update scrut (AConApp dcon (map AVar ns)) ce

update k v [] = []
update k v ((k',v'):xs) = if k' == k then (k,v) : xs else (k',v') : (update k v xs)

hasUNR [] = False
hasUNR ((AUnr _):es) = True || hasUNR es
hasUNR ((AApp a1 a2):es) = hasUNR [a1] || hasUNR [a2] || hasUNR es
hasUNR ((APrimOp _ x):es) = hasUNR x || hasUNR es
hasUNR (e:es) = False || hasUNR es

hasBAD [] = False
hasBAD ((ABad _):es) = True || hasBAD es
hasBAD ((AApp a1 a2):es) = hasBAD [a1] || hasBAD [a2] || hasBAD es
hasBAD ((APrimOp _ x):es) = hasBAD x || hasBAD es
hasBAD (e:es) = False || hasBAD es

isFormula (APrimOp op es) = True
isFormula x = False

notUnr :: AAlt -> Bool
notUnr (_,_,c) = case c of
      (AUnr _) -> False
      _ -> True

findADef :: Name -> [ADecl] -> Maybe AExp
findADef _ [] = Nothing
findADef n ((ADef f e _):ds) = if f == n then Just e else findADef n ds

unrollCalls bl cEnv binds e = unrollCalls' bl cEnv binds e

-- bl -> blacklist for unrolling.
unrollCalls' bl cEnv binds (AGlobal i) =
  let
    v = (idName i)
    c = lookupContractEnv cEnv v
    rhs =
      case maybeUnfoldingTemplate (idUnfolding i) of
        { Nothing -> case findADef v binds of {Nothing -> (AGlobal i); Just x -> x} ; Just e -> (toAExp e) }
  in
    case v `elem` bl of {False -> case c of { Nothing -> rhs ; Just c' -> (ARequires v rhs (toAExp c')) } ; True -> (AGlobal i)}
unrollCalls' bl cEnv binds (AVar v) =
  case findADef v binds of
    Nothing -> (AVar v)
    Just rhs -> case lookupContractEnv cEnv v of
      Nothing -> rhs
      Just c -> case v `elem` bl of
        True -> rhs
        False -> ARequires v rhs (toAExp c)
unrollCalls' bl cEnv binds (AApp e1 (NoTouch e)) = AApp (unrollCalls bl cEnv binds e1) e
unrollCalls' bl cEnv binds (AApp e1 e2)     = AApp (unrollCalls bl cEnv binds e1) (unrollCalls bl cEnv binds e2)
unrollCalls' bl cEnv binds (ALam x e)       = ALam x (unrollCalls bl cEnv binds e)
unrollCalls' bl cEnv binds (ACase e x alts) =
  let
    e' = unrollCalls bl cEnv binds e
    alts' = map (\(a,b,c) -> (a,b,unrollCalls bl cEnv binds c)) alts
  in ACase e' x alts'
unrollCalls' bl cEnv binds (AConApp n es)   = AConApp n (map (\x -> unrollCalls bl cEnv binds x) es)
unrollCalls' bl cEnv binds (APrimOp n es)   = APrimOp n (map (\x -> unrollCalls bl cEnv binds x) es)
unrollCalls' bl cEnv binds e                = e

unrollFacts binds (AApp (AGlobal i) e@(AConApp _ _)) =
  let
    v = idName i
    fe = case findADef v binds of
      Nothing -> AGlobal i
      Just e -> e
  in
    AApp fe e
unrollFacts binds (AApp (AVar v) e@(AConApp _ _)) =
  let
    fe = case findADef v binds of
      Nothing -> AVar v
      Just e -> e
  in
    AApp fe e
unrollFacts bs (AApp a1 a2) = AApp (unrollFacts bs a1) a2
unrollFacts bs (ALam x e) = ALam x (unrollFacts bs e)
unrollFacts bs (ACase e x alts) =
  let
    e' = unrollFacts bs e
    alts' = map (\(a,b,c) -> (a,b,unrollFacts bs c)) alts
  in ACase e' x alts'
unrollFacts bs (AConApp c ds) = AConApp c (map (unrollFacts bs) ds)
unrollFacts bs (APrimOp c ds) = APrimOp c (map (unrollFacts bs) ds)
unrollFacts bs e = e

inlineContractDef :: ContractEnv -> AExp -> AExp
inlineContractDef cEnv ex =
  case ex of
    AGlobal i -> case (lookupContractEnv cEnv (idName i)) of
      Nothing -> (AGlobal i)
      Just c ->  (ARequires (idName i) (AGlobal i) (toAExp c))
    AVar v -> case (lookupContractEnv cEnv v) of
      Nothing -> AVar v
      Just c ->  (ARequires v (AVar v) (toAExp c))
    ALam x e -> ALam x (inlineContractDef cEnv e)
    AApp f a -> AApp (inlineContractDef cEnv f) (inlineContractDef cEnv a)
    APrimOp op es -> APrimOp op (map (inlineContractDef cEnv) es)
    AConApp c es -> AConApp c (map (inlineContractDef cEnv) es)
    ALet x r b -> ALet x (inlineContractDef cEnv r) (inlineContractDef cEnv b)
    ACase e0 x alts -> ACase (inlineContractDef cEnv e0) x (map (\(a,b,c) -> (a,b,inlineContractDef cEnv c)) alts)
    e -> e

checkAndBuild :: ContractEnv -> Int -> [ADecl] -> [ADecl] -> [ADecl]
checkAndBuild _ _ _ [] = []
checkAndBuild cEnv n bs ((ADef f e t):ds) =
  case t of
    Nothing ->
      let
        fbody = inlineContractDef cEnv e
        body2 = AEnsures fbody okContract
        a = checkAExp f bs cEnv n [] body2
      in
        (ADef f a (Just okContract)) : checkAndBuild cEnv n bs ds
    Just rt ->
      let
        fbody = inlineContractDef cEnv e
        body2 = AEnsures fbody rt
        a = checkAExp f bs cEnv n [] body2
      in
        (ADef f a t) : checkAndBuild cEnv n bs ds

simplifyF :: AExp -> CEnv -> [ADecl] -> (AExp, CEnv) -- simplify to a Fixed point
simplifyF e c d = let (a,b) = simplify e c d in if a == (fst $ simplify a b d) then (a,b) else simplifyF a b d

checkAExp :: Name -> [ADecl] -> ContractEnv -> Int -> CEnv -> AExp -> AExp
checkAExp _ ds _ 0 assume e =
  let
    k = fst $ simplifyF e assume ds
    n = fst $ simplifyF (unrollFacts ds k) assume ds
    --n = unrollFacts ds k
    --n = k
  in
    n
checkAExp f ds cEnv n assume e =
  let
    (x,ce) = simplifyF e assume ds
    unr = unrollCalls [f] cEnv ds x
  in
    checkAExp f ds cEnv (n-1) ce unr
