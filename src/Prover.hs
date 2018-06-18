module Prover where

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
import Data.List ((\\), isInfixOf, intersperse)
import System.Process
import System.IO
import Literal
import Data.Char
import System.Timeout
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec as PC
import Text.ParserCombinators.Parsec.Language( LanguageDef(..), emptyDef )

lst3 (_,_,a) = a

-- Handling responses from external prover.

simplifyDef :: LanguageDef st
simplifyDef = emptyDef { P.reservedNames = ["Valid", "Invalid"] }

lexer :: P.TokenParser ()
lexer = P.makeTokenParser simplifyDef

reserved :: String -> Parser ()
reserved = P.reserved Prover.lexer

int :: Parser Integer
int = P.integer Prover.lexer

whiteSpace :: Parser ()
whiteSpace = P.whiteSpace Prover.lexer

validOrInvalid :: Parser Bool
validOrInvalid = do
  optional (PC.char '>')
  Prover.whiteSpace
  Prover.int
  PC.char ':'
  Prover.whiteSpace
  choice [ do { reserved "Valid"; return True }, do { reserved "Invalid"; return False } ]

findResponse :: Show a => Prover -> Parser a -> IO a
findResponse prover parser = do
  line <- hGetLine (outH prover)
  case parse parser "" line of
    Right b -> return b
    Left _ -> findResponse prover parser

printLines :: Prover -> IO ()
printLines p = do
  k <- timeout 3000000 (hGetLine (outH p))
  case k of
    Nothing -> popProver p
    Just l -> do {putStrLn l; printLines p}

-- Prover mechanics: pushing/popping, returning answers...

checkProver :: Prover -> [(AExp, Bool)] -> [AExp] -> IO ()
checkProver p ass [x] = do
  let e = (solveCase ass x)
  send p (formulaToString (toFormula e))
  printLines p
checkProver p ass (x:xs) = do
  case intsOnly x of
    True -> do
      send p (formulaToString (toFormula x))
      val <- findResponse p validOrInvalid
      checkProver p ((x, val):ass) xs
    False -> do
      let iN = isNot x
      let iC = hasCase x
      case iC of
        True -> do
          checkProver p ass ((solveCase ass x) : xs)
        False -> do
          pushProver p x
          checkProver p ((x,not $ iN):ass) xs

intsOnly x = intsOnly' x

intsOnly' (APrimOp _ es) = and (map (\e -> intsOnly e) es)
intsOnly' (AConApp c _) = (showSDocUnsafe $ ppr c) == "I#"
intsOnly' (ALit _) = True
intsOnly' (AGlobal v) = ('$' `elem` (showSDocUnsafe $ ppr v)) || (isPrimOp $ showSDocUnsafe $ ppr v)
intsOnly' (AApp e1 e2) = intsOnly e1 && intsOnly e2
intsOnly' _ = False

isNot e = case e of
  APrimOp NotOp _ -> True
  _ -> False

hasCase (ACase _ _ _) = True
hasCase (APrimOp _ es) = or (map (\e -> hasCase e) es)
hasCase _ = False

solveCase ass (APrimOp o es) = (APrimOp o (propagate ass es))

propagate _ [] = []
propagate ass (e@(APrimOp o es):x) = solveCase ass e : propagate ass x
propagate ass ((ACase sc var ps):x) = (case lookup sc ass of
  Just True -> find (DataAlt trueDataCon) ps
  Just False -> find (DataAlt falseDataCon) ps) : propagate ass x
propagate ass (e:es) = e : propagate ass es

find c [] = error (showSDocUnsafe $ ppr c)
find c ((c', _, r):ps) = if c == c' then r else find c ps

toBAD :: AExp -> [[AExp]]
toBAD tree@(ACase _ _ _) = map reverse $ traverse [] tree
  where
    traverse path (ACase sc v ps) =
      concat $
      map (\(c, _, r) ->
      if c == DataAlt trueDataCon then
        (traverse (sc:path) r) else
          if c == DataAlt falseDataCon then
            (traverse ((APrimOp NotOp [sc]):path) r)
            else (traverse path r)) ps
    traverse path (AApp _ a2) = traverse path a2
    traverse path (APrimOp _ es) = concatMap (traverse path) es
    traverse path (AConApp _ es) = concatMap (traverse path) es
    traverse path (ABad _) = [path]
    traverse path (ALam _ e) = [path] ++ toBAD e
    traverse _ _ = []
toBAD (APrimOp op es) = concatMap toBAD es
toBAD (ALam x e) = toBAD e
toBAD _ = [[]]

toString :: Outputable a => a -> String
toString = showSDocUnsafe . ppr

-- Prover interface

data Prover = P { inH, outH :: Handle }

send :: Prover -> String -> IO ()
send p s = do {putStrLn ("Sending: " ++ s); hPutStrLn (inH p) s}

pushProver :: Prover -> AExp -> IO ()
pushProver p aexp = send p (formulaToString (BGPush [toFormula aexp]))

popProver :: Prover -> IO ()
popProver p = send p (formulaToString BGPop)

stopProver :: Prover -> IO ()
stopProver (P { inH = pin, outH = pout }) = do { hClose pin; hClose pout }

startProver :: IO Prover
startProver = do
  (pin, pout, _, _) <- runInteractiveCommand "~/Simplify"
  hSetBuffering pin LineBuffering
  send (P { inH = pin, outH = pout }) "(PROMPT_OFF)"
  return (P { inH = pin, outH = pout })

-- AExp -> Formula

toFunc_maybe :: PrimOp -> Maybe String
toFunc_maybe op = case op of
  IntAddOp -> Just "+"
  IntSubOp -> Just "-"
  IntMulOp -> Just "*"
  IntGtOp  -> Just ">"
  IntGeOp  -> Just ">="
  IntEqOp  -> Just "=="
  IntNeOp  -> Just "/="
  IntLtOp  -> Just "<"
  IntLeOp  -> Just "<="
  NotOp    -> Just "not"
  OrOp     -> Just "or"
  AndOp    -> Just "and"
  XorOp    -> Just "xor"
  _ -> Nothing

isFunc :: PrimOp -> Bool
isFunc x = case toFunc_maybe x of
            Nothing -> False
            Just op -> elem op ["+", "-" , "*"]

isFLit :: PrimOp -> Bool
isFLit x = case toFunc_maybe x of
            Nothing -> False
            Just op -> elem op [">", ">=", "<", "<=", "==", "/="]

isFTerm :: AExp -> Bool
isFTerm (APrimOp op es) = isFunc op && (and (map isFTerm es))
isFTerm (ALit _) = True
isFTerm (AVar _) = True
isFTerm (AInside _ e) = isFTerm e
isFTerm (AApp e1 e2) = isFTerm e1 && isFTerm e2
isFTerm _ = False

isFormula :: AExp -> Bool
isFormula (APrimOp op es) = isFLit op && (and (map (\x-> isFormula x || isFTerm x) es))
isFormula (AInside _ e) = isFormula e
isFormula _ = False

flatApp :: AExp -> (Name, [AExp])
flatApp (AVar f) = (f, [])
flatApp (AGlobal i) = (idName i, [])
flatApp (AApp f a) = let (n,as) = flatApp f
               in (n, as++[a])
flatApp (AInside _ e) = flatApp e
flatApp others = error ("flatApp: "++ toString others)

toFTerm :: AExp -> FTerm
toFTerm (AInside _ e) = toFTerm e
toFTerm (ALit l) = case l of
                    MachInt i -> FInt i
toFTerm (AVar v)  =
  let
    x = getOccString v
    l = length x
  in if last x == '#' then FVar (take (l-1) x) else FVar (filter (\c -> ord c > 32 && c /= '\'') x)
toFTerm (APrimOp op es) =
  let
    fs = map toFTerm es
  in
    case toFunc_maybe op of
      Just p -> (FFunc p fs)
      Nothing -> FFunc (toString op) fs
toFTerm (AApp f a) =
  let
    (f1,as) = flatApp (AApp f a)
    as2 = map toFTerm as
  in
    (FFunc (filter (\c -> ord c > 32 && c /= '\'') (toString f1)) as2)
toFTerm (AGlobal x) = case '$' `elem` (toString x) of
  True -> BlankTerm
  False -> error ("toFTerm | AGlobal: "++ toString x)
toFTerm (AConApp c ps) = case '#' `elem` (toString c) of
  True -> toFTerm $ head ps
  False -> FFunc (toString c) (map toFTerm ps)
toFTerm others = error ("toFTerm: "++ toString others)

toFormula :: AExp -> Formula
toFormula (APrimOp op [e1,e2]) =
 let e11 = toFTerm e1
     e22 = toFTerm e2
 in case toFunc_maybe op of
   Just p ->
     case p of
       "==" -> FLit (FEq e11 e22)
       "/=" -> FNot (FLit (FEq e11 e22))
       "<"  -> FLit (FLt e11 e22)
       "<=" -> FLit (FLeq e11 e22)
       ">"  -> FLit (FGt e11 e22)
       ">=" -> FLit (FGeq e11 e22)
toFormula (APrimOp op es)
 = trace (toString es) $ let fs = map toFormula es
   in case toFunc_maybe op of
       Just p -> case p of
                  "not" -> FNot (head fs)
                  "and" -> FAnd fs
                  "or"  -> FOr fs
toFormula (AVar v) = BoolTerm (toFTerm (AVar v)) -- e.g. $res && True
toFormula (AApp (AVar v) e2) = (BoolTerm (toFTerm (AApp (AVar v) e2))) -- e.g. noT1 x
toFormula (AApp a1 a2) = BoolTerm (toFTerm (AApp a1 a2))
toFormula others = error ("toFormula others: " ++ toString others)

-- Formula & -> String functions (for Simplify)

data Formula = FAnd [Formula]
  | FOr [Formula]
  | FNot Formula
  | FLit FLiteral
  | BoolTerm FTerm
  | BGPush [Formula]
  | BGPop
  deriving (Show)

data FLiteral = FEq FTerm FTerm
  | FNeq FTerm FTerm
  | FLt  FTerm FTerm
  | FLeq FTerm FTerm
  | FGt  FTerm FTerm
  | FGeq FTerm FTerm
  | FTrue
  | FFalse
  deriving (Show)

data FTerm = FVar String
  | FInt Integer
  | FFunc String [FTerm] -- String |- PrimOp
  | BlankTerm
  deriving (Show)

formulaToString :: Formula -> String
formulaToString (FLit l) = fLitToString l
formulaToString (FNot t) = "(NOT " ++ formulaToString t ++ ")"
formulaToString (FAnd fs) = let fss = concat $ intersperse " " (map formulaToString fs)
                            in "(AND " ++ fss ++ ")"
formulaToString (BGPush fs) = let fss = concat $ intersperse " " (map formulaToString fs)
                              in "(BG_PUSH " ++ fss ++ ")"
formulaToString BGPop = "(BG_POP)"
formulaToString (BoolTerm t) = fTermToString t

fTermToString :: FTerm -> String
fTermToString (FInt i) = show i
fTermToString (FVar v) = v
fTermToString (FFunc op ts) = let tss = concat $ intersperse " " (map fTermToString ts)
            in "(" ++ op ++ " " ++ tss ++ ")"
fTermToString (BlankTerm) = ""

fLitToString :: FLiteral -> String
fLitToString FTrue = "TRUE"
fLitToString FFalse = "FALSE"
fLitToString (FEq t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(EQ "++ t1s ++ " " ++ t2s ++ ")"
fLitToString (FNeq t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(NOT (EQ "++ t1s ++ " " ++ t2s ++ "))"
fLitToString (FLt t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(< "++ t1s ++ " " ++ t2s ++ ")"
fLitToString (FLeq t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(<= "++ t1s ++ " " ++ t2s ++ ")"
fLitToString (FGt t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(> "++ t1s ++ " " ++ t2s ++ ")"
fLitToString (FGeq t1 t2) =
  let
    t1s = fTermToString t1
    t2s = fTermToString t2
  in
    "(>= "++ t1s ++ " " ++ t2s ++ ")"
