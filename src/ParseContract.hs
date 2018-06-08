module ParseContract where

import Contract
import Lib
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import CoreSyn

type P = Parser

lexer = Token.makeTokenParser emptyDef
identifier = Token.identifier lexer
whiteSpace = Token.whiteSpace lexer

contracts :: P [Contract]
contracts = many $ do
  fname <- identifier
  whiteSpace
  string "::"
  whiteSpace
  cont <- hsContract
  whiteSpace
  return $ C fname cont

hsContract :: P HsContract
hsContract =  (try funContract) <|> baseContract   -- TODO:  Tuple, Constructor, Any

baseContract :: P HsContract
baseContract = try (do
  char '{'
  whiteSpace
  var <- identifier
  whiteSpace
  exp <- between (char '|') (char '}') (many1 $ noneOf ("}"))
  return $ HsBaseContract var exp) <|> parContract

parContract :: P HsContract
parContract = do
  char '('
  whiteSpace
  h <- hsContract
  whiteSpace
  char ')'
  return $ HsParContract h

funContract :: P HsContract
funContract = do
  n <- optionMaybe (do {var <- identifier; char ':'; return var})
  l <- baseContract
  whiteSpace
  string "->"
  whiteSpace
  r <- hsContract
  return $ HsFunContract n l r

unVar (HsBaseContract v _) = v

parseString :: String -> [Contract]
parseString str =
   case parse contracts "" str of
     Left e  -> error $ show e
     Right r -> r
