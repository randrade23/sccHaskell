module AExpData where

import CoreSyn
import Name
import Id
import Literal
import PrimOp
import DataCon

getANames :: [ADecl] -> [Name]
getANames = map getAName

getAName :: ADecl -> Name
getAName (ADef f _ _) = f

getARHS :: ADecl -> AExp
getARHS (ADef _ e _) = e

data ADecl = ADef Name AExp (Maybe AExp) -- name of function, function def, contract (?)
     deriving (Eq)

data AExp
 = AVar Name
 | AGlobal Id
 | ALit Literal
 | AApp AExp AExp
 | ALam Name AExp
 | APrimOp PrimOp [AExp]
 | AConApp DataCon [AExp]
 | ACase AExp Name [AAlt]
 | ALetrec [ADecl] AExp
 | ALet Name AExp AExp
 | ARequires Name AExp AExp -- e <\ t
 | AEnsures AExp AExp  -- e \> t
 | AInside Name AExp
 | AUnr Blame
 | ABad Blame
 | NoTouch AExp -- don't unroll
 deriving (Eq)

data Blame = Me
          | CallOf Name
          deriving (Eq)

type AAlt = (CoreSyn.AltCon, [Name], AExp)
