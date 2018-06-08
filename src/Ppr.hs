module Ppr where

import Outputable
import Converts
import Data.List (intersperse)
import CoreSyn
import Name
import AExpData
import Contract

instance Show AExp where
  show = showSDocUnsafe . ppr

pprADecls :: [ADecl] -> SDoc
pprADecls ds = vcat (intersperse (text "") (map ppr ds))

instance Outputable Blame where
  ppr Me = text "Me"
  ppr (CallOf n) = ppr n

instance Outputable ADecl where
  ppr (ADef f rhs t) = sep [ppr f, equals, ppr rhs, text "|>", ppr t]

instance Outputable AExp where
   ppr (AVar n)       = ppr n
   ppr (AGlobal i)    = ppr i
   ppr (ALit i)       = ppr i
   ppr (APrimOp op es)
    | length es == 2  = text "(" <> ppr (head es) <+> ppr op <+> ppr (head (tail es)) <> text ")"
    | otherwise       = text "(" <> ppr op <+> hsep (map ppr es) <> text ")"
   ppr (AConApp n es)
    | length es == 2 = text "(" <> ppr (head es) <+> ppr n <+> ppr (head (tail es)) <> text ")"
    | otherwise      = text "(" <> ppr n <+> hsep (map ppr es) <> text ")"
   ppr (AApp e1 e2)   = pprAApp (AApp e1 e2)
   ppr (ALam e x)     = char '\\' <> ppr e <> text "." <+> ppr x
   ppr (ALet v rhs b) = pprALets (ALet v rhs b)
   ppr (ALetrec es b) = pprALets (ALetrec es b)
   ppr (ACase e n alts) = vcat[ hsep [text "case", ppr e, text "of", ppr n] , nest 2 (vcat (map pprAlt alts)) ]
   ppr (AUnr n) = text "UNR" <+> ppr n
   ppr (ABad n) = text "BAD" <+> ppr n
   ppr (ARequires _ e t) = sep [text "(" <+> ppr e <+> text ")" , text "<|", ppr t]
   ppr (AEnsures e t) = sep [text "(" <+> ppr e <+> text ")",  text "|>", ppr t]
   ppr (NoTouch e)    = text "(NoTouch " <+> ppr e <> text ")"

pprAlt (c, ns, rhs) = hsep [ppr c, hsep (map ppr ns), text "->", ppr rhs]

pprAApp :: AExp -> SDoc
pprAApp e = go e []
  where
    go (AApp e1 e2) es = go e1 (e2:es)
    go e' es = pprParendExp e' <+> hsep (map pprParendExp es)

pprALets :: AExp -> SDoc
pprALets e = go e []
  where
    go (ALet v r b) bs = go b ((ppr v <+> text "=" <+> ppr r) : bs)
    go (ALetrec es b) bs = go b ((foldr (++) []
     (map (\(ADef v r t) ->
        [ppr v <+> text "=" <+> ppr r,
         ppr v <+> text "::" <+> ppr t]) es))  ++ bs)
    go other bs = vcat [text "let" <+> vcat (reverse bs) , text "in" <+> ppr other]

pprParendExp :: AExp -> SDoc
pprParendExp e
  | atomicExp e = ppr e
  | otherwise   = parens (ppr e)

atomicExp :: AExp -> Bool
atomicExp (AVar _) = True
atomicExp (AGlobal _) = True
atomicExp (ALit _) = True
atomicExp (AConApp _ []) = True
atomicExp _ = False

instance Outputable (CoreContract) where
   ppr (FullContract {contract_name = n, contract_body = b}) = ppr n <+> text " " <+> ppr b
