{-# LANGUAGE TemplateHaskell #-}

-- | Parse the lexed output into a sexp-tree, ready to be converted into terms.
module Sexp where

import Lexer

import Data.Functor.Foldable
import Text.Parsec
import Text.Show.Deriving

data SexpTreeF t r = SexpTreeF [r] | NodeF t
$(deriveShow1 'SexpTreeF)

type SexpTree t = Fix (SexpTreeF t)
pattern SexpTree r = Fix (SexpTreeF r)
pattern Node t = Fix (NodeF t)

type TokenTree = SexpTree Token

sexp :: TokParser [TokenTree] -> TokParser TokenTree
sexp = (SexpTree <$>) . between (expect OpenParen) (expect CloseParen)

node :: TokParser TokenTree
node = Node <$> notParen

notParen :: TokParser Token
notParen = tokenPrim show (\p _ _ -> p)
  (\t -> if (notElem t [OpenParen, CloseParen]) then Just t else Nothing)

sexpTree :: TokParser TokenTree
sexpTree = sexp (many sexpTree) <|> node
