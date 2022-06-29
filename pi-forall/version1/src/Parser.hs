{- pi-forall language -}

-- | A parsec-based parser for the concrete syntax
module Parser
  ( parseModuleFile,
    parseModuleImports,
    parseExpr,
    expr,
    decl,
    testParser,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State.Lazy hiding (join)
import Data.List (foldl')
import LayoutToken qualified as Token
import Syntax hiding (moduleImports)
import Text.Parsec hiding (Empty, State)
import Text.Parsec.Expr (Assoc (..), Operator (..), buildExpressionParser)
import Unbound.Generics.LocallyNameless qualified as Unbound

{-

Concrete syntax for the language:
Optional components in this BNF are marked with < >

  terms:
    a,b,A,B ::=
      Type                     Universes
    | x                        Variables   (start with lowercase)
    | \ x . a                  Function definition
    | a b                      Application
    | (x : A) -> B             Pi type

    | (a : A)                  Annotations
    | (a)                      Parens
    | TRUSTME                  An axiom 'TRUSTME', inhabits all types
    | PRINTME                  Show the current goal and context

    | let x = a in b           Let expression

    | Unit                     Unit type
    | ()                       Unit value

    | Bool                     Boolean type
    | True | False             Boolean values
    | if a then b else c       If

    | { x : A | B }            Dependent pair type
    | A * B                    Nondependent pair syntactic sugar
    | (a, b)                   Prod introduction
    | let (x,y) = a in b       Prod elimination

  declarations:

      foo : A
      foo = a

  Syntax sugar:

   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

-}

liftError :: (MonadError e m) => Either e a -> m a
liftError (Left e) = throwError e
liftError (Right a) = return a

-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleFile name = do
  liftIO $ putStrLn $ "Parsing File " ++ show name
  contents <- liftIO $ readFile name
  liftError $
    Unbound.runFreshM
      (runParserT (do whiteSpace; v <- moduleDef; eof; return v) [] name contents)

-- | Parse only the imports part of a module from the given filepath
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $
    Unbound.runFreshM $
      (runParserT (do whiteSpace; moduleImports) [] name contents)

-- | Test an 'LParser' on a String.
testParser :: LParser t -> String -> Either ParseError t
testParser parser str =
  Unbound.runFreshM $
    runParserT (do whiteSpace; v <- parser; eof; return v) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser expr

-- * Lexer definitions

type LParser a =
  ParsecT
    String -- The input is a sequence of Char
    [Column]
    ( -- The internal state for Layout tabs

      Unbound.FreshM -- The internal state for generating fresh names,
    )
    a -- the type of the object being parsed

instance Unbound.Fresh (ParsecT s u Unbound.FreshM) where
  fresh = lift . Unbound.fresh

-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type).
piforallStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
piforallStyle =
  Token.LanguageDef
    { Token.commentStart = "{-",
      Token.commentEnd = "-}",
      Token.commentLine = "--",
      Token.nestedComments = True,
      Token.identStart = letter,
      Token.identLetter = alphaNum <|> oneOf "_'",
      Token.opStart = oneOf ":!#$%&*+.,/<=>?@\\^|-",
      Token.opLetter = oneOf ":!#$%&*+.,/<=>?@\\^|-",
      Token.caseSensitive = True,
      Token.reservedNames =
        [ "Refl",
          "ind",
          "Type",
          "data",
          "where",
          "case",
          "of",
          "with",
          "contra",
          "subst",
          "by",
          "let",
          "in",
          "axiom",
          "TRUSTME",
          "PRINTME",
          "ord",
          "Bool",
          "True",
          "False",
          "if",
          "then",
          "else",
          "Unit",
          "()"
        ],
      Token.reservedOpNames =
        ["!", "?", "\\", ":", ".", ",", "<", "=", "+", "-", "*", "^", "()", "_", "|", "{", "}"]
    }

tokenizer :: Token.GenTokenParser String [Column] (Unbound.FreshM)
layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, Token.LayFun layout) = Token.makeTokenParser piforallStyle "{" ";" "}"

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser TName
variable =
  do
    i <- identifier
    return $ Unbound.string2Name i

colon, dot, comma :: LParser ()
colon = Token.colon tokenizer >> return ()
dot = Token.dot tokenizer >> return ()
comma = Token.comma tokenizer >> return ()

reserved, reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens, brackets, braces :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer
braces = Token.braces tokenizer

moduleImports :: LParser Module
moduleImports = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  return $ Module modName imports []

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())

  return $ Module modName imports decls

importDef :: LParser ModuleImport
importDef = do reserved "import" >> (ModuleImport <$> importName)
  where
    importName = identifier

---
--- Top level declarations
---

decl, sigDef, valDef :: LParser Decl
decl = sigDef <|> valDef
sigDef = do
  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  return (mkSig n ty)
valDef = do
  n <- try (do n <- variable; reservedOp "="; return n)
  val <- expr
  return $ Def n val

------------------------
------------------------
-- Terms
------------------------
------------------------

trustme :: LParser Term
trustme = reserved "TRUSTME" *> return (TrustMe)

printme :: LParser Term
printme = reserved "PRINTME" *> return (PrintMe)

-- Expressions

expr, term, factor :: LParser Term
-- expr is the toplevel expression grammar
expr = do
  p <- getPosition
  Pos p <$> buildExpressionParser table term
  where
    table =
      [ [ifixM AssocRight "->" mkArrowType],
        [ifixM AssocRight "*" mkTupleType]
      ]

    ifixM assoc op f = Infix (reservedOp op >> f) assoc
    mkArrowType =
      do
        n <- Unbound.fresh wildcardName
        return $ \tyA tyB ->
          Pi tyA (Unbound.bind n tyB)
    mkTupleType =
      do
        n <- Unbound.fresh wildcardName
        return $ \tyA tyB ->
          Sigma tyA (Unbound.bind n tyB)

-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = funapp

funapp :: LParser Term
funapp = do
  f <- factor
  foldl' app f <$> many bfactor
  where
    bfactor = factor
    app e1 e2 = App e1 e2

factor =
  choice
    [ Var <$> variable <?> "a variable",
      typen <?> "Type",
      lambda <?> "a lambda",
      try letPairExp <?> "a let pair",
      letExpr <?> "a let",
      trustme <?> "TRUSTME",
      printme <?> "PRINTME",
      bconst <?> "a constant",
      ifExpr <?> "an if expression",
      sigmaTy <?> "a sigma type",
      expProdOrAnnotOrParens
        <?> "an explicit function type or annotated expression"
    ]

typen :: LParser Term
typen =
  do
    reserved "Type"
    return Type

-- Lambda abstractions have the syntax '\x . e'
lambda :: LParser Term
lambda = do
  reservedOp "\\"
  binds <- many1 variable
  dot
  body <- expr
  return $ foldr lam body binds
  where
    lam x m = Lam (Unbound.bind x m)

bconst :: LParser Term
bconst =
  choice
    [ reserved "Bool" >> return TyBool,
      reserved "False" >> return (LitBool False),
      reserved "True" >> return (LitBool True),
      reserved "Unit" >> return TyUnit,
      reserved "()" >> return LitUnit
    ]

ifExpr :: LParser Term
ifExpr =
  do
    reserved "if"
    a <- expr
    reserved "then"
    b <- expr
    reserved "else"
    c <- expr
    return (If a b c)

--
letExpr :: LParser Term
letExpr =
  do
    reserved "let"
    x <- variable
    reservedOp "="
    rhs <- expr
    reserved "in"
    body <- expr
    return $ Let rhs (Unbound.bind x body)

letPairExp :: LParser Term
letPairExp = do
  reserved "let"
  reservedOp "("
  x <- variable
  reservedOp ","
  y <- variable
  reservedOp ")"
  reservedOp "="
  scrut <- expr
  reserved "in"
  a <- expr
  return $ LetPair scrut (Unbound.bind (x, y) a)

-- Function types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because these types, annotations and
-- regular old parens all start with parens.

data InParens = Colon Term Term | Comma Term Term | Nope Term

expProdOrAnnotOrParens :: LParser Term
expProdOrAnnotOrParens =
  let -- afterBinder picks up the return type of a pi
      afterBinder :: LParser Term
      afterBinder = do
        reservedOp "->"
        rest <- expr
        return rest

      -- before binder parses an expression in parens
      -- If it doesn't involve a colon, you get (Right tm)
      -- If it does, you get (Left tm1 tm2).  tm1 might be a variable,
      --    in which case you might be looking at an explicit pi type.
      beforeBinder :: LParser InParens
      beforeBinder =
        parens $
          choice
            [ do
                e1 <- try (term >>= (\e1 -> colon >> return e1))
                e2 <- expr
                return $ Colon e1 e2,
              do
                e1 <- try (term >>= (\e1 -> comma >> return e1))
                e2 <- expr
                return $ Comma e1 e2,
              Nope <$> expr
            ]
   in do
        bd <- beforeBinder
        case bd of
          Colon (Var x) a ->
            option
              (Ann (Var x) a)
              ( do
                  b <- afterBinder
                  return $ Pi a (Unbound.bind x b)
              )
          Colon a b -> return $ Ann a b
          Comma a b ->
            return $ Prod a b
          Nope a -> return a

sigmaTy :: LParser Term
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "|"
  b <- expr
  reservedOp "}"
  return (Sigma a (Unbound.bind x b))
