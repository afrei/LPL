{-# OPTIONS -Wall -fwarn-tabs #-}

{- Adam Freilich
CIS 670 Final Project
4.28.14 Final Version -}

{- LEXING/PARSING-}

{- I took this definition of parser types from 
https://github.com/cthulhu314/ParsecExample/blob/master/parser.hs
because I couldn't get parsec to install (I was having technical problems 
with cabal). The last function I took from there is integerParser -}

module Parser where 

import Control.Applicative
import Control.Monad
import Data.Char
import Types

data Parser a = P(String -> [(a,String)])

instance Functor Parser where
        fmap f m = m >>= \a -> return $ f a

instance Monad Parser where
        return a = P (\s -> [(a,s)])
        (>>=) (P m) f = P(\c -> m c >>= \(a,s) -> parse (f a) s)

instance Alternative Parser where
        empty = mzero
        (<|>) = mplus

instance MonadPlus Parser where
        mzero = P(\_ -> [])
        mplus (P a) (P b) = P(\s -> (a s) ++ (b s)) 

instance Applicative Parser where
        pure = return
        (<*>) mf ma = mf >>= \f -> ma >>= \a -> return $ f a

{-Basic Parsers-}

headOption :: [a] -> Maybe a
headOption (x:_) = Just x
headOption [] = Nothing

parse :: Parser t -> String -> [(t, String)]
parse (P m) = m

result :: Parser a -> String -> Maybe a
result m s = case headOption (parse m s) of
             Just(res,"") -> Just(res)
             _ -> Nothing

zero' ::  t -> t1 -> [a]
zero' _ _ = []

zero ::  t -> Parser a
zero a = P(zero' a)

item' :: [t] -> [(t, [t])]
item' (x:xs) = [(x,xs)]
item' [] = []

item :: Parser Char
item = P(item')

term :: Char -> Parser Char
term y = P(term' y)

term' :: Eq t => t -> [t] -> [(t, [t])]
term' y (x:xs) = if(x == y) then [(y,xs)] else [] 
term' _ [] = []

word :: String -> Parser String
word = sequence . map (term) 

digits :: Parser String
digits = some $ msum $ map term ['0'..'9']

integerParser :: Parser Integer
integerParser = fmap (read :: String -> Integer) digits

charIs :: (Char -> Bool) -> Parser Char
charIs f = do {x <- item; if f x then return x else mzero}

onInputReturn :: String -> a -> Parser a
onInputReturn str a = word str >> return a

spaces :: Parser String
spaces = do {x <- many $ charIs isSpace; return x}

{-Type Parsers-}

oneTParser :: Parser Type
oneTParser = onInputReturn "1" OneT

zeroTParser :: Parser Type
zeroTParser = onInputReturn "0" ZeroT

topTParser :: Parser Type
topTParser = onInputReturn "T" TopT

tensTParser :: Parser Type
tensTParser = do 
               typ1 <- spaces >> typeParser'
               typ2 <- spaces >> word "x" >> spaces >> typeParser'
               _    <- spaces
               return $ TensT typ1 typ2

bangTParser :: Parser Type
bangTParser = do 
               typ <- word "!" >> spaces >> typeParser'
               _   <- spaces
               return $ BangT typ

limpTParser :: Parser Type
limpTParser = do 
               typ1 <- spaces >> typeParser'
               typ2 <- spaces >> word "->" >> spaces >> typeParser'
               _    <- spaces
               return $ LimpT typ1 typ2

oplusTParser :: Parser Type
oplusTParser = do 
               typ1 <- spaces >> typeParser'
               typ2 <- spaces >> word "+" >> spaces >> typeParser'
               _    <- spaces
               return $ OplusT typ1 typ2

withTParser :: Parser Type
withTParser = do 
               typ1 <- spaces >> typeParser'
               typ2 <- spaces >> word "&" >> spaces >> typeParser'
               _    <- spaces
               return $ WithT typ1 typ2

atomicTParser :: Parser Type
atomicTParser = do 
                 char <- charIs (\x -> isAsciiUpper x && (x /= 'T'))
                 return $ Atomic [char]

basicTypeParser :: Parser Type
basicTypeParser = oneTParser <|> zeroTParser <|> topTParser <|> atomicTParser

compositeTypeParser :: Parser Type
compositeTypeParser =  withTParser  <|> bangTParser <|> limpTParser <|> 
                       oplusTParser <|> tensTParser

compositeTypeParser' :: Parser Type
compositeTypeParser' =  do 
                         ty <- word "(" >> spaces >> compositeTypeParser
                         _ <- spaces >> word ")"
                         return ty 

-- The bang case is there so that !!A or !!!A are possible types
-- which is necassery for compatibility with the show method
-- which was chosen because it looks pretty 
typeParser' :: Parser Type
typeParser' = compositeTypeParser' <|> bangTParser <|> basicTypeParser

typeParser :: Parser Type
typeParser = compositeTypeParser <|> basicTypeParser

{- Expression Parsers -} 

unitParser :: Parser Exp
unitParser = onInputReturn "<>" UnitE

zeroParser :: Parser Exp
zeroParser = (do 
              lvs <- word "[]" >> spaces >>  word "discarding" >> 
                    spaces >> word ":" >> many (spaces >> lVarParser)
              return $ TopE lvs)

pVarParser :: Parser PerVar
pVarParser = do 
             n   <- word "{u" >> integerParser
             typ <- spaces >> term ':' >> spaces >> typeParser
             _   <- spaces >> term '}'
             return $ PerVar n typ

lVarParser :: Parser LinVar
lVarParser = do 
             n   <- word "{x">> integerParser
             typ <- spaces >> term ':' >> spaces >> typeParser
             _   <- spaces >> term '}'
             return $ LinVar n typ

lVarEParser :: Parser Exp
lVarEParser = fmap LinVarE lVarParser

pVarEParser :: Parser Exp
pVarEParser = fmap PerVarE pVarParser

-- From here on out, expression parsers take an expression parser p as input
-- because the user will be able to name expressions in the repl
-- and they will need to be parsed but can appear anywhere in user input 
-- expressions. The parser p is our last resort. Think of it as empty from the
-- alternative instance for parser defined above. 
abortEParser :: Parser Exp -> Parser Exp
abortEParser p = do
                  ex  <- word "abort" >> spaces >> expParser' p
                  typ <- spaces >> word ":" >> spaces >> typeParser
                  lvs <- spaces >> word "discarding" >> spaces >> 
                         word ":" >> many (spaces >> lVarParser)
                  return $ AbortE ex typ lvs

inj1Parser :: Parser Exp -> Parser Exp
inj1Parser p = do
                ex <- word "inj1" >> spaces >> expParser' p
                ty <- spaces >> word "+" >> spaces >> typeParser
                return $ Inj1E ex ty

inj2Parser :: Parser Exp -> Parser Exp
inj2Parser p = do
                ty <- word "inj2" >> spaces >> typeParser
                ex <- spaces >> word "+" >> spaces >> expParser' p
                return $ Inj2E ty ex 

caseEParser :: Parser Exp -> Parser Exp
caseEParser p = do 
                 e  <- word "case" >> spaces >> expParser' p
                 x1 <- spaces >> word "of" >> spaces >> word "|" >>
                       spaces >> word "inj1" >> spaces >> lVarParser
                 e1 <- spaces >> word "." >> spaces >> expParser' p
                 x2 <- spaces >> word "|" >> spaces >> 
                                 word "inj2" >> spaces >> lVarParser
                 e2 <- spaces >> word "." >> spaces >> expParser' p
                 return $ CaseE e x1 e1 x2 e2

withEParser :: Parser Exp -> Parser Exp
withEParser p =  do
               e1 <- word "[" >> spaces >> expParser' p
               e2 <- spaces >> word "&" >> spaces >> expParser' p
               _  <- spaces >> word "]"
               return $ WithE e1 e2


prj1EParser :: Parser Exp -> Parser Exp
prj1EParser p = do
              ex <- word "prj1" >> spaces >> expParser' p
              return $ Prj1E ex 

prj2EParser :: Parser Exp -> Parser Exp
prj2EParser p = do
              ex <- word "prj2" >> spaces >> expParser' p
              return $ Prj2E ex 

letUEParser :: Parser Exp -> Parser Exp
letUEParser p =  do
                  e1 <- word "let" >> spaces >> word "<>" >> spaces >> 
                        word  "="  >> spaces >> expParser' p
                  e2 <- spaces >> word "in" >> spaces >> expParser' p
                  return $ LetUE e1 e2

tensEParser :: Parser Exp -> Parser Exp
tensEParser p =  do
                  e1 <- word "<" >> spaces >> expParser' p
                  e2 <- spaces >> word "x" >> spaces >> expParser' p
                  _ <- (spaces >> word ">")
                  return $ TensE e1 e2

letTensEParser :: Parser Exp -> Parser Exp
letTensEParser p = do 
                    x  <- word "let" >> spaces >> lVarParser
                    y  <- spaces >> word "x" >> spaces >> lVarParser
                    e1 <- spaces >> word "=" >> spaces >> expParser' p
                    e2 <- spaces >> word "in" >> spaces >> 
                                    word "" >> spaces >> expParser' p
                    return $ LetTensE x y e1 e2

lambdaEParser :: Parser Exp -> Parser Exp
lambdaEParser p = do 
                   x <- word "fun" >> spaces >> lVarParser 
                   e <- spaces >> word "." >> spaces >> expParser' p
                   return $ LambdaE x e

appEParser :: Parser Exp -> Parser Exp
appEParser p =  do
                 e1 <- expParser' p
                 e2 <- spaces >> word "$" >> spaces >> expParser' p
                 return $ AppE e1 e2

bangEParser :: Parser Exp -> Parser Exp
bangEParser p =  do
                  e1 <- word "!" >> spaces >> expParser' p
                  return $ BangE e1

letBangEParser :: Parser Exp -> Parser Exp
letBangEParser p = do 
                    x <- word "let !" >> pVarParser
                    e1 <- spaces >> word "=" >> spaces >> expParser' p
                    e2 <- spaces >> word "in" >> spaces >> expParser' p
                    return $ LetBangE x e1 e2

basicExpParser :: Parser Exp
basicExpParser = unitParser <|> lVarEParser <|> zeroParser <|> pVarEParser

compositeExpParser :: Parser Exp -> Parser Exp
compositeExpParser p  =  abortEParser p   <|> inj1Parser p     <|> inj2Parser p  <|>
                         caseEParser p    <|> withEParser p    <|> prj1EParser p <|>
                         prj2EParser p    <|> letUEParser p    <|> tensEParser p <|>
                         letTensEParser p <|> lambdaEParser p  <|> appEParser p  <|>
                         bangEParser p    <|> letBangEParser p

compositeExpParser' :: Parser Exp -> Parser Exp
compositeExpParser' p =  do 
                          ex <- word "(" >> spaces >> compositeExpParser p
                          _  <- spaces >> word ")"
                          return ex

basicExpParser' :: Parser Exp
basicExpParser' =  do 
                    ex <- word "(" >> spaces >> basicExpParser
                    _  <- spaces >> word ")"
                    return ex

-- The tensor case makes parsing compatible with showing
-- which works the way it does because it looks nice
expParser' :: Parser Exp -> Parser Exp
expParser' p =  compositeExpParser' p <|> tensEParser p <|> 
                basicExpParser <|> basicExpParser' <|> p

expParser :: Parser Exp -> Parser Exp
expParser p =  compositeExpParser p <|> expParser' p

finalExpParser :: Parser Exp
finalExpParser = expParser empty

-- Given a list of strings and what they map to, this parser
-- will interpret the given names. Useful in REPL. 
nameParser :: [(String, a)] -> Parser a
nameParser xs = foldr (<|>) empty $ map (uncurry onInputReturn) xs