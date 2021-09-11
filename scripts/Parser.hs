import Data.Tuple
import Control.Arrow
import Text.Parsec
import Text.Parsec.String

data Term = Var Int | Succ Term | X | Y
  deriving (Show)

data Form = Exists Form | Forall Form | And Form Form | Or Form Form |
            Member Term Term | Equal Term Term |
            Iff Form Form | Neg Form | Implies Form Form | False
  deriving (Show)

var :: Parser Term
var = Var . read <$> many1 digit

tsucc :: Parser Term
tsucc = string "succ" >> par term >>= return . Succ

par :: Parser a -> Parser a
par = between (char '(') (char ')')

term :: Parser Term
term = var <|> tsucc <|> (char 'X' >> return X) <|> (char 'Y' >> return Y)

unary :: String -> (Form -> Form) -> Parser Form
unary s op = do
  string s
  char '('
  f1 <- form
  char ')'
  return (op f1)

binary :: String -> (a -> a -> Form) -> Parser a -> Parser Form
binary s op p = do
  string s
  char '('
  f1 <- p
  char ','
  f2 <- p
  char ')'
  return (op f1 f2)

form :: Parser Form
form = choice
  [     try (unary "Ex" Exists)
  ,     unary "Fo" Forall
  ,     binary "A" And form
  ,     binary "O" Or form
  ,     try (binary "Im" Implies form)
  ,     binary "If" Iff form
  ,     binary "M" Member term
  ,     binary "Eq" Equal term
  ,     unary "Ne" Neg
  ]

depth :: Form -> Int
depth (Forall f) = 1 + depth f
depth (Exists f) = 1 + depth f
depth (And f f') = depth f `max` depth f'
depth (Or f f') = depth f `max` depth f'
depth (Iff f f') = depth f `max` depth f'
depth (Implies f f') = depth f `max` depth f'
depth (Neg f) = depth f
depth (Member _ _) = 0
depth (Equal _ _) = 0

parsear archivo = do
  texto <- readFile archivo
  let mform = parse form "" texto
  case mform of
    Left _ -> putStrLn "error"
    Right f -> putStrLn ("depth: " ++ show (depth f))
