-- file: LambdaParser.hs
-- author: William Hilton
-- date: May 2014
import Data.List

{- Lambda Calculus BNF (with full syntax including parentheses)

  <letter> = [a-z,A-Z,0-9]
  <var> ::= <letter>|<letter><var>
  <abs> ::= /<var>.<term>
  <apl> ::= (<term> <term>)
  <term> ::= <var>|<abs>|<apl>

  Comments: 
  I chose '/' for lambda instead of '\' because the backslash already 
  has a unique meaning in strings.
-}

-- Here we define the abstract syntax, the desired end result of parsing a string.
legalVarChars = ['a'..'z']++['A'..'Z']++['0'..'9']
type Variable = String --technically a subset of string, but string will suffice.
data Term = Epsilon
          | Var Variable
          | Abstraction Variable Term
          | Application Term Term
          deriving (Show, Eq)

-------------------------------------------------------------------------
-- P A R S E R
-------------------------------------------------------------------------
-- Let's make a parser!
type Result = (Term, String)
type Parser = Result -> Result

-- Somehow, this name is both inappropriate and appropriate.
shitshow :: String -> IO ()
shitshow s = case (parseTerm (Epsilon, s) id) of
               (t,"") -> print t
               (t,s) -> print t >> putStr "Leftovers: " >> print s

parse :: String -> Term
parse s = case (parseTerm (Epsilon,s) id) of 
            (t,"") -> t
            (t,s) -> error "Incomplete Parse"

parseTerm :: Result -> Parser -> Result
parseTerm txs@(_,('(':xs)) p = parseApplication txs p
parseTerm txs@(_,('/':xs)) p = parseAbstraction txs p
parseTerm txs@(_,(a:xs)) p | elem a legalVarChars = parseVariable txs p
parseTerm (_,(_:xs)) p = error "parseTerm: shit happened."

-- Note: the leading '(' has already been removed from the input.
parseApplication :: Result -> Parser -> Result
parseApplication txs p = p $ parseChar '(' txs $
                       \paren -> parseTerm paren $ 
                       \t1 -> parseChar ' ' t1 $
                       \space -> parseTerm space $
                       \t2 -> parseChar ')' t2 $
                       \paren -> ((Application (fst t1) (fst t2)),(snd paren))

-- Note, the leading '/' has already been removed from the input.
parseAbstraction :: Result -> Parser -> Result
parseAbstraction txs p = p $ parseChar '/' txs $
                       \slash -> parseVariable slash $ 
                       \var -> parseChar '.' var $ 
                       \dot -> parseTerm dot $ 
                       \term -> ((Abstraction (resultToVariable var) (fst term)), (snd term))

parseVariable :: Result -> Parser -> Result
parseVariable (_,xs) p = p (parseVariable' "" xs)

parseVariable' :: String -> String -> Result
parseVariable' var (x:xs) | elem x legalVarChars = parseVariable' (var++[x]) xs
                          | otherwise       = ((Var var), x:xs)
parseVariable' var "" = ((Var var), "")

resultToVariable :: Result -> Variable
resultToVariable ((Var x),_) = x

parseCloseParen :: Result -> Parser -> Result
parseCloseParen (_,(')':xs)) p = p (Epsilon,xs)
parseCloseParen (_,(_:xs)) p = error "parseCloseParen: shit happened."

parseChar :: Char -> Result -> Parser -> Result
parseChar c (_,(x:xs)) p | c == x = p (Epsilon,xs)
                         | otherwise = error ("parseChar expected a '" ++ [c] ++ "' but saw a '" ++ [x] 
                                              ++ "' in '" ++ (x:xs) ++ "'")

-------------------------------------------------------------------------
-- P R I N T E R
-------------------------------------------------------------------------
-- Because reverse parsers are cool
format :: Term -> String
format (Var a) = a
format (Abstraction var body) = "/" ++ var ++ "." ++ (format body)
format (Application t1 t2) = "(" ++ (format t1) ++ " " ++ (format t2) ++ ")"

-------------------------------------------------------------------------
-- E V A L U A T O R
-------------------------------------------------------------------------
-- Return a list of all unbounded variables in an expression
freeVars :: Term -> [Variable]
freeVars(Var a) = [a]
-- Note: This is the "list difference operator"
freeVars(Abstraction var body) = freeVars(body) \\ [var]
-- Note: by using union we guarantee no duplicates
freeVars(Application term1 term2) = (freeVars term1) `union` (freeVars term2)

-- A "normal form" is a term that cannot be evaluated any further.
isNormalForm :: Term -> Bool
isNormalForm t@(Var _) = True
isNormalForm t@(Application f g) = isStuck t
isNormalForm t@(Abstraction _ f) = isNormalForm f
isNormalForm _ = False

-- A value is a "good" normal form.
isValue :: Term -> Bool
isValue (Abstraction _ body) = isNormalForm body
isValue _ = False

-- A stuck term is a "bad" normal form.
isStuck :: Term -> Bool
isStuck (Var _) = True
isStuck (Abstraction _ _) = False
isStuck (Application a _) = isStuck a

-- Step a term until it is in normal form.
reduce :: Term -> Term
reduce t | isNormalForm t = t
         | otherwise = reduce (step t)

-- Like reduce, but displays the lambda expression at each step.
eval :: Term -> IO ()
eval t | isNormalForm t = putStrLn (format t)      -- Stop when we can step no further*
       | otherwise = do putStrLn (format t); eval (step t)

-- Like eval, but for the even lazier since it takes a string input, not a term.
cal :: String -> IO ()
cal s = eval (parse s)

-- Small step semantics for lambda calculus
step :: Term -> Term
step t@(Var a) = t
step t@(Abstraction var body) = t
-- Step by function evaluation. I chose lazy (call by name) evaluation, so term is not reduced first.
step t@(Application (Abstraction var body) term) = betasub var term body
step t@(Application term1 term2)
    -- Step term1 of application until it is in normal form.
    | not (isNormalForm term1) = Application (step term1) term2 
     -- Oh no! term1 is stuck! (If it was a value the previous application rule would apply.) Oh well, let's keep evaluating term2
    | not (isNormalForm term2) = Application term1 (step term2)
     -- We can't step at all. No change.
    | otherwise = t

-- betasub :: parameter -> argument -> term -> output
betasub :: Variable -> Term -> Term -> Term
-- Substitute variables
betasub x arg t@(Var old) | old == x  = arg
                          | otherwise = t
-- Beta substitutions applies to both terms of an application.                         
betasub x arg t@(Application term1 term2) = Application (betasub x arg term1) (betasub x arg term2)
-- Recurse substitution inside the body of an abstraction, with very careful caveats.
betasub x arg t@(Abstraction var body) 
    -- Inner variables shadow outer variables.
    | x == var = t
    -- If substituting would bind a currently free variable, perform alpha re-naming, then substitution.
    | elem var (freeVars arg) = betasub x arg (alphasub (autoRename var) t)
    -- Otherwise, substitution occurs in the body of an inner function.
    | otherwise = Abstraction var (betasub x arg body)

autoRename :: Variable -> Variable
autoRename a = '_':a

--alphasub :: new name -> abstraction -> abstraction
alphasub :: Variable -> Term -> Term
alphasub new (Abstraction old body) = Abstraction new (betasub old (Var new) body)

-------------------------------------------------------------------------
-- E X A M P L E S
-------------------------------------------------------------------------

lid    = Abstraction "x" (Var "x")                   -- λx.x
lTrue  = Abstraction "t" (Abstraction "f" (Var "t")) -- λt.λf.t
lFalse = Abstraction "t" (Abstraction "f" (Var "f")) -- λt.λf.f

double = "/x.(x x)"
trouble = "(" ++ double ++ " " ++ double ++ ")"

-------------------------------------------------------------------------
-- L A Z Y   M A N ' S   U N I T   T E S T
-------------------------------------------------------------------------
-- I got these from https://files.nyu.edu/cb125/public/Lambda/
test :: IO ()
test = do
  test' "(/x.(it x) works)" "(it works)"
  -- Beta-reduction
  test' "(/var.((a var) (b var)) argument)" "((a argument) (b argument))"
  test' "(/x./y.(x y) z)" "/y.(z y)"
  -- Alpha redution
  test' "(/x./y.(x y) y)" "/_y.(y _y)"
  -- Identity
  test' "(/x.x a)" "a"
  -- Double
  test' "(/x.(x x) a)" "(a a)"
  -- Nested substitution
  test' "(/x.((x y) z) z)" "((z y) z)"
  -- Throwing away values
  test' "(/x.(w y) z)" "(w y)"
  -- 
  test' "(/x.(p x) j)" "(p j)"
  test' "(/x.(p y) j)" "(p y)"
  test' "((/x./y.(p y) j) m)" "(p m)" -- Caught an error in isNormalForm! Woot
  test' "((/x./y.(p x) j) m)" "(p j)"
  test' "(/p.(p j) /x.(q x))" "(q j)"
  test' "((/x./y.((k x) y) j) m)" "((k j) m)"
  test' "((/y./x.((k x) y) j) m)" "((k m) j)"
  test' "(p j)" "(p j)"
  test' "(/x.(p x) j)" "(p j)"
  test' "(/q.(q j) p)" "(p j)"
  test' "((/q./x.(q x) p) j)" "(p j)"
  test' "((/x./q.(q x) j) p)" "(p j)"
  test' "((/q./x.(q x) /y.(p y)) j)" "(p j)"
  test' "(((/gq./l./x.((gq l) x) /q./x.(q x)) p) j)" "(p j)"
  test' "(/x.((a x) ((k x) j)) m)" "((a m) ((k m) j))"
  test' "(/x.(/x.((k x) x) j) m)" "((k j) j)"
  -- Whew.

test' :: String -> String -> IO ()
test' input reference = if (reference == (format (reduce (parse input))))
                          then putStrLn "Passed"
                          else putStrLn ("Failed: " ++ input)
