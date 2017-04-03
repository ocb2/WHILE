{-# LANGUAGE GADTs, NoMonomorphismRestriction #-}

module WHILE where

import Control.Applicative
import Control.Monad.State hiding (fix)
import Data.Int (Int64(..))
import Data.Function (on)
import Data.Graph.Inductive hiding (Context, Graph)
import Data.Graph.Inductive.PatriciaTree hiding (Graph)
import Data.List
import Data.Maybe (catMaybes, fromJust)
import Text.ParserCombinators.ReadP hiding (get)

-- syntax tree

data Term = Assignment Identifier Expression_a
          | Skip
          | Term ::: Term
          | Conditional Expression_b Term Term
          | While Expression_b Term
          | Out Expression_a
          deriving (Eq, Show)

data Expression_a = Constant Integer
                  | Variable Identifier
                  | Expression_a :* Expression_a
                  | Expression_a :/ Expression_a
                  | Expression_a :+ Expression_a
                  | Expression_a :- Expression_a
                  | Expression_a :% Expression_a
                  deriving (Eq, Show)

data Expression_b = TT
                  | FF
                  | Not Expression_b
                  | And Expression_b Expression_b
                  | Or Expression_b Expression_b
                  | Expression_a := Expression_a
                  | Expression_a :< Expression_a
                  deriving (Eq, Show)

type Identifier = String

-- parser

runParseTerms s = case readP_to_S (do r <- pTerms ; eof ; return r) s of
 [(r,"")] -> Just r
 _ -> Nothing

pTerms = do p <- pTerm ; s ; eof
            return p

pTerm =
 chainr1 pTerm'
 (do s ; string ";"
     return (:::))

pTerm' =
 pAssignment    +++
 pSkip          +++
 pConditional   +++
 pWhile         +++
 pOut

pAssignment = do
 v <- pIdentifier
 s ; string ":="
 e <- pExpressionA
 return (Assignment v e)

pSkip = do s ; string "skip" ; return Skip

pConditional = do
 s ; string "if ("
 c <- pExpressionB
 s ; string ")"
 s ; string "{"
 t <- pTerm
 s ; string "}"
 s ; string "else"
 s ; string "{"
 e <- pTerm
 s ; string "}"
 return (Conditional c t e)

pWhile = do
 s ; string "while ("
 b <- pExpressionB
 s ; string ")"
 s ; string "{"
 e <- pTerm
 s ; string "}"
 return (While b e)

pOut = do
 s ; string "out "
 e <- pExpressionA
 return (Out e)

constructParser t (o:[]) = chainr1 t o
constructParser t (o:os) = chainr1 (constructParser t os) o

binary c o = do
    s
    string o
    return c

pExpressionB =
 chainr1 pExpressionB'
 (do s ; string "|"
     return Or)

pExpressionB' =
 chainr1 pExpressionB''
 (do s ; string "&"
     return And)

pExpressionB'' =
 (do s ; string "tt"
     return TT) +++
 (do s ; string "ff"
     return FF) +++
 (do s ; string "~"
     b <- pExpressionB
     return (Not b)) +++
 (do l <- pExpressionA
     o <- (do s ; string "=" ; return (:=))         +++
          (do s ; string "<" ; return (:<))         +++
          (do s ; string ">" ; return (flip (:<)))  +++
          (do s ; string "<=" ; return (\p q -> (Or (p :< q) (p := q)))) +++
          (do s ; string ">=" ; return (\p q -> (Or (q :< p) (p := q))))
     r <- pExpressionA
     return (o l r))

pExpressionA = constructParser terminal [binary (:%) "%",
                                         binary (:-) "-",
                                         binary (:+) "+",
                                         binary (:/) "/",
                                         binary (:*) "*"] where
    terminal = (Constant <$> pInteger) +++ (Variable <$> pIdentifier)

pInteger = do s ; is <- munch1 (`elem` ['0'..'9'])
              return (read is :: Integer)

pIdentifier = do s ; munch1 (`elem` ['a'..'z'])

s = skipSpaces

-- interpreter

type Context = ([(String, Integer)], [Integer])

interpret :: Term -> Context
interpret t = interpret' t ([], []) where
    interpret' (Assignment i e) c@(g, o) = ((i, evaluate_a e c):g, o)
    interpret' (Out e) c@(g, o) = (g, o ++ [(evaluate_a e c)])
    interpret' Skip c = c
    interpret' (p ::: q) c = interpret' q (interpret' p c)
    interpret' (Conditional e t f) c = if evaluate_b e c
        then interpret' t c
        else interpret' f c
    interpret' t@(While e b) c = if evaluate_b e c
        then interpret' t (interpret' b c)
        else c

evaluate_a :: Expression_a -> Context -> Integer
evaluate_a (Constant n) _ = n
evaluate_a (Variable i) (g, _) = case lookup i g of
    Nothing -> error ("Undefined variable " ++ i)
    Just v -> v
evaluate_a (p :* q) c = p' * q' where
    p' = evaluate_a p c
    q' = evaluate_a q c
evaluate_a (p :/ q) c = p' `div` q' where
    p' = evaluate_a p c
    q' = evaluate_a q c
evaluate_a (p :+ q) c = p' + q' where
    p' = evaluate_a p c
    q' = evaluate_a q c
evaluate_a (p :- q) c = p' - q' where
    p' = evaluate_a p c
    q' = evaluate_a q c
evaluate_a (p :% q) c = p' `mod` q' where
    p' = evaluate_a p c
    q' = evaluate_a q c

evaluate_b :: Expression_b -> Context -> Bool
evaluate_b TT _ = True
evaluate_b FF _ = False
evaluate_b (Not e) c = not (evaluate_b e c)
evaluate_b (And p q) c = evaluate_b p c && evaluate_b q c
evaluate_b (Or p q) c = evaluate_b p c || evaluate_b q c
evaluate_b (p := q) c = evaluate_a p c == evaluate_a q c
evaluate_b (p :< q) c = evaluate_a p c < evaluate_a q c

-- compiler

compile :: Term -> Assembly_x86
compile = peephole . compile_x86 . allocate . compile_i

-- intermediate assembly code generation

type Assembly_i = [Instruction_i]

data Instruction_i = Label_i Destination
                   | ADD_i   Destination Source Source
                   | AND_i   Destination Source Source
                   | CALL_i  Destination
                   | CMP_i   Source      Source
                   | DIV_i   Destination Source Source
                   | EXIT_i
                   | JE_i    Destination
                   | JL_i    Destination
                   | JMP_i   Destination
                   | MOD_i   Destination Source Source
                   | MOV_i   Destination Source
                   | MUL_i   Destination Source Source
                   | NOT_i   Destination Source
                   | OR_i    Destination Source Source
                   | OUT_i   Source
                   | RET_i
                   | SUB_i   Destination Source Source
                   deriving (Eq, Show)

data Source = Cell Cell | Immediate_i Integer deriving (Eq, Show)
type Destination = Cell

type Cell = String

compile_i :: Term -> Assembly_i
compile_i t = (evalState (compile_t t) []) ++ [EXIT_i]

compile_t :: Term -> State [String] [Instruction_i]
compile_t (Assignment i e) = do
    c <- get
    put (i:c)

    (e_o, e') <- compile_a e

    return (e' ++ [MOV_i i e_o])
compile_t Skip = return []
compile_t (p ::: q) = do
    p' <- compile_t p
    q' <- compile_t q

    return (p' ++ q')
compile_t (Conditional c t f) = do
    (c_o, c') <- compile_b c
    t' <- compile_t t
    f' <- compile_t f

    t_l <- fresh
    f_l <- fresh

    return (c'           ++
           [CMP_i c_o (Immediate_i 0),
            JE_i  f_l]   ++
            t'           ++
           [JMP_i t_l,
            Label_i f_l] ++
            f'           ++
           [Label_i t_l])
compile_t (While c b) = do
    (c_o, c') <- compile_b c
    b' <- compile_t b

    t_l <- fresh
    f_l <- fresh

    return ([Label_i t_l] ++
             c' ++
            [CMP_i c_o (Immediate_i 0),
             JE_i f_l] ++
             b' ++
            [JMP_i t_l,
             Label_i f_l])
compile_t (Out e) = do
    (e_o, e') <- compile_a e

    return (e' ++ [OUT_i e_o])

compile_a :: Expression_a -> State [String] (Source, [Instruction_i])
compile_a e = case e of
    (Constant n) -> return (Immediate_i n, [])
    (Variable i) -> return (Cell i, [])
    (p :* q)     -> binary MUL_i p q
    (p :/ q)     -> binary DIV_i p q
    (p :+ q)     -> binary ADD_i p q
    (p :- q)     -> binary SUB_i p q
    (p :% q)     -> binary MOD_i p q
    where
        binary i p q = do
            (p_o, p') <- compile_a p
            (q_o, q') <- compile_a q

            r <- fresh

            return (Cell r, p' ++ q' ++ [i r p_o q_o])

compile_b :: Expression_b -> State [String] (Source, [Instruction_i])
compile_b e = case e of
    TT -> return (true, [])
    FF -> return (false, [])
    (Not p) -> unary NOT_i p
    (And p q) -> binary AND_i p q
    (Or p q) -> binary OR_i p q
    (p := q) -> equality JE_i p q
    (p :< q) -> equality JL_i p q
    where
        true = Immediate_i ((2^64) - 1)
        false = Immediate_i 0

        unary o p = do
            (p_o, p') <- compile_b p

            r <- fresh

            return (Cell r, p' ++ [o r p_o])
        binary o p q = do
            (p_o, p') <- compile_b p
            (q_o, q') <- compile_b q

            r <- fresh

            return (Cell r, p' ++ q' ++ [o r p_o q_o])
        equality o p q = do
            (p_o, p') <- compile_a p
            (q_o, q') <- compile_a q

            t <- fresh
            f <- fresh
            r <- fresh

            return (Cell r, p' ++ q' ++ [CMP_i p_o q_o,
                                         o t,
                                         MOV_i r false,
                                         JMP_i f,
                                         Label_i t,
                                         MOV_i r true,
                                         Label_i f])

fresh :: State [String] String
fresh = do
    c <- get

    let i = (head (identifiers \\ c))

    put (i:c)
    return i

identifiers = (map return ['a'..'z'] :: [String]) ++ (map (\n -> 'n':(show n)) [1..])

-- register allocation

type Graph = Gr

allocate :: Assembly_i -> (Assembly_i, [(String, Register)])
allocate is = undefined where
    g = (color registers . precolor registers . interference . lifetime) is
    registers = [RAX, RBX, RCX, RDX, RSI, RDI, RSP, RBP, R8, R9, R10, R11, R12, R13, R14, R15]
    
(<<) = flip (>>)

lifetime :: [Instruction_i] -> [(String, (Integer, Integer))]
lifetime is = (fst . (flip execState) ([], 0) . (flip mapM) is) $ \i -> increment << case i of
    (Label_i _)     -> pass
    (ADD_i   d p q) -> pushd d >> pushs p >> pushs q
    (AND_i   d p q) -> pushd d >> pushs p >> pushs q
    (CALL_i  _)     -> pass
    (CMP_i     p q) ->            pushs p >> pushs q
    (DIV_i   d p q) -> pushd d >> pushs p >> pushs q
    (EXIT_i)        -> pass
    (JE_i    _)     -> pass
    (JL_i    _)     -> pass
    (JMP_i   _)     -> pass
    (MOD_i   d p q) -> pushd d >> pushs p >> pushs q
    (MOV_i   d p)   -> pushd d >> pushs p
    (MUL_i   d p q) -> pushd d >> pushs p >> pushs q
    (NOT_i   d p)   -> pushd d >> pushs p
    (OR_i    d p q) -> pushd d >> pushs p >> pushs q
    (OUT_i     p)   ->            pushs p
    (RET_i)         -> pass
    (SUB_i   d p q) -> pushd d >> pushs p >> pushs q
    where
        pass = return ()
        push i = do
            (l, x) <- get
            put (push' x l, x) where
                push' x [] = [(i, (x, x))]
                push' x ((i', (l, _)):ls) | i == i' = (i, (l, x)):ls
                push' x (l:ls) = l:(push' x ls)

        pushd = push
        pushs (Cell i) = push i
        pushs _ = pass

        increment = do
            (l, x) <- get
            put (l, x + 1)

interference :: [(String, (Integer, Integer))] -> Graph String (String, String)
interference ls = mkGraph vertices edges where
    vertices = map (\(i, (i', _)) -> (i, i')) ls'
    edges = concatMap (incident ls') ls'

    incident [] _ = []
    incident   ((i,  (d,  l)):vs)
             v'@(i', (d', l')) | l `intersects` l' &&
                                 i /= i' = (i, i', (d, d')):(incident vs v')
    incident (_:vs) v' = incident vs v'

    intersects (a, b) (c, d) = c `between` (a, b) ||
                               d `between` (a, b)
    between a (b, c) = a >= b && a <= c

    ls' = zip [0..] ls

--precolor :: (DynGraph g, Eq k) => g v e -> g (v, [k]) e
precolor r g = g

-- simple greedy algorithm
color :: Eq k => [k] -> Graph v e -> Graph (v, k) e
color ks g = nmap (\(l, c) -> (l, fromJust c)) ((snd . runState ((color' . sortBy (compare `on` (length . neighbors g)) . nodes) g)) (gmap (\(p, v, l, s) -> (p, v, (l, Nothing), s)) g))
    where
        color' [] = return True
        color' (v:vs) = do
            cs <- colors v

            if null cs
                then return False
                else try (v, vs) cs

        try _ [] = return False
        try (v, vs) (c:cs) = do
            g' <- get
            put (label v c g')

            b <- color' vs

            if b then return True else put g' >> try (v, vs) cs

        colors v = do
            g' <- get

            return (ks \\ (catMaybes . map snd . catMaybes $ (map (lab g') (neighbors g' v))))

        label v c g = case match v g of
            (Just (p, v, (l, _), s), g') -> (p, v, (l, Just c), s) & g'
            (Nothing, _) -> error "Unmatched node in graph"

-- x86 code generation

data Assembly_x86 = Assembly_x86 [String] [Instruction_x86]

instance (Show Assembly_x86) where
    show (Assembly_x86 ds is) = concatMap (\l -> "extern " ++ l ++ "\n") builtins ++
                                "\n" ++
                                "section .data\n" ++
                                concatMap (\d -> d ++ ": dq 0\n") ds ++ "\n" ++
                                "section .text\nglobal _start\n\n_start:" ++
                                concatMap (\i -> "\n    " ++ show i) is

data Instruction_x86 = Label String
                 | ADD  Operand Operand
                 | AND  Operand Operand
                 | CALL Operand
                 | CMP  Operand Operand
                 | DEC  Operand
                 | DIV  Operand
                 | INC  Operand
                 | JE   Operand
                 | JL   Operand
                 | JMP  Operand
                 | JNE  Operand
                 | MOV  Operand Operand
                 | MUL  Operand Operand
                 | NEG  Operand
                 | NOP
                 | NOT  Operand
                 | OR   Operand Operand
                 | PUSH Operand
                 | POP  Operand
                 | RET
                 | SYSCALL
                 | SUB  Operand Operand
                 deriving (Eq)

instance (Show Instruction_x86) where
    show i = case i of
        (Label s) -> s ++ ":"
        (ADD p q) -> binary  "qword" "add"  p q
        (AND p q) -> binary  "qword" "and"  p q
        (CALL p)  -> unary   "qword" "call" p
        (CMP p q) -> binary  "qword" "cmp"  p q
        (DEC p)   -> unary   "qword" "dec"  p
        (DIV p)   -> unary   "qword" "div"  p
        (INC p)   -> unary   "qword" "inc"  p
        (JE p)    -> unary   ""      "je"   p
        (JL p)    -> unary   ""      "jl"   p
        (JMP p)   -> unary   "qword" "jmp"  p
        (JNE p)   -> unary   "qword" "jne"  p
        (MOV p q) -> binary  "qword" "mov"  p q
        (MUL p q) -> binary  "qword" "imul" p q
        (NEG p)   -> unary   "qword" "neg"  p
        (NOP)     -> nullary         "nop"
        (NOT p)   -> unary   "qword" "not"  p
        (OR p q)  -> binary  "qword" "or"   p q
        (PUSH p)  -> unary   "qword" "push" p
        (POP p)   -> unary   "qword" "pop"  p
        (RET)     -> nullary         "ret"
        (SYSCALL) -> nullary         "syscall"
        (SUB p q) -> binary  "qword" "sub"  p q
        where
            nullary o = o
            unary "" o p = nullary o ++ " " ++ show p
            unary s o p = nullary o ++ " " ++ s ++ " " ++ show p
            binary s o p q = unary s o p ++ ", " ++ show q

data Operand = Immediate (I Integer)
             | Register  (I Register)
             | Label_o   (I String)
             deriving (Eq)

instance (Show Operand) where
    show (Immediate n) = show n
    show (Register r) = show r
    show (Label_o (Concrete i)) = i
    show (Label_o (Pointer i)) = "[" ++ i ++ "]"

data Register = RAX | RBX | RCX | RDX
              | RSI | RDI | RSP | RBP
              | R8  | R9  | R10 | R11
              | R12 | R13 | R14 | R15
              deriving (Eq, Show)

data I a = Concrete a | Pointer a deriving (Eq)

instance Show a => Show (I a) where
    show (Concrete a) = show a
    show (Pointer a) = "[" ++ show a ++ "]"

compile_x86 :: (Assembly_i, [(String, Register)]) -> Assembly_x86
compile_x86 (is, _) = uncurry (flip Assembly_x86) (runState (liftM concat $ mapM translate is) [])

translate :: Instruction_i -> State [String] [Instruction_x86]
translate i = case i of
    (Label_i i) -> return [Label i]
    (AND_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return [MOV rax p',
                AND rax q',
                MOV (label d) rax]
    (ADD_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return $ case (p, q) of
            (Cell i, Immediate_i 1) | d == i -> [INC p']
            (Immediate_i 1, Cell o) | d == o -> [INC p']
            (Cell i, _)             | d == i -> [ADD p' q']
            (_, Cell o)             | d == o -> [ADD q' p']
            _                                -> [MOV rax p',
                                                 ADD rax q',
                                                 MOV (pointer d) rax]
    (CALL_i i) -> return [CALL (label i)]
    (CMP_i p q) -> do
        p' <- operand p
        q' <- operand q

        return $ case (p, q) of
            (Immediate_i _,
             Immediate_i _) -> [MOV rax p',
                                CMP rax q']
            (Cell _,
             Cell _)        -> [MOV rax p',
                                CMP rax q']
            _               -> [CMP p' q']
    (DIV_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return [MOV rax p',
                MOV rcx q',
                MOV rdx (Immediate (Concrete 0)),
                DIV rcx,
                MOV (pointer d) rax]
    (EXIT_i) -> return [MOV rax (concrete 0x3C),
                        MOV rdi (concrete 0x00),
                        SYSCALL]
    (JE_i i) -> return [JE (label i)]
    (JL_i i) -> return [JL (label i)]
    (JMP_i i) -> return [JMP (label i)]
    (MOD_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return [MOV rax p',
                MOV rcx q',
                MOV rdx (Immediate (Concrete 0)),
                DIV rcx,
                MOV (pointer d) rdx]
    (MOV_i p q) -> do
        q' <- operand q

        push p

        return $ case q of
            (Cell _) -> [MOV rax q',
                         MOV (pointer p) rax]
            _        -> [MOV (pointer p) q']
    (MUL_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return $ case (p, q) of
            _                    -> [MOV rax p',
                                     MUL rax q',
                                     MOV (pointer d) rax]
    (NOT_i d p) -> do
        p' <- operand p

        push d

        return $ case p of
            (Cell _) -> [MOV rax p',
                         NOT rax,
                         MOV (pointer d) rax]
            _        -> [MOV (pointer d) p',
                         NOT (pointer d)]
    (OR_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return [MOV rax p',
                AND rax q',
                MOV (label d) rax]
    (OUT_i p) -> do
        p' <- operand p

        return [MOV rax p',
                CALL (label "print_decimal"),
                CALL (label "newline")]
    (RET_i) -> return [RET]
    (SUB_i d p q) -> do
        p' <- operand p
        q' <- operand q

        push d

        return $ case (p, q) of
            (Immediate_i _, Immediate_i _) -> [MOV (pointer d) p',
                                        SUB (pointer d) q']
            _                       -> [MOV rax p',
                                        SUB rax q',
                                        MOV (pointer d) rax]
    where
        concrete = Immediate . Concrete
        label = Label_o . Concrete
        pointer = Label_o . Pointer

        rax = Register (Concrete RAX)
        rcx = Register (Concrete RCX)
        rdx = Register (Concrete RDX)
        rdi = Register (Concrete RDI)

        operand (Cell i) = do
            push i
            return (Label_o (Pointer i))
        operand (Immediate_i n) = return (concrete n)

        push i = do
            c <- get
            put (c + i)
            where
                [] + i = [i]
                (c:cs) + i | c == i = (c:cs)
                (c:cs) + i = c:(cs + i)

builtins = ["print_decimal",
            "newline"]

-- peephole optimizer

fix f x | f x == x = x
fix f x = fix f (f x)

-- this is basically a term rewrite system so care must be taken to not either
-- reach a fixed point prematurely by taking a branch that returns its match
-- (which will prevent further optimizations), or to loop forever, by returning
-- a term which can be matched again on and is different from its match
peephole :: Assembly_x86 -> Assembly_x86
peephole (Assembly_x86 ns is) = Assembly_x86 ns (fix peephole' is) where
    peephole' ((MOV a b):
               (MOV c d):
               is) | and [a == d,
                          b == c] = (MOV a b):is
    peephole' ((MOV a b):
               (INC o):
               (MOV c d):
               is) | and [a == d,
                          b == c,
                          o == a] = (MOV d b):
                                    (INC d):is
    peephole' ((MOV a b):
               (DEC o):
               (MOV c d):
               is) | and [a == d,
                          b == c,
                          o == a] = (MOV d b):
                                    (DEC b):is
    peephole' ((MOV a b):
            (i@(MOV c (Immediate _))):
               is) | a == c = i:is
    peephole' ((ADD a (Immediate (Concrete 1))):
               is) = (INC a):is
    peephole' ((SUB a (Immediate (Concrete 1))):
               is) = (DEC a):is
    peephole' ((SUB (Immediate (Concrete 0)) a):
               is) = (NEG a):is
    peephole' (i:is) = i:(peephole' is)
    peephole' [] = []