{-# LANGUAGE GeneralizedNewtypeDeriving, NPlusKPatterns #-}
import WHILE hiding (identifiers)

import Control.Applicative
import Control.Monad
import Control.Monad.Random hiding (Random)
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.List

type Seed = StdGen
type Random = RandT Seed (State [String])
newtype Random1 a = Random1 { unRandom :: MaybeT (RandT Seed (State [String])) a } deriving (Applicative, Functor, Monad)
runRandom g f = (fst . (flip runState) [] . (flip runRandT) g . runMaybeT . unRandom) f



--randomTerm :: Seed -> Integer -> (Term, Seed)
randomTerm s d_t d_e = (runState . runRandT (randomTerm' d_t >>= (\t -> return $ (Assignment "a" (Constant 0)) ::: t))) s ["a"] where
    randomTerm' :: Integer -> Random Term
    randomTerm' 0 = randomTerminal_t 0
    randomTerm' (n + 1) = (join . fromList_f) [
        (1, randomTerminal_t n),
        (10000000, (`fmap` randomExpression_a n) . Assignment =<< fresh),
        (1, (`fmap` randomExpression_a n) . Assignment =<< randomVariable),
        (100, (`fmap` randomTerm' n) . (:::) =<< randomTerm' n),
        (1, (do
            c <- randomExpression_b n
            t <- randomTerm' n
            f <- randomTerm' n

            return (Conditional c t f))),
        (1, (`fmap` randomTerm' n) . While =<< randomExpression_b n)]

    randomExpression_a :: Integer -> Random Expression_a
    randomExpression_a n | n <= 0 = randomTerminal_a
    randomExpression_a 0 = randomTerminal_a
    randomExpression_a (n + 1) = (join . fromList_f) [
        (2, randomTerminal_a),
        (1, (`fmap` randomExpression_a n) . (:*) =<< randomExpression_a n),
        (1, (`fmap` randomExpression_a n) . (:/) =<< randomExpression_a n),
        (1, (`fmap` randomExpression_a n) . (:+) =<< randomExpression_a n),
        (1, (`fmap` randomExpression_a n) . (:-) =<< randomExpression_a n),
        (1, (`fmap` randomExpression_a n) . (:%) =<< randomExpression_a n)]

    randomExpression_b :: Integer -> Random Expression_b
    randomExpression_b 0 = randomTerminal_b
    randomExpression_b (n + 1) = (join . fromList_f) [
        (2, randomTerminal_b),
        (1, Not <$> randomExpression_b n),
        (1, (`fmap` randomExpression_b n) . And =<< randomExpression_b n),
        (1, (`fmap` randomExpression_b n) . Or =<< randomExpression_b n),
        (1, (`fmap` randomExpression_a n) . (:=) =<< randomExpression_a n),
        (1, (`fmap` randomExpression_a n) . (:<) =<< randomExpression_a n)]

    randomTerminal_t 0 = return Skip
    randomTerminal_t n = let n' = n - 1 in (join . fromList_f) [
        (1, return Skip),
        (1, Out <$> randomExpression_a n')]
    randomTerminal_a = (join . fromList_f) [
        (1, Constant <$> getRandomR (0, 100)),
        (2, Variable <$> randomVariable)]
    randomTerminal_b = (join . fromList_f) [
        (1, return TT),
        (1, return FF)]

    randomVariable = do
        s <- lift $ get

        fromList (zip s [1..])
    fresh = lift $ do
        s <- get
        let i = (head (identifiers \\ s))

        put (i:s)
        return i

fromList_f :: MonadRandom m => [(Rational, a)] -> m a
fromList_f = fromList . map (\(p, q) -> (q, p))

identifiers = (map return ['a'..'z'] :: [String]) ++ (map (\n -> 'n':(show n)) [1..])