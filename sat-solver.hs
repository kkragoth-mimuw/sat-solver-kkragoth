module Main where

import Data.List
import System.IO
import System.Random
import Test.QuickCheck
import Formula
import Parser hiding (check)
import Utils
import Lab
import Debug.Trace


swoop :: CNF -> ([VarName], [VarName], [VarName])
swoop lss = (allValues, positives, negatives)
    where
        (allPositives, allNegatives) = foldr (\e (p, n) -> case e of
                                                        Pos varName -> (varName:p, n)
                                                        Neg varName -> (p, varName:n) 
                                                ) ([], []) (concat lss)
        positives = rmdups allPositives
        negatives = rmdups allNegatives
        allValues = rmdups (allPositives ++ allNegatives)

extractPureLiterals :: CNF -> [VarName]
extractPureLiterals lss = purePositiveLiterals ++ pureNegativeLiterals where
    (_, purePositiveLiterals, pureNegativeLiterals) = extractPureLiteralsAndCheckConsistency lss

extractPureLiteralsAndCheckConsistency :: CNF -> (Bool, [VarName], [VarName])
extractPureLiteralsAndCheckConsistency lss = (isConsistent, purePositiveLiterals, pureNegativeLiterals)
    where
        (allValues, positives, negatives) = swoop lss
        
        purePositiveLiterals = positives \\ negatives
        pureNegativeLiterals = negatives \\ positives

        isConsistent = length (allValues) == length (purePositiveLiterals ++ pureNegativeLiterals)

isPhiConsistent :: CNF -> Bool
isPhiConsistent lss = isConsistent
    where (isConsistent, _, _) = extractPureLiteralsAndCheckConsistency lss

dpll :: CNF -> Bool
dpll [] = True
dpll lss | [] `elem` lss = False -- traceShow ("[] elem of phi") False
dpll lss | isPhiConsistent lss = True -- traceShow ("isConsistent") True
dpll lss =
    let phi = oneLiteral lss
        phi' = pureLiteralAssigns phi
        -- traceShow lss
        -- l = chooseFirstLiteral phi'
    in
        -- case traceShow lss (chooseFirstLiteral phi') of
        case (chooseLiteral phi') of
            Nothing -> dpll phi'
            Just l -> (dpll (([Pos l]):phi')) || (dpll (([Neg l]):phi'))

oneLiteral :: CNF -> CNF
oneLiteral lss = case find (\l -> length l == 1) lss of
    Just [l] -> oneLiteral $ unitPropagation l lss
    Nothing -> lss

unitPropagation :: Literal -> CNF -> CNF
unitPropagation l lss = map removeOppositeLFromClause $ removeClauesWithL lss where
    removeClauesWithL = filter (notElem l)
    removeOppositeLFromClause = filter ((/=) (opposite l))

pureLiteralAssigns :: CNF -> CNF
pureLiteralAssigns lss = filter (\clause -> length (intersect (literals clause) pureLiterals) == 0) lss where 
    pureLiterals = extractPureLiterals lss


chooseLiteral :: CNF -> Maybe VarName
chooseLiteral lss = let
        allLiterals = concat $ map literals lss
        frequencies = frequencyList $ allLiterals 
        sortedFreq = sortBy sortGT frequencies
    in
        case sortedFreq of
            [] -> Nothing
            (_, l):_ -> Just l
    -- sortBy sortGT $ frequency $ concat $ map literals lss

frequencyList :: Ord a => [a] -> [(Int,a)] 
frequencyList list = map (\l -> (length l, head l)) (group (sort list))

sortGT (a1, b1) (a2, b2)
  | a1 < a2 = GT
  | a1 > a2 = LT
  | a1 == a2 = compare b1 b2

chooseFirstLiteral :: CNF -> Maybe VarName
chooseFirstLiteral lss = case concat $ map literals lss of
    [] -> Nothing
    x:_ -> Just x

sat_solver :: Formula -> Bool
sat_solver phi = dpll $ removeTautologies $ ecnf phi

main :: IO Int
main = do
    eof <- hIsEOF stdin
    if eof
        then return 0
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let sat = sat_solver phi -- call the sat solver
                if sat
                    then putStrLn "1" -- write 1 if the formula is satisfiable
                    else putStrLn "0" -- write 0 if the formula is not satisfiable
                return 0