module Lab where

import Data.List (intersect)

import Formula
import Utils

-- data structure used in the SAT solver
data Literal = Pos VarName | Neg VarName deriving (Eq, Show, Ord)

-- compute the opposite literal
opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

-- A clause is a list of literals (representing their conjunction)
type Clause = [Literal]

-- A CNF if a list of clauses (representing their disjunction)
type CNF = [Clause]

-- compute the NNF (negation normal form)
nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Not T) = F
nnf (Not F) = T
nnf (Var p) = Var p
nnf (Not (Var p)) = Not $ Var p
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = nnf (Or (Not phi) psi)
nnf (Iff phi psi) = nnf (And (Implies phi psi) (Implies psi phi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = nnf (Or (Not phi) (Not psi))
nnf (Not (Or phi psi)) = nnf (And (Not phi) (Not psi))
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Not (Iff phi psi)) = nnf (Or (And phi (Not psi)) (And (Not phi) psi))

-- transform a formula to logically equivalent cnf (exponential complexity)
-- (entirely analogous to dnf from Lab01)
cnf :: Formula -> CNF
cnf phi = go $ nnf (deepSimplify phi) where
  go T = []
  go F = [[]]
  go (Var x) = [[Pos x]]
  go (Not (Var x)) = [[Neg x]]
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = distribute (go phi) (go psi)

-- find all positive occurrences of a variable name
positiveLiterals :: Clause -> [VarName]
positiveLiterals ls = rmdups [p | Pos p <- ls]

-- find all negative occurrences of a variable name
negativeLiterals :: Clause -> [VarName]
negativeLiterals ls = rmdups [p | Neg p <- ls]

-- find all occurrences of a variable name
literals :: Clause -> [VarName]
literals ls = rmdups $ positiveLiterals ls ++ negativeLiterals ls

-- formula simplification
simplify :: Formula -> Formula

simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- keep simplifying until no more simplifications are possible
deepSimplify :: Formula -> Formula
deepSimplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deepSimplify psi

ecnf :: Formula -> CNF
ecnf f = let (Var rootName, cnf') = ecnfRecursiveStep (deepSimplify f) []
  in [[Pos rootName]] ++ cnf'

ecnfRecursiveStep :: Formula -> CNF -> (Formula, CNF)
ecnfRecursiveStep var@(Var _) lss = (var, lss)
ecnfRecursiveStep (T) lss =
  let p_var = generatePVar lss
      phi = (cnf (Iff p_var (T)))
      in (p_var, lss ++ phi)
ecnfRecursiveStep (F) lss =
  let p_var = generatePVar lss
      phi = (cnf (Iff p_var (F)))
      in (p_var, lss ++ phi)
ecnfRecursiveStep (Not f) lss = 
  let (newF, lss1) = ecnfRecursiveStep f lss
      p_var = generatePVar lss1
      phi = (cnf (Iff p_var (Not newF)))
      in (p_var, lss1 ++ phi)
ecnfRecursiveStep (And p s) lss =
  let (leftForm, lss1) = ecnfRecursiveStep p lss
      (rightForm, lss2) = ecnfRecursiveStep s lss1
      p_var = generatePVar lss2
      phi = (cnf (Iff p_var (And leftForm rightForm)))
      in (p_var, lss2 ++ phi)
ecnfRecursiveStep (Or p s) lss =
  let (leftForm, lss1) = ecnfRecursiveStep p lss
      (rightForm, lss2) = ecnfRecursiveStep s lss1
      p_var = generatePVar lss2
      phi = (cnf (Iff p_var (Or leftForm rightForm)))
      in (p_var, lss2 ++ phi)
ecnfRecursiveStep (Implies p s) lss =
  let (leftForm, lss1) = ecnfRecursiveStep p lss
      (rightForm, lss2) = ecnfRecursiveStep s lss1
      p_var = generatePVar lss2
      phi = (cnf (Iff p_var (Implies leftForm rightForm)))
      in (p_var, lss2 ++ phi)
ecnfRecursiveStep (Iff p s) lss =
  let (leftForm, lss1) = ecnfRecursiveStep p lss
      (rightForm, lss2) = ecnfRecursiveStep s lss1
      p_var = generatePVar lss2
      phi = (cnf (Iff p_var (Iff leftForm rightForm)))
      in (p_var, lss2 ++ phi)
ecnfRecursiveStep x _ = error $ show x

generatePVar :: CNF -> Formula
generatePVar lss = Var ("p__" ++ (show $ length lss))

-- remove clauses containing a positive and a negative occurrence of the same literal
removeTautologies :: CNF -> CNF
removeTautologies lss = filter (\clause -> length ((positiveLiterals clause) `intersect` (negativeLiterals clause)) == 0) lss