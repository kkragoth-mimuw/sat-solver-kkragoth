
.PHONY: all

all: sat-solver tester

# even non-Haskell solutions will need to compile the tester to run the tests
tester: Tester.hs
	ghc -o tester Tester.hs

# can comment this if your solution is not in Haskell
sat-solver: sat-solver.hs Parser.hs Utils.hs Lab.hs
	ghc -O2 -o sat-solver sat-solver.hs

clean:
	rm sat-solver tester *.hi *.o
