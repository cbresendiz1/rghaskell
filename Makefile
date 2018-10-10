default :
	@echo "Please read the README and Makefile"

build :
	stack build

verify_all :
	stack exec -- liquid src/RG.hs src/CASList.hs src/RefinedADTs.hs src/MinCrash.hs src/BadMeasureParse.hs src/Ackermann.hs
verify_CAS :
	stack exec -- liquid src/CASList.hs src/RG.hs
