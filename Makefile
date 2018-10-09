all :
	stack exec -- liquid src/RG.hs src/CASList.hs src/RefinedADTs.hs src/MinCrash.hs src/BadMeasureParse.hs src/Ackermann.hs
run :
	stack exec -- liquid src/CASList.hs src/RG.hs
