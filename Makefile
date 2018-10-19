.PHONY : default build verify-rgref verify-cas
default :
	@echo "Please read the README and Makefile"
	@echo "+ List of (make) commands :"
	@echo "  [ build verify-rgref verify-cas]"
build :
	stack build
verify-rgref :
	stack exec -- liquid src/rgref/pos/*.hs
verify-cas :
	stack exec -- liquid src/rgref/pos/CASList.hs src/rgref/pos/RG.hs
verify-problem : # should fail
	stack exec -- liquid src/rgref/*.hs
