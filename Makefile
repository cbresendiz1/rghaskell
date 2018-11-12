.PHONY : default build verify-rgref verify-cas verify-rgtest test
default:
	@echo "Please read the README and Makefile"
	@echo "+ List of (make) commands :"
	@echo "  [ build verify-rgref verify-cas verify-rgtest test ]"
build:
	stack build
test:
	stack test rghaskell:lh-test
verify-rgref:
	stack exec -- liquid src/RGRef/RG.hs
verify-cas:
	stack exec -- liquid src/RGRef/CASList.hs src/RGRef/RG.hs
verify-rgtest:
	stack exec -- liquid src/RGRef/RG.hs src/RGRef/RGTests.hs
