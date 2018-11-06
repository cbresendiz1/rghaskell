.PHONY : default build verify-rgref verify-cas
default :
	@echo "Please read the README and Makefile"
	@echo "+ List of (make) commands :"
	@echo "  [ build verify-rgref verify-cas]"
build :
	stack build
verify-rgref :
	stack exec -- liquid src/RGRef/RG.hs
verify-cas :
	stack exec -- liquid src/RGRef/CASList.hs src/RGRef/RG.hs
