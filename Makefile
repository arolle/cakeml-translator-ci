.PHONY: default
default: test

revProg.sexp: listrevProgScript.sml
	Holmake

revProg: revProg.sexp
	@echo "compile"
	$(MAKE) --makefile=Makefile.cake $@

.PHONY: test
test: revProg
	@echo "tests"
	diff <(echo -n "tset" ) <(echo -n "test" | ./revProg)
	diff <(printf "tset\n321") <(printf "test\n123" | ./revProg)
	diff <(printf "tset\x00321") <(printf "test\x00123" | ./revProg -0 )

