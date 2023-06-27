
ifndef $(CAKE)
		CAKE=$(CAKEDIR)/cake
endif
ifndef $(BASIS)
    BASIS=$(CAKEDIR)/basis_ffi.c
endif

%.S : %.cml
	$(CAKE) $(CAKEFLAGS) <$< >$@

%.S : %.sexp
	$(CAKE) --exclude_prelude=true --sexp=true $(CAKEFLAGS) <$< >$@

% : %.S
	$(CC) $(LDFLAGS) $^ $(BASIS) $(LOADLIBES) $(LDLIBS) -o $@

