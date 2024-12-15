##
##  Template makefile for Standard, Profile, Debug, Release, and Release-static versions
##
##    eg: "make rs" for a statically linked release version.
##        "make d"  for a debug version (no optimizations).
##        "make"    for the standard version (optimized, but with debug information and assertions active)

PWD        = $(shell pwd)
EXEC      ?= $(notdir $(PWD))

CSRCS      = $(wildcard $(PWD)/*.cc) 
DSRCS      = $(foreach dir, $(DEPDIR), $(filter-out $(MROOT)/$(dir)/Main.cc, $(wildcard $(MROOT)/$(dir)/*.cc)))
CHDRS      = $(wildcard $(PWD)/*.h)
COBJS      = $(CSRCS:.cc=.o) $(DSRCS:.cc=.o)

PCOBJS     = $(addsuffix p,  $(COBJS))
DCOBJS     = $(addsuffix d,  $(COBJS))
RCOBJS     = $(addsuffix r,  $(COBJS))
R64COBJS   = $(addsuffix x,  $(COBJS))

CXX       ?= g++
CFLAGS    ?= -Wall -Wno-parentheses
LFLAGS    ?= -Wall

COPTIMIZE ?= -O3

CFLAGS    += -I$(MROOT) -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
CFLAGS    += -D GMVER=\"$(VERSION)\"
LFLAGS    += -lz

.PHONY : s p d r rs rx clean 

s:	$(EXEC)
p:	$(EXEC)-profile
d:	$(EXEC)-debug
r:	$(EXEC)-release
rs:	$(EXEC)-static
rx:	$(EXEC)-static-64bitnum

libs:	lib$(LIB)-standard.a
libp:	lib$(LIB)-profile.a
libd:	lib$(LIB)-debug.a
libr:	lib$(LIB)-release.a

## Compile options
%.o:			CFLAGS +=$(COPTIMIZE) -g -D DEBUG
%.op:			CFLAGS +=$(COPTIMIZE) -pg -g -D NDEBUG
%.od:			CFLAGS +=-O0 -g -D DEBUG
%.or:			CFLAGS +=$(COPTIMIZE) -g -D NDEBUG
%.ox:			CFLAGS +=$(COPTIMIZE) -g -D NDEBUG

## Link options
$(EXEC):		LFLAGS += -g
$(EXEC)-profile:	LFLAGS += -g -pg
$(EXEC)-debug:		LFLAGS += -g
#$(EXEC)-release:	LFLAGS += ...
$(EXEC)-static:		LFLAGS += --static
$(EXEC)-static-64bitnum:LFLAGS += --static

## Dependencies
$(EXEC):		$(COBJS)
$(EXEC)-profile:	$(PCOBJS)
$(EXEC)-debug:		$(DCOBJS)
$(EXEC)-release:	$(RCOBJS)
$(EXEC)-static:		$(RCOBJS)
$(EXEC)-static-64bitnum:$(R64COBJS)

lib$(LIB)-standard.a:	$(filter-out */Main.o,  $(COBJS))
lib$(LIB)-profile.a:	$(filter-out */Main.op, $(PCOBJS))
lib$(LIB)-debug.a:	$(filter-out */Main.od, $(DCOBJS))
lib$(LIB)-release.a:	$(filter-out */Main.or, $(RCOBJS))


## Build rule
%.o %.op %.od %.or %.ox:	%.cc
	@echo Compiling: $(subst $(MROOT)/,,$@)
	@$(CXX) $(CFLAGS) -c -o $@ $<

## Linking rules (standard/profile/debug/release)
$(EXEC) $(EXEC)-profile $(EXEC)-debug $(EXEC)-release $(EXEC)-static $(EXEC)-static-64bitnum:
	@echo Linking: "$@ ( $(foreach f,$^,$(subst $(MROOT)/,,$f)) )"
	@$(CXX) $^ $(LFLAGS) -o $@

## Library rules (standard/profile/debug/release)
lib$(LIB)-standard.a lib$(LIB)-profile.a lib$(LIB)-release.a lib$(LIB)-debug.a:
	@echo Making library: "$@ ( $(foreach f,$^,$(subst $(MROOT)/,,$f)) )"
	@$(AR) -rcsv $@ $^

## Library Soft Link rule:
libs libp libd libr:
	@echo "Making Soft Link: $^ -> lib$(LIB).a"
	@ln -sf $^ lib$(LIB).a

## Clean rule
clean:
	@rm -f $(EXEC) $(EXEC)-profile $(EXEC)-debug $(EXEC)-release $(EXEC)-static \
	  $(COBJS) $(PCOBJS) $(DCOBJS) $(RCOBJS) $(R64COBJS) *.core depend.mk 

## Make dependencies
depend.mk: $(CSRCS) $(CHDRS)
	@echo Making dependencies
	@$(CXX) $(CFLAGS) -I$(MROOT) \
	   $(CSRCS) -MM | sed 's|\(.*\):|$(PWD)/\1 $(PWD)/\1r $(PWD)/\1d $(PWD)/\1p:|' > depend.mk
	@for dir in $(DEPDIR); do \
	      if [ -r $(MROOT)/$${dir}/depend.mk ]; then \
		  echo Depends on: $${dir}; \
		  cat $(MROOT)/$${dir}/depend.mk >> depend.mk; \
	      fi; \
	  done

-include $(MROOT)/mtl/config.mk
-include depend.mk
