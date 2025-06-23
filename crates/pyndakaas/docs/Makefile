# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line, and also
# from the environment for the first two.
# TODO Added -E -a to force reload for autodoc, otherwise the re-generation of the build is very inconsistent!
SPHINXOPTS    ?= -E -a
SPHINXBUILD   ?= sphinx-build
SOURCEDIR     = source
BUILDDIR      = build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	pip install --group ../pyproject.toml:docs
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) -E -a $(O)

# Live HTML view of the documentation for development (requires `sphinx-autobuild` to be installed). Recompiles the crate on every change.
livehtml:
	sphinx-autobuild "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) --pre-build "pip install -e ..[docs]" --watch ../src --watch ../python/pindakaas/solver.py --watch ../python/pindakaas/encoding.py $(O)
	# TODO does not quite work
	# sphinx-autobuild "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) --pre-build "pip install -e ..[docs]" --open-browser --watch ../src --watch ../python/pindakaas/*.py $(O)
