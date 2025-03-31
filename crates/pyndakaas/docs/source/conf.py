# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

import pindakaas
project = 'Pindakaas'
copyright = "2025, Jip J. Dekker (jip@dekker.one), Hendrik 'Henk' Bierlee (hendrik.bierlee@monash.edu)"
author = "Jip J. Dekker (jip@dekker.one), Hendrik 'Henk' Bierlee (hendrik.bierlee@monash.edu)"

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration


extensions = [
    'sphinx.ext.autodoc',
    # 'sphinx.ext.autosummary',
    # 'sphinx.ext.intersphinx',
    # 'sphinx.ext.todo',
    # 'sphinx.ext.inheritance_diagram',
    # 'sphinx.ext.autosectionlabel',
    # 'sphinx.ext.napoleon',
    # 'sphinx_rtd_theme',
]

templates_path = ['_templates']
exclude_patterns = []



# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'alabaster'
html_static_path = ['_static']
