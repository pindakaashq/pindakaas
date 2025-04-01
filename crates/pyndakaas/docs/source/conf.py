# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

import tomllib
with open("../../../../Cargo.toml", "rb") as f:
    cargo = tomllib.load(f)
    package = cargo["workspace"]["package"]
    author = ", ".join(author.replace("<","(").replace(">",")")  for author in package["authors"])
    release = package["version"]

with open("../../../pindakaas/Cargo.toml", "rb") as f:
    cargo = tomllib.load(f)
    package = cargo["package"]
    description = package["description"]
    project = package["name"]
    copyright = f"2024-2025, {author}"
version = release

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration


extensions = [
    'sphinx.ext.autodoc',
    # 'sphinx.ext.autosummary',
    # 'sphinx.ext.intersphinx',
    'sphinx.ext.todo',
    # 'sphinx.ext.inheritance_diagram',
    # 'sphinx.ext.autosectionlabel',
    # 'sphinx.ext.napoleon',
    'sphinx_rtd_theme',
]

templates_path = ['_templates']
exclude_patterns = []
todo_include_todos = True

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']

