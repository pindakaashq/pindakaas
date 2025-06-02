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

extensions = [
    'sphinx.ext.autodoc',
    'sphinx_rtd_theme',
]

templates_path = ['_templates']
exclude_patterns = []
todo_include_todos = True

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']

