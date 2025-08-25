from pathlib import Path

import tomllib

workspace = Path(__file__).parent.parent.parent.parent.parent

with (workspace / "Cargo.toml").open("rb") as f:
    cargo = tomllib.load(f)
    package = cargo["workspace"]["package"]
    author = ", ".join(
        author.replace("<", "(").replace(">", ")") for author in package["authors"]
    )

with (workspace / "crates/pyndakaas/Cargo.toml").open("rb") as f:
    cargo = tomllib.load(f)
    package = cargo["package"]
    release = package["version"]
    description = package["description"]
    project = package["name"]
    copyright = f"2024-2025, {author}"

version = release

extensions = [
    "sphinx.ext.autodoc",
    "sphinx_rtd_theme",
]

autodoc_typehints = "description"  # show type hints from signature in docs

templates_path = ["_templates"]
exclude_patterns = []

html_theme = "sphinx_rtd_theme"
# html_static_path = ['_static']

html_logo = "../../../../assets/logo.svg"
pygments_style = "sphinx"

# html_theme_options = {
#     'logo_only': True,
# }
