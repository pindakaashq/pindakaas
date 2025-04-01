.. Pindakaas documentation master file, created by
   sphinx-quickstart on Mon Mar 31 13:39:43 2025.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Pindakaas: Encoding Integer and Pseudo Boolean constraints into CNF 
===================================================================

TODOs
-----
- Extra installs of feature via pip (e.g. `pip install pindakaas[cadical,kissat]`)
- Better type checking and errors (e.g. adding non-list to add_clause currently gives `TypeError: argument 'clause': 'Lit' object cannot be converted to 'Sequence'`)
- Can we somehow share the documentation between pindakaas/lib and pyndakaas/lib? One way is documentation Ellipsis to text_signature to include_str ..
- VarRange -> implement Range better?
- Generate `*.pyi` stub file to support type hints

.. todo:: ConditionalDatabase with context manager: ``with ccnf as cnf.if([a,b]):``

.. toctree::
   :maxdepth: 2
   :caption: Contents:


.. automodule:: pindakaas
   :members:
   :undoc-members:


Solvers
-------

.. automodule:: pindakaas.solvers
   :members:
   :undoc-members:
