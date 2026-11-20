# Linked-unit parity fixtures

Programs of several modules, compiled with `compile_vyper_mods`
(`lowering/defs/compileUnitScript.sml`) and compared with the pinned Python
compiler's bytes.

- `sources/twin_names/`: two modules that each declare `x`, an immutable
  `IMM` and `foo`; the main module exports a function of the other
  (`exports:`), initializes it (`initializes:`), and calls `lib.__init__()`
  from its constructor.
- `sources/iface_exports/`: the main module exports a named interface of a
  module that provides one of its functions by re-exporting a third module's,
  and another module's `__interface__`, whose functions it exposes in the
  compiler's order (re-exports, external functions, public getters).
- `sources/default_export/`, `sources/default_interface/`: the main module
  exports another module's `__default__`, directly and through its
  `__interface__`, ahead of a function of that module; each calls its own
  internal helper, so the runtime internals follow the export order.
- The other cases are the multi-module programs in
  `tests/fixtures/check_contract/` (`multimodule_storage`,
  `nested_initializes`, `attribute_initializes`, `imported_deploy`,
  `initializes_alias_shadow`).
- `oracle/` holds each case's `<case>.json` (annotated AST and layout) and
  `<case>.hex` (deploy and runtime bytes), from `oracle.py` with the patched
  pinned Vyper (the settings in `../README.md`).

CI's `export-parity` job regenerates them with the patched pin, compares them
with the committed ones, and checks them with the native JSON runner
(`tools/build_native_json_parity.py` builds it):

```sh
bytecode/native/bytecode_parity_json.exe bytecode/linked-units/oracle
```

Regenerate, from the repository root, with the patched pin's Python (the
pin's output can depend on the hash seed):

```sh
PYTHONHASHSEED=0 python -P -s bytecode/linked-units/oracle.py bytecode/linked-units/oracle \
  bytecode/linked-units/sources/* \
  tests/fixtures/check_contract/{multimodule_storage,nested_initializes,attribute_initializes,imported_deploy,initializes_alias_shadow}
```
