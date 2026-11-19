# Linked-unit parity fixtures

Programs of several modules, compiled with `compile_vyper_mods`
(`lowering/defs/compileUnitScript.sml`) and compared with the pinned Python
compiler's bytes.

- `sources/twin_names/`: two modules that each declare `x` and `foo`; the
  main module exports a function of the other (`exports:`), initializes it
  (`initializes:`) with storage and an immutable, and calls `lib.__init__()`
  from its constructor.
- `sources/iface_exports/`: the main module exports a named interface of a
  module that provides one of its functions by re-exporting a third module's,
  and another module's `__interface__`, whose functions it exposes in the
  compiler's order (re-exports, external functions, public getters).
- The other cases are the multi-module programs in
  `tests/fixtures/check_contract/` (`multimodule_storage`,
  `nested_initializes`, `attribute_initializes`, `imported_deploy`,
  `initializes_alias_shadow`).
- `oracle/` holds each case's `<case>.json` (annotated AST and layout) and
  `<case>.hex` (deploy and runtime bytes), from `oracle.py` with the patched
  pinned Vyper (the settings in `../README.md`).

Check them with the native JSON runner (`tools/build_native_json_parity.py`
builds it):

```sh
bytecode/native/bytecode_parity_json.exe bytecode/linked-units/oracle
```

Regenerate, from the repository root, with the patched pin's Python (the
pin's output can depend on the hash seed):

```sh
PYTHONHASHSEED=0 python -P -s bytecode/linked-units/oracle.py bytecode/linked-units/oracle \
  bytecode/linked-units/sources/twin_names bytecode/linked-units/sources/iface_exports \
  tests/fixtures/check_contract/{multimodule_storage,nested_initializes,attribute_initializes,imported_deploy,initializes_alias_shadow}
```
