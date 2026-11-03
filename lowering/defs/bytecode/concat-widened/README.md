# Widened Concat allocation regression

`concat_wide_local.vy` concatenates a runtime `Bytes[50]` argument with one
literal byte into a `Bytes[100]` local. The intermediate buffer needs capacity
51. Sizing it from the destination annotation crossed an allocation-word
boundary and produced different bytecode from Python Vyper.

`oracle/` contains the annotated AST/layout and deployment/runtime bytecode
exported with Vyper `9362e36b145c4b63ceb6a893018ea970e78bf6a6` (`VYPER_PIN`),
experimental code generation, Prague, optimization `NONE`, and disabled
bytecode metadata. The source remains an input to the runtime concatenation.

`evalCompilerConcatWidenedTheory` checks the contract in deployment and runtime
modes, then proves exact deployment and runtime bytecode equality against this
independent oracle. Run it with:

```sh
holbuild -j2 build evalCompilerConcatWidenedTheory
```

To reproduce the oracle with the pinned Vyper installation, use the
`vyper.compile_code` API with the settings above and request
`annotated_ast_dict`, `layout`, `bytecode`, and `bytecode_runtime`. Merge the
AST and layout dictionaries into the JSON fixture; write the two byte strings
without their `0x` prefixes as `deploy=...` and `runtime=...` in the hex fixture.
