# F21 — Fixed source-local offsets and name collisions

**Intended maintainer:** lowering compile environments, function-local allocation,
namespace/return dispatch. **Disposition: BOUNDED by SUPPORTED whitelist;
general lowering repair DEFERRED.** Not fixed by STOP or remap changes.
[Evidence, history and current audit](README.md).

## Concrete counterexamples and current definition behavior

These are **definition-level lowering examples**, not new built fixtures or
reference compiler executions. They instantiate PLAN's four categories:

1. **Internal locals overlap.** Internal `f()` has `x:uint256=11`, calls internal
   `g()` whose `y:uint256=22`, then returns x. With no arguments, each
   `build_compile_env` allocates its first local `MemLoc 0 32` (offsets counted
   from0), and internal bodies do not call external `reserve_local_ptrs`.
   Stores become MSTORE0=11 and MSTORE0=22, followed by f's MLOAD0. Source scoped
   locals preserve x=11; this lowered memory path reads22. Temporary return
   ALLOCAs/stack return tokens do not relocate these literal local addresses.
   Caller aggregate buffers at overlapping addresses are vulnerable too.
2. **Fallback arguments absent from entry binding.** External `__default__(x:uint256)`
   with `return x`: compile environment has x=`MemLoc 0 32`, but
   `compile_fallback_body` has no argument registration/decoding operation.
   It reads memory0 rather than the supplied argument. In a fresh zero memory,
   that read is0 even for intended x=7. This is an invalid public entry shape,
   not an assertion the Python frontend accepts fallback arguments.
3. **Duplicate branch-local names/types.** `if true: x:uint256=11; else:
   x:uint256[2]=[22,33]` has collected bindings `[(x,uint256),(x,uint256[2])]`.
   `allocate_args ... 0 FEMPTY` updates x first to`MemLoc 0 32`, then to
   **MemLoc32 64**, final cursor96; `ce_var_type x` is the last type. The
   true branch's source scope contains scalar11, but the lowered name lookup
   uses the later array binding/size. This is a concrete environment mismatch,
   not a claimed exact end-to-end RETURN byte string for ill-typed duplicate ASTs.
4. **Module/reserved-name shadowing.** Module `stored:uint256` at storage slot5,
   argument also named stored: name table replaces `StorageLoc 5w` with
   `MemLoc 0 32`; source `TopLevelName (NONE,"stored")` still denotes module
   storage, while lowered lookup sees the argument memory. With storage5=37,
   memory0=7, source reads37 versus target7. External argument named
   **`__return_pc__`**, typeuint256, creates that same memory binding. For
   `Return NONE`, `compile_stmt` emits MLOAD0 then **RET**, not external STOP;
   for a value return it selects internal RET, not ABI RETURN. Reserved
   `__return_buf__` can also collide with compiler-generated bindings.
   **The reserved-name part is fixed** (#557, a04-04): the return PC and return
   buffer now live in `ce_return_pc`/`ce_return_buf`, `Return` decides
   internal/external from `ce_return_pc`, and both names are ordinary user
   identifiers. **Module-name shadowing is fixed** (#557, a04-03): module
   variables are keyed `module_var_key` = `"self." ++ name` in `ce_vars`, so
   a local `stored` no longer replaces `StorageLoc 5w`.

The whitelist rejects internal AnnAssign/For/IntCall, calls in loop bodies,
fallback arguments and all duplicate arg/local/loop bindings. **Exclusion is not a proof these lowering bugs are
fixed for arbitrary source programs.** Some malformed AST examples would also
be rejected by source/reference typing; syntax support and typing are separate.

## Current definitions and verified support boundaries

- [Compile environments](../../lowering/defs/compileVyperScript.sml):
  `allocate_args`, `allocate_internal_special_vars`, `build_compile_env`,
  last-binding `ce_var_type`; `collect_locals` is in module lowering below.
- [Function bodies](../../lowering/defs/moduleLoweringScript.sml):
  `reserve_local_ptrs`, `compile_external_function_body`, `compile_fallback_body`,
  `compile_internal_function`; [Return dispatch](../../lowering/defs/stmtLoweringScript.sml).
- [Name whitelist](../../lowering/supported/supportedNamesScript.sml),
  [program boundary](../../lowering/supported/supportedProgramScript.sml).
- [Name regressions](../../lowering/supported/supportedNamePropsScript.sml):
  `supported_binding_duplicates_reject`, `supported_compiler_slot_names_accept`,
  `supported_module_binding_shadowing_accept`, `supported_fallback_header_names_contract`.
- [Program regressions](../../lowering/supported/supportedProgramPropsScript.sml):
  `supported_internal_context_rejections`, `supported_loop_internal_call_rejections`,
  `supported_module_bindings_accepted`, `supported_binding_duplicates_rejected`.
- All101 exact membership owners are not assumed: see the actual
  [manifest](../../lowering/defs/bytecode/supported-fixtures.txt).
  No original fixture exercises the overlapping internal-local path; membership
  is a boundary check, not semantic testing of these excluded examples.

Pinned reference `vyper/codegen/function_definitions/common.py`,
`initialize_context`, constructs a `MemoryAllocator(allocate_start)` rather
than per-function literal0; `vyper/codegen/context.py`, `Context._new_variable`
and `new_variable`, allocate typed locals. `vyper/codegen/self_call.py`,
`ir_for_self_call`, has explicit frame/argument/return-buffer handling.
`vyper/codegen/return_.py`, `make_return_stmt`, distinguishes internal/external
by function metadata, not a user-name presence test. These functions were read;
no reference acceptance/result is claimed for invalid fallback/duplicate ASTs.

## Related repaired contracts, not this source-offset fix

[STOP](F23-stop-returndata.md) is official F23/TASK023: stale bytes`[42w;7w]`
are cleared; that does not allocate local memory. TASK061, landed`8f6e5002`,
repaired remap relations to require equality of **vs_fmp, vs_call_entry_fmp,
vs_initial_fmp, vs_return_pc_token**, with explicit allocation materialization.
The permanent [frozen original GETFMP witness](../../venom/passes/shared/proofs/allocaRemapRegressionScript.sml)
is unchanged: `probe_s1=init_venom_state "entry"`,
`probe_s2=probe_s1 with vs_fmp:=1w`, roots`{}`, remap`FEMPTY`,
`GETFMP [] ["x"]` yields x=0w versus1w. `unequal_fmp_remap_inputs` verifies all
original antecedents; `unequal_fmp_remap_output` negates the **full existential
conclusion**. Do not rewrite original states or binary bytes to fit today's
stronger relation. This proof-contract fix is distinct from source fixed offsets.

## Reproduction and disposition evidence

Substitute the literal bindings above into `allocate_args`/`build_compile_env`,
then inspect body and Return dispatch. For the source11/22 overlap, inspect
scoped local writes versus literal MSTORE/MLOAD; no whole-program receipt exists
for this newly written sketch. Read named support rejection statements for the
actual current boundary. Receipts019–021 record rebuilt whitelist properties;
final022 records101 exact memberships, not an arbitrary memory-safety producer.
Receipts023/061 record actual STOP/remap counterexamples separately. S3 memory
and S1 lowering remain admitted; broader allocation safety is not proved here.

Historical PLAN: §4.3 F21,811–827; D19; §5.6 names/internal bodies;
§6.2 locals/calls. Old `allocate_args`238–244, `reserve_local_ptrs`611–629,
fallback660–672, `build_compile_env`426–441, return dispatch1089–1120.
