# TASK: Lay out internal-function frames like Vyper: ALLOCA locals, overlapping first-fit, cleanup elision, callee memory in liveness

## Meta
Status: planned
Priority: P1
Created: 2026-10-22
Issue: https://github.com/verifereum/vyper-hol/issues/545
Base: #652 at 0660f7726bfea8e293e9fa8fb1375d50e53ea280

## Task

Implement the issue below in full, including dependent proof repairs and focused validation. The issue's requested definition changes and its explicitly specified allocator theorem replacement are in scope. Follow the repository's AGENTS.md. The issue's older reserve_local_ptrs prototype must be adapted to the declaration-site ALLOCA implementation already in this branch from #652; do not reinstate the old reservation path.

## Constraints

- Use holbuild only, at most -j4. No interactive proof-state workflow.
- Keep theorem statements and assumptions except the explicit checked_first_fit_SOME replacement requested in a05-02. New or stronger hypotheses require owner approval. Report any necessary statement changes; never silently weaken correctness.
- No cheats, axioms, TRY/ORELSE around proof search, or increased tactic timeouts in completed work. Preserve original proof code in a comment if temporarily admitting it.
- Build touched theories and specific relevant evalCompiler fixture theories locally, including CI-mode checks with --skip-checkpoints --skip-proof-steps. Do not run a full-project build or evalCompilerBytecodeParityTheory. This overrides the issue's suggestion to run the entire parity corpus.
- Compare witnesses against VYPER_PIN with the oracle settings in python_o1_bytecode_oracle.py; never replace Python oracle bytes with HOL output. Check p39/p40 behavior for foo(5).
- #549 is closed. #546/#566/#560/#558/#556/#552/#562 are open; inspect current code before relying on old residual classifications. Preserve #546-dependent whitelist restrictions until its necessary work is present.
- Do not edit dependency pins or .github/workflows. Do not push or post to GitHub. Commit implementation milestones on this branch.
- Commit trailer: Bot: sol (OpenAI GPT-6.1 Sol).
- Leave generated PLAN/STATE/LEARNINGS/LOG/DOSSIER and .alan state untracked. Commit only implementation files and this task file.
- Flag every new definition and every changed concrete expectation in the completion report. Report any unresolved checklist item explicitly; partial implementation is not completion.

## Issue description

## Defect
- **a05-01: internal locals at fixed literal addresses.** `compile_internal_function` never calls `reserve_local_ptrs`,
  so locals and loop variables of internal functions keep `build_compile_env`'s `MemLoc offset` slots and are
  addressed as `Lit (n2w offset)`, invisible to ConcretizeMemLoc; a callee local can overwrite a caller local live
  across the INVOKE. Vyper allocates every local with `alloca` (`Context.new_variable`). Witness `p39_int_local_clobber`
  (`supported_program: F`), PARITY_DEFECT and a **miscompile**: minievm `foo(5)` gives real 5, HOL 6:
  ```vyper
  @internal
  def bar(y: uint256):
      z: uint256 = y + 1
      self.x = z
  @external
  def foo(x: uint256) -> uint256:
      a: uint256 = x
      self.bar(x)
      return a
  ```
  (`x: uint256` is a storage variable.) With a05-01 + a05-02, `p02_int_local_string` and `p58_int_bytes_local` keep
  residuals owned by #549 and #566:
  ```vyper
  @internal
  def bar(s: String[10]) -> String[10]:
      t: String[10] = s
      return t
  @external
  def foo(s: String[10]) -> String[10]:
      return self.bar(s)
  ```
  ```vyper
  @internal
  def f(b: Bytes[4]) -> Bytes[8]:
      c: Bytes[8] = concat(b, b)
      return c
  @external
  def foo(b: Bytes[4]) -> Bytes[8]:
      return self.f(b)
  ```
- **a05-02: compile-NONE.** `checked_first_fit` requires the occupied intervals to be pairwise disjoint, but the
  liveness allocator legitimately puts allocas with disjoint lifetimes at the same address; with a dead alloca to fill
  (the temporary return region of every stack-returning internal function), ConcretizeMemLoc and `compile_vyper`
  return NONE. Python's `MemoryAllocator.allocate` scans overlapping intervals. Witness `p74_int_ext_call` (`@view`
  internal doing `return staticcall I(t).bar(y)`, `supported_program: T`): NONE; also p76, a06 `x02_extcall_internal`,
  a08 `ctl04_internal_extcall` (T), and p09-p11, p03, p04, p41, p57 (F).
- **a05-08: cleanup elision.** `cleanup_elision_safe` (`venom/codegen/defs/stackPlanGenScript.sml:511`) is false for
  every function with a `PARAM`, so internal functions pop all dead slots at the entry of a must-halt block; for
  external functions it elides where `stack_safety.py` does not (an invoked callee with a CFG cycle). Witness
  `p92_int_revert_branch` (internal `f(y, z)` with `if y == 3: raise`, T): PARITY_DEFECT (hol 159B, real 156B,
  `POP POP POP` at the `raise` block entry); also ctl05, and p74, p76, p106, x02, ctl04 once a05-02 lands.
- **a05-03: callee memory ignored.** `compute_alloc_map_fuel_in_context` passes `mems_used = K []` to the memory
  liveness and reserves `[0, callee.fn_eom)` only for allocas live at the INVOKE; Vyper adds the callee's `mems_used`
  to the caller's livesets, fill and `eom`. Safe, but positions differ. Witness `p21_for_body_call`
  (`for i in range(3): s = self.f(s)`, F): PARITY_DEFECT (hol 159B, real 161B).

Severity: miscompile (a05-01), compile-NONE (a05-02), parity-only (a05-08, a05-03).
Inside the current whitelist: yes for a05-02 (p74, p76, x02, ctl04) and a05-08 (p92, p106, ctl05, p74, p76, x02,
ctl04); a05-01 and a05-03 are hidden.

**Why it blocks removing `supported_program`:** `supported_function_body`
(`lowering/supported/supportedProgramScript.sml:18-20`), for internal functions, requires
`supported_internal_stmts_shape body` (no `AnnAssign`/`For`; hides a05-01 and its NONE via a05-02) and
`~supported_stmts_expr_exists expr_internal_call_root body` (hides the call-chain NONE and the a05-03 positions);
`supported_stmt ... For` (`supportedStmtsScript.sml:127-130`) bans internal calls in loop bodies (a05-03). Without
them the theorems quantify over a05-01's miscompiles (p39, p40) and fail parity for internal functions with locals,
loops, nested calls or halting branches.

**Why these parts go together:** all four decide the memory and stack frame of internal functions. a05-01 alone turns
p01 and p67 into NONE (a05-02), so the two land together; a05-08 and a05-03 bring p74, p76, p92 and the nested-call
witnesses to MATCH on that layout, and a05-03 changes the same ConcretizeMemLoc fill that a05-02 relaxes.

## Dependencies
- **Depends on:** Hard: none. Validation only: #549 (a05 `p02`, `p58` keep the a11-02 flat-copy residual until a11-02
  lands); #566 (a05 `p58` keeps the a07-05 `concat` offset residual); #560 (a05 `p05_int_local_dynarray` needs a11-04
  and a07-13); #558 (`p57` needs a11-06 step 3); #556 (`p43b_int_local_word_types2` keeps an `and`-chain residual
  until a14-03 lands)
- **Blocks:** Hard: #575 (whitelist deletion). Validation only: #546 (a05-01 and a05-02 make programs whose internal
  functions have locals, loops, external calls or reason strings compile, and a05-08 and a05-03 make them MATCH;
  a05-05 and a05-07 are validated on such programs); #554 (raw_call witnesses `rc23`, `rc27`, `rc28` need a05-08: the
  cleanup POPs); #558 (a05-01 + a05-02: a05 `p57` compiles only
  with them); #560 (a05-01 + a05-02: `p05_int_local_dynarray` MATCHes only with them); #549 (a05 `p02`, `p58` MATCH
  only with a05-01 + a05-02); #566 (a05 `p58` MATCHes only with a05-01 and a05-02)
- **Coordinate with:** #546 (a05-03 step 5 re-checks the callee-first pass order after a05-05 reorders
  `ctx_functions`); #552 (a08-07 changes the BUMP semantics; a05-08 also changes `venom/codegen/defs/stackPlanGenScript.sml`
  and re-proves `genBlockSimScript.sml`/`emitSimScript.sml`, which reference `bump_emit_ops`); #561 (a05-02 and a05-03 change other inputs of the same
  ConcretizeMemLoc allocation as a14-01; re-compare #561's witnesses after both); #562 (a03-07 also changes
  `venom/codegen/defs/stackPlanGenScript.sml` (deep-dup spill order); land one after the other)

## Fix plan
Parts: a05-01, a05-02, a05-08, a05-03. Estimate: M-L (a05-01 S, a05-02 S, a05-08 M, a05-03 M-L). Layers: lowering
(a05-01), Venom pass ConcretizeMemLoc (a05-02, a05-03), codegen stack planning (a05-08).

### Order of work
1. a05-01 step 1 and a05-02 steps 1-3 in one change (a05-01 alone gives NONE); re-prove `staticLayoutAllocatorProofs`.
2. a05-08 steps 1-4: plan-state fields, the `stack_safety.py` port, the `clean_stack_plan` promise, the threading.
3. a05-03 steps 1-5; re-run its Validation after #546's a05-05.
4. Relax the whitelist conjuncts above (the internal-call ones only together with #546's a05-05).

### Fix plan a05-01: Locals and loop variables of internal functions live at fixed literal addresses (not ALLOCAs), so they clobber the caller's memory
Status: confirmed, **prototyped** (diff below; MATCH on 12 witnesses together with a05-02). Area: a05.
Severity: **miscompile** (wrong results: p39, p40), and parity-only on most other witnesses.

#### Witnesses
All are `supported_program: F` (internal bodies may not contain
`AnnAssign`/`For`), `check_contract` ACCEPT/ACCEPT, and real Vyper compiles them.

| witness | shape | baseline verdict | baseline behaviour (EVM interpreter, `foo(5)` or the witness's own arguments) | with the a05-01 + a05-02 prototypes |
|---|---|---|---|---|
| `p39_int_local_clobber.vy` | caller local `a` live across `self.bar(x)`; `bar` has local `z` | PARITY_DEFECT (hol 134B, real 133B) | **real 5, HOL 6**: `bar`'s `z` overwrites `a` | **MATCH** |
| `p40_int_for_clobber.vy` | as p39, but `bar` has a `for i in range(2)` loop | PARITY_DEFECT (hol 193B, real 195B) | **real 5, HOL 1** | **MATCH** |
| `p01_int_local_word.vy` | `z: uint256 = y + 1` in an internal | PARITY_DEFECT | same | MATCH (NONE with a05-01 alone, see a05-02) |
| `p06_int_for_range.vy` | `for i in range(3)` in an internal | PARITY_DEFECT | same | MATCH |
| `p07_int_for_array.vy`, `p08_int_for_local.vy`, `p42_int_for_dynarray_arg.vy`, `p36_int_for_return.vy` | For over an array / a local / a DynArray arg, and return from inside the loop | PARITY_DEFECT | same | MATCH |
| `p67_int_local_int128.vy` | `a: int128 = -1` in an internal | PARITY_DEFECT | same | MATCH (NONE with a05-01 alone) |
| `p68_int_local_bytes4.vy`, `p43b_int_local_word_types2.vy` | `bytes4` local; int128/address/bytes4/bool locals in an internal | PARITY_DEFECT | same | p68 MATCH; p43b still PARITY (hol 284B, real 274B), see Validation |
| `p03_int_local_array.vy`, `p04_int_local_struct.vy` | array/struct local in an internal | NONE | n/a | MATCH |
| `p05_int_local_dynarray.vy` | DynArray local in an internal | PARITY_DEFECT | same | still PARITY (hol 191B, real 190B), same behaviour: the literal `[y]` stores its length word after the element (a11-04, #560) and gets a 64-byte buffer where Vyper allocates the full `DynArray[uint256, 3]` (a07-13, #560); with a11-04's prototype and a07-13's size change added, MATCH |
| `p02_int_local_string.vy`, `p58_int_bytes_local.vy` | String/Bytes local in an internal | PARITY_DEFECT | same (`foo("abc")`, `foo(0xdeadbeef)`) | still PARITY (p02 hol 361B, real 401B; p58 hol 408B, real 468B), same behaviour: the internal function still copies the String/Bytes local with a flat 64-byte `MCOPY` where Vyper copies the runtime length (a11-02, #549), and places the staging temporary and the local at other addresses, as HOL does in the external a11 witness `c07`; p58's `f` also keeps the `concat` running offset in SSA where Vyper uses a memory temporary (a07-05, #566) |
| `p57_int_struct_local_return.vy` | internal returns a struct local; `self.f(x).b` | NONE | n/a | PARITY (hol 174B, real 175B) and **miscompile**: real 7, HOL 5. The field read `self.f(x).b` on the call result reads field `a` (a11-06 step 3, #558); with a11-06's prototype added, MATCH |
| `ctl_local_internal.vy` (from #557) | `y: uint256 = 3; return y` in an internal `g()` | PARITY_DEFECT (hol 94B, real 96B) | same | MATCH |
| `nm_local_return_buf.vy` (from #557) | as `ctl_local_internal`, local named `__return_buf__` | PARITY_DEFECT after #584 fixed its name collision (a04-04): hol 94B, real 96B, the same as `ctl_local_internal` | same | MATCH |
| `p41`, `p44`, `p60`, `p09`-`p11` | internal locals and nested calls | PARITY (p44, p60), NONE (p41, p09-p11) | same (p44, p60) | still PARITY, same behaviour: the only remaining differences are memory positions in the caller and the dead return-temp position, the callee-frame placement of a05-03 |

In the HOL IR for p01 before the Venom pipeline (baseline), `bar`'s `z` is
`MSTORE 32, %%25` / `MLOAD 32` with a literal address and no ALLOCA (the two ALLOCAs of `bar` are the parameter `y`
and the temporary return region). Real Vyper allocates `z` with `alloca` (`Context.new_variable`) and concretizes it
with the other allocations.

#### Root cause
- `lowering/defs/compileVyperScript.sml:407`, `build_compile_env`: every function's arguments **and
  locals** (`collect_locals body`) get abstract `MemLoc offset size` slots via `allocate_args`
  (`:427-429`). For internal functions this is followed by `allocate_internal_special_vars` (`:432`).
- External and fallback bodies convert the locals to ALLOCA pointers:
  `compile_guarded_body` (`lowering/defs/moduleLoweringScript.sml:626-629`) runs
  `reserve_local_ptrs cenv (collect_locals body)`, which replaces each `MemLoc` with
  `PtrVar (Var fresh) size`. `emit_local_alloca` (`stmtLoweringScript.sml:847`) then emits the
  ALLOCA at the declaration (`AnnAssign`, line 895) or loop (`For`, lines 1257 and 1334).
- `compile_internal_function` (`moduleLoweringScript.sml:675-752`) **never calls
  `reserve_local_ptrs`**. Its locals keep `MemLoc offset`. `AnnAssign`/`For` then use
  `Lit (n2w offset)` addresses directly (the `MemLoc` branches at `stmtLoweringScript.sml:900`,
  `:1291`, `:1383`, and `compile_get_target_ptr` at `:391`), and `emit_local_alloca` emits nothing. These literal
  addresses are invisible to ConcretizeMemLoc, so no caller allocation that is live across the
  INVOKE avoids them. That is how `bar`'s `z` (literal 0x20) clobbers `foo`'s `a` in p39.
- Real Vyper: `vyper/codegen_venom/stmt.py:68` (`lower_AnnAssign` → `ctx.new_variable`), `:605` and
  `:721` (loop variables). `vyper/codegen_venom/context.py:99` `new_variable` →
  `allocate_buffer` (line 637) → `builder.alloca(size)`. The same applies to every function kind.

#### Fix plan (lowering only; prototyped)
1. In `compile_internal_function`, reserve the local pointers after the parameters are
   materialised, and compile the body with the extended env:
```diff
--- a/lowering/defs/moduleLoweringScript.sml
+++ b/lowering/defs/moduleLoweringScript.sml
@@ -730,12 +730,15 @@ Definition compile_internal_function_def:
                return (SOME (FST alloc_result))
             od
           else return NONE);
+       (* Locals and loop variables are ALLOCA-backed, as in external bodies
+          (Python Context.new_variable -> allocate_buffer -> alloca). *)
+       cenv3 <- reserve_local_ptrs cenv2 (collect_locals body);
        (* Nonreentrant lock *)
        (if is_nonreentrant then
           compile_nonreentrant_lock nkey use_transient is_view
         else return ());
        (* Compile body *)
-       compile_stmts cenv2 NoLoop
+       compile_stmts cenv3 NoLoop
          (case ret_type of SOME t => t | NONE => BaseT BoolT) body;
```
   `reserve_local_ptrs` only draws fresh variable names. The ALLOCAs are still emitted at the
   declaration and loop sites, as in Python.
2. This fix alone turns p01 and p67 from PARITY into **NONE**, because the new
   ALLOCAs trigger a05-02. Land the two fixes together.
3. Leave `build_compile_env` unchanged: it still allocates the abstract `MemLoc` slots for locals, which
   `reserve_local_ptrs` now overrides in both function kinds. They stay as the declared record and keep the
   `__return_buf__`/`__return_pc__` offsets (computed after the locals) and the existing env lemmas intact.

#### Proof / repo impact
- Prototype build: `holbuild build compileVyperTheory supportedProgramTheory` succeeds with this
  change. No proof in that dependency closure mentions `compile_internal_function_def`.
- EVAL fixture: `lowering/defs/bytecode/eval/evalCompilerBytecodeAbiInternalTupleLoweringScript.sml`
  (lines 955 and 1159) unfolds `compile_internal_function_def`. Its fixture has no locals, but the
  extra `reserve_local_ptrs` monadic step must be reduced there.
- Lowering-correctness proofs for internal calls (when written) must relate the internal frame's
  ALLOCAs to the source scopes, just as for external bodies. This removes the asymmetry rather
  than adding a case.
- Whitelist: removes the reason for `supported_internal_stmts_shape` (no `AnnAssign`/`For` in
  internal bodies; `lowering/supported/supportedStmtTraverseScript.sml:139-157`,
  `supportedProgramScript.sml:18-19`). Delete it once a05-01 and a05-02 have landed. Internal bodies
  that call internal functions stay excluded by the separate `expr_internal_call_root` conjunct
  (`supportedProgramScript.sml:20`) until a05-03 and a05-05 land.
- New fixtures: p39, p40 (behavioural regressions), p01, p06, p03, p04.

#### Validation
Prototype results (the a05-01 and a05-02 prototype diffs applied together):
- `MATCH` for p01, p03, p04, p06, p07, p08, p36, p39, p40, p42, p67, p68, and #557's `ctl_local_internal` and
  `nm_local_return_buf` (their residual after #557 is this layout); minievm `foo(5)` on p39 and p40 returns 5
  on both sides.
- Residuals owned elsewhere: p02 and p58 (a11-02, #549: flat copy of the String/Bytes local, as in a11 `c07`; for p58 also a07-05, #566: the `concat` running offset), p05 (a11-04 and a07-13, #560: with a11-04's prototype and a07-13's `total_size = type_memory_bytes cenv ret_ty` added, MATCH), p57 (a11-06 step 3, #558: `self.f(x).b` reads field `a` (minievm `foo(5)`: real 7, HOL 5); with a11-06's prototype added, MATCH), p43b (a14-03, #556: the only difference is two extra jump-only blocks from the `and` chain; with the a05-08 and a14-03 prototypes added, p43b and p66 MATCH).
- p09, p10, p11, p41, p44, p60: `PARITY_DEFECT` with memory-position differences only (a05-03).
- a05-01 alone: p01 and p67 become `HOL compile_vyper = NONE` (a05-02); p06, p36,
  p39 and p40 are `MATCH` (minievm `foo(5)` on p39: 5 on both sides).

#### Dependencies / overlaps
- **a05-02 must land together with this fix** (otherwise NONE).
- a05-03 for byte parity when the internal function itself calls other internals.
- The residuals of p02, p58, p05, p57 and p43b belong to a11-02 (#549), a07-05 (#566), a11-04 and a07-13 (#560),
  a11-06 (#558) and a14-03 (#556); see Validation.

#### Estimate
S (the definition change is 3 lines). Low risk, because it reuses the external-body path verbatim.

### Fix plan a05-02: ConcretizeMemLoc gives up (compile_vyper = NONE) when liveness-shared allocas coexist with a dead alloca
Status: confirmed, **prototyped** (diff below). A diagnostic EVAL of the pass internals localises the root cause. Area: a05.
Severity: compile-NONE. **Not hidden by the whitelist:** `p74`, `p76`, a06 `x02_extcall_internal` and
a08 `ctl04_internal_extcall` are `supported_program: T` and return NONE.

#### Witnesses
`check_contract` accepts every one in runtime and deploy mode, and real
Vyper compiles all of them.

| witness | shape | verdict |
|---|---|---|
| `p09_int_chain.vy` | `foo -> f -> g`, all word args/returns | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p10_int_diamond.vy` | `foo -> f -> {g, h}` | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p11_int_deep.vy` | four-deep internal chain | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p03_int_local_array.vy` | `a: uint256[3]` local in an internal fn (+ a05-01) | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p04_int_local_struct.vy` | struct local in an internal fn (+ a05-01) | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p41_int_local_and_call.vy` | internal fn with a local and an internal call | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p57_int_struct_local_return.vy` | internal fn returns a struct local | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p74_int_ext_call.vy` (**supported_program: T**) | `@view` internal does `staticcall I(t).bar(y)`, called from external | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| `p76_int_assert_raise.vy` (**supported_program: T**) | internal with `assert y != 3, "three"` and `raise "four"` | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| a06 `x02_extcall_internal` | `extcall` in an internal fn (supported_program T) | `PARITY_DEFECT: HOL compile_vyper = NONE` |
| a08 `ctl04_internal_extcall` | `extcall` in an internal fn (supported_program T) | `PARITY_DEFECT: HOL compile_vyper = NONE` |

`diag.sh` reports `first failing prefix length 3: CFP_Simple VP_ConcretizeMemLoc` for p74 and p76, and
`diag2.sh` on `f` shows the same pattern as below. For p74, candidates `{42↦0, 51↦0, 61↦0, 64↦0, 44↦32, 49↦64}`
and the dead temporary-return alloca 46 give `layout = NONE`. For p76, candidates
`{44↦128, 83↦128, 47↦64, 86↦64, 40↦0, 79↦0, ...}` plus a dead alloca give `layout = NONE`. The
witnesses other than p74, p76, x02 and ctl04 are `supported_program: F`.

Real Vyper compiles and runs these programs. The formal compiler returns `NONE`, so neither theorem
can be instantiated with real bytecode for them. Without `supported_program`, the e2e theorems
quantify over these programs. If they say "compile_vyper = SOME bc ==> ...", the result is vacuous
on them. Either way, real-Vyper parity fails.

Diagnostic for `p09`, function `f` (the HOL IR just before ConcretizeMemLoc,
from `diag2.sh`):

```
function f eom=NONE {
    %%28 = PARAM 0
    %%29 = RETPC_PARAM 1
    %%30 = ALLOCA 32          ; Allocation 44: the stack param y, materialised
    MSTORE %%30, %%28
    %%31 = ALLOCA 32          ; Allocation 46: the "temporary return region", never used
    %%32 = ALLOCA 32          ; Allocation 47: the return-value temporary
    %%33 = MLOAD %%30
    %%34 = INVOKE @g, %%33
    %%35 = ADD %%32, 0
    MSTORE %%35, %%34
    %%36 = MLOAD %%32
    RET %%36, %%29
}
DIAG static_alloca_items = SOME [(Allocation 44,32); (Allocation 46,32); (Allocation 47,32)]
DIAG candidate = FEMPTY⟨Allocation 44 ↦ 0; Allocation 47 ↦ 0⟩   (liveness allocator; disjoint lifetimes)
DIAG layout = NONE                                              (complete_alloc_positions)
```

#### Root cause
`venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml`:

- The liveness allocator (`allocate_with_livesets_in_context`, line 810) may place two allocas
  with disjoint livesets at the same address. Here Allocation 44 and Allocation 47 both get 0. That
  is intended, and it matches Python.
- `complete_alloc_positions_with_items` (line 652) then collects every candidate interval into
  `occupied` with `checked_preserved_intervals` (line 587, helper `checked_preserved_intervals_aux` at line 568).
  The comment above the helper (lines 561-567) says that candidates
  "may intentionally ... share an address", so `occupied` contains `(0,32)` twice. Next it calls
  `complete_alloc_positions_aux` (line 630) to place allocas that have no liveset. Allocation 46
  is a dead alloca: `compile_internal_function` always emits the "temporary return region" when
  the function returns on the stack (`lowering/defs/moduleLoweringScript.sml:712-722`, the ALLOCA at line 718). The same
  happens for any alloca that liveness never sees used.
- `complete_alloc_positions_aux` calls `checked_first_fit occupied sz` (line 621):
  ```
  checked_first_fit occupied sz =
    if reserved_intervals_wf occupied then
      checked_first_fit_scan (sort_reserved_by_pos occupied) sz 0
    else NONE
  ```
  `reserved_intervals_wf` (`staticLayoutDefsScript.sml:31`) requires the intervals to be
  **pairwise disjoint**. The two equal `(0,32)` intervals fail that test, so the fill returns
  `NONE`. ConcretizeMemLoc fails, and `compile_vyper` returns `NONE`.

The precondition is stronger than it needs to be. `checked_first_fit_scan` over a list sorted by
position already handles overlapping intervals: it skips intervals that end before `start`, and
jumps `start` past any interval it hits. Python's `MemoryAllocator.allocate`
(`vyper/venom/memory_allocator.py:49-70`) scans `sorted(self.reserved)`, a set of `(position, size)`
pairs that may overlap.

The trigger therefore needs at least two allocations with disjoint lifetimes at the same position,
plus one alloca that must be filled afterwards. The temporary return region supplies the dead
alloca in every internal function that returns on the stack. The witnesses get the shared
position from an internal call and its result (p09-p11, p41), locals (p03, p04, p57), an external
call's buffers (p74, x02, ctl04) and revert-reason buffers (p76). The whitelist excludes locals and
internal calls in internal bodies, but not external calls or reason strings, so p74, p76, x02 and
ctl04 are supported programs that fail.

#### Fix plan (Venom pass definition plus its proofs)
1. In `concretizeMemLocDefsScript.sml`, weaken the guard of `checked_first_fit` to validate each
   interval and not pairwise disjointness:
   ```
   checked_first_fit occupied sz =
     if EVERY reserved_interval_wf occupied then
       checked_first_fit_scan (sort_reserved_by_pos occupied) sz 0
     else NONE
   ```
2. Keep `checked_preserved_intervals` as it is. It already checks candidates only against the
   global `reserved` intervals, which must be disjoint.
3. Change the `checked_first_fit_SOME` lemma
   (`proofs/staticLayoutAllocatorProofsScript.sml:155`). It currently concludes
   `0 < sz ==> reserved_intervals_wf ((pos,sz)::occupied)`. Make it conclude
   `EVERY (reserved_intervals_disjoint (pos,sz)) occupied` (already there), plus
   `0 < sz ==> reserved_interval_wf (pos,sz)`. `checked_first_fit_scan_SOME` (line 122) needs only
   `EVERY reserved_interval_wf rs` and sortedness. Its inductive steps never use pairwise
   disjointness of the tail.
4. No other proof changes are needed. With the prototype applied, `staticLayoutCompletionProofsTheory`
   and `concretizeMemLocTransitionProofsTheory` (the only other users of `checked_first_fit_SOME`
   and the fill) rebuild unchanged and without cheats. Their invariants only use the disjointness
   and the per-interval facts that the new lemma still provides.

##### Prototype diff (builds: `holbuild build compileVyperTheory supportedProgramTheory`, and also `staticLayoutCompletionProofsTheory concretizeMemLocTransitionProofsTheory` with no further edits)
```diff
diff --git a/venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml b/venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml
index 01d6ec69..8c008f66 100644
--- a/venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml
+++ b/venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml
@@ -620,7 +620,7 @@ End
 
 Definition checked_first_fit_def:
   checked_first_fit occupied sz =
-    if reserved_intervals_wf occupied then
+    if EVERY reserved_interval_wf occupied then
       checked_first_fit_scan (sort_reserved_by_pos occupied) sz 0
     else NONE
 End
diff --git a/venom/passes/concretize_mem_loc/proofs/staticLayoutAllocatorProofsScript.sml b/venom/passes/concretize_mem_loc/proofs/staticLayoutAllocatorProofsScript.sml
index fde58324..0544b2fb 100644
--- a/venom/passes/concretize_mem_loc/proofs/staticLayoutAllocatorProofsScript.sml
+++ b/venom/passes/concretize_mem_loc/proofs/staticLayoutAllocatorProofsScript.sml
@@ -122,7 +122,7 @@ QED
 Theorem checked_first_fit_scan_SOME[local]:
   !rs sz start pos.
     reserved_positions_sorted rs /\
-    reserved_intervals_wf rs /\
+    EVERY reserved_interval_wf rs /\
     checked_first_fit_scan rs sz start = SOME pos ==>
     start <= pos /\
     pos + sz < dimword (:256) /\
@@ -157,7 +157,7 @@ Theorem checked_first_fit_SOME:
     checked_first_fit occupied sz = SOME pos ==>
     pos + sz < dimword (:256) /\
     EVERY (reserved_intervals_disjoint (pos,sz)) occupied /\
-    (0 < sz ==> reserved_intervals_wf ((pos,sz)::occupied))
+    (0 < sz ==> reserved_interval_wf (pos,sz))
 Proof
   rpt gen_tac >> strip_tac >>
   gvs[checked_first_fit_def] >>
@@ -165,7 +165,7 @@ Proof
    EVERY (reserved_intervals_disjoint (pos,sz))
      (sort_reserved_by_pos occupied)` by
     (irule checked_first_fit_scan_SOME >>
-     simp[sort_reserved_by_pos_sorted, sort_reserved_by_pos_wf]) >>
+     simp[sort_reserved_by_pos_sorted, EVERY_sort_reserved_by_pos]) >>
   gvs[EVERY_sort_reserved_by_pos, reserved_intervals_wf_def,
       reserved_interval_wf_def]
 QED
```

#### Proof / repo impact
- Definitions: one guard in `checked_first_fit`.
- Proofs: only `staticLayoutAllocatorProofs` (`checked_first_fit_scan_SOME`, `checked_first_fit_SOME`,
  3 lines in the diff above). `staticLayoutCompletionProofs` and `concretizeMemLocTransitionProofs`
  rebuild unchanged (verified). The semantic correctness argument does not change: a filled
  dead alloca still gets an interval disjoint from every other occupied interval.
- No lowering or frontend change. Existing parity fixtures are unaffected. Their programs never had
  overlapping candidates in a function that also needed a fill, because that case returned NONE.
- Whitelist: by itself, this unblocks the `NONE` cases behind the "no internal call inside an
  internal function" and "no AnnAssign/For inside an internal function" restrictions
  (`supported_function_body`, `vis = Internal ==> ...` in
  `lowering/supported/supportedProgramScript.sml:18-20`). Full byte parity for those programs also
  needs a05-01 and a05-03.
- New fixtures: p74 and p76 (inside today's whitelist), p09 (chain), p10 (diamond), p41, p57.

#### Validation
Prototype results (the comparison procedure below; every probe is `HOL: SOME` with the prototype):
- a05-02 alone:
  - p74, p76: `PARITY_DEFECT` (p74 hol 259B, real 257B; p76 hol 637B, real 633B). The only differences are the extra
    `POP`s at the entries of the halting blocks of the internal function (**a05-08**). With the a05-08 prototype also
    applied, p74, p76, a06 `x02_extcall_internal` and a08 `ctl04_internal_extcall` are
    `MATCH`.
  - a06 `x02_extcall_internal` (hol 223B, real 221B) and a08 `ctl04_internal_extcall` (hol 261B, real 259B):
    `PARITY_DEFECT`, only two extra `POP`s each (a05-08).
  - p09, p10, p11, p41: `PARITY_DEFECT` with memory-position differences only. In p09 the only difference is the
    dead return-temp alloca of `f`: 0x40 (real) versus 0x20 (HOL); that is a05-03.
  - p03, p04 (hol 203B/167B, real 204B/168B): their locals are still at literal addresses (a05-01).
  - p57 (hol 175B, real 175B): `self.f(x).b` reads field `a` (minievm `foo(5)`: real 7, HOL 5). That is a11-06.
- a05-01 + a05-02: p03 and p04 are `MATCH`; the other results are in a05-01's Validation.
- Build: with the prototype and no other edit, `holbuild build compileVyperTheory supportedProgramTheory`
  and `holbuild build staticLayoutCompletionProofsTheory
  concretizeMemLocTransitionProofsTheory` succeed; the diff contains no cheat.

#### Dependencies / overlaps
- a05-01 (internal locals at literal addresses) and a05-03 (callee memory not modelled). Byte
  parity of most witnesses needs all three. This fix is the one that turns NONE into SOME.
- The failing fill (`complete_alloc_positions_with_items`) runs for every function kind, so the
  fix covers the same NONE in any function that has two liveness-shared allocas and a dead alloca.

#### Estimate
S. One definition guard plus three lines in two lemmas (verified to build through the
transition proofs).
Low risk: the scan is already correct on overlapping input.

### Fix plan a05-08: Codegen never elides dead-stack cleanup POPs in internal functions, and its elision test is not Python's
Status: confirmed, **prototyped** (exact port as an EVAL-compset override; see Validation). Area: a05.
Severity: parity-only (extra or missing `POP`s at the entry of halting blocks; the behaviour is the same).
**Not hidden by the whitelist:** p92, p106, ctl05, p74, p76, x02 and ctl04 are `supported_program: T`.

#### Witnesses
`check_contract` accepts all of them in both modes, and real Vyper
compiles them. "Prototype" is the exact port of Validation.

| witness | shape | baseline verdict | with the prototype |
|---|---|---|---|
| `a05/p92_int_revert_branch.vy` (**T**) | internal `f(y, z)` with `if y == 3: raise`, called from `foo` | `PARITY_DEFECT runtime@54 (hol 159B, real 156B)`: HOL has `POP POP POP` at the entry of the `raise` block. Real keeps the dead `y`, `z` and return-pc slots | `MATCH` |
| `a08/ctl05_internal_raise.vy`, `a14/ctl05_internal_raise.vy` (**T**) | internal `h(x)` with `if x == 0: raise` | `PARITY_DEFECT runtime@54 (hol 134B, real 132B)`: `POP POP` at the entry of the `raise` block | `MATCH` |
| `a05/p74_int_ext_call.vy` (**T**) | `@view` internal with `staticcall` | NONE (a05-02); with the a05-02 fix: `PARITY (hol 259B, real 257B)`, `POP POP` at the entry of the `extcall_fail` block | with a05-02: `MATCH` |
| `a05/p76_int_assert_raise.vy` (**T**) | internal with `assert y != 3, "three"` and `raise "four"` | NONE (a05-02); with the a05-02 fix: `PARITY (hol 637B, real 633B)`, two `POP POP` sequences | with a05-02: `MATCH` |
| `a06/x02_extcall_internal.vy`, `a08/ctl04_internal_extcall.vy` (**T**) | `extcall` in an internal function | NONE (a05-02); with the a05-02 fix: `PARITY` (x02 hol 223B, real 221B; ctl04 hol 261B, real 259B), two extra `POP`s | with a05-02: `MATCH` |
| `e02_halt_region_invoke_loop` (F) | external `foo` does `if x == 3: self.g(); raise`; internal `g` has a `for` loop | `PARITY_DEFECT runtime@54 (hol 186B, real 191B)`: HOL elides the cleanup at the entry of the `self.g(); raise` block, real pops (the invoked `g` has a CFG cycle, so Python's regional growth is `None`). The other differences are in `g` (a05-01) | `PARITY (hol 187B, real 191B)`: the `foo` difference is gone, the `g` differences (a05-01) remain; with a05-01 and a05-02: `MATCH` (without the prototype: `PARITY (hol 190B, real 191B)`) |
| `a05/p106_int_nested_halt_branches.vy` (**T**) | internal `f` with nested `if x == 3: (if y == 2: raise "a") raise "b"`: the inner elision reuses the promise of the outer one | NONE (a05-02); with the a05-02 fix: `PARITY (hol 669B, real 667B)` | with a05-02: `MATCH` |
| `a05/p107_int_halt_region_loop.vy` (F) | internal `f` with `if x == 3: (for loop) raise`: the loop keeps the branch out of the must-halt set | `PARITY (hol 218B, real 215B)`; the same with a05-01 and a05-02 | `PARITY (hol 216B, real 215B)` (a05-01); with a05-01 and a05-02: `MATCH` |
| `a05/p108_int_halt_region_invoke_loop.vy` (F) | internal `f` with `if x == 3: self.g(); raise`, `g` has a loop (e02 inside an internal function) | `PARITY (hol 226B, real 230B)`; with a05-01 and a05-02: `PARITY (hol 230B, real 230B)`, only the placement of `f`'s code differs (a05-05) | unchanged (`f` must pop, because `g` has a cycle); with a05-01 and a05-02 the same a05-05 placement difference |
| `e01_halt_region_loop` (**T**) | e02 with the loop written inline in `foo` | `MATCH` | `MATCH` |

A disassembly diff shows no other differences for p92 and ctl05 (baseline) and for p74, p76, x02 and ctl04
(with a05-02): apart from the PUSH2 targets, HOL only has the extra POPs. The control
`a05/p91_ext_staticcall_control.vy` (the same `staticcall` in an **external** function) is `MATCH`.

#### Root cause
- `venom/codegen/defs/stackPlanGenScript.sml:511` defines:
  ```
  cleanup_elision_safe cfg fn bb <=>
    ~EXISTS (λinst. is_param_opcode inst.inst_opcode)
       (FLAT (MAP (λb. b.bb_instructions) fn.fn_blocks)) /\
    MEM bb.bb_label (must_halt_labels cfg fn) /\
    LENGTH (cleanup_frame_vars fn) + cleanup_max_transient fn ≤ 1024
  ```
  Every internal function has `PARAM`/`RETPC_PARAM`, so the test is always false for them, and
  `clean_stack_plan` (line 541) then takes the `popmany_plan (MAP Var to_pop)` branch and pops every dead slot
  at the entry of a must-halt successor of a branching block. For external functions the test bounds the whole
  frame of `fn` and has no cycle test and no promise, so it elides where Python does not when an invoked
  function has a CFG cycle (e02).
- Real Vyper: `vyper/venom/venom_to_assembly.py:622-699` `clean_stack_from_cfg_in`. It returns the incoming
  bound when no dead slot is physically on the stack (lines 647-648) and pops all of them when none lies below every
  live value (lines 668-670). Otherwise `projected_height = stack.height - len(to_cleanup)` (line 673) and the
  promise is the incoming `stack_height_bound` or, when that is `None`,
  `StackCleanupSafety.stack_height_bound(bb, projected_height)` (lines 678-682). With no promise it pops every
  dead slot (lines 684-686); with one it pops `to_cleanup`, marks the retained prefix dead and returns the promise
  (lines 688-699). `_generate_evm_for_basicblock_r` (line 525) passes the block's resulting bound to all
  successors (line 614) and starts every function with `None` (line 234). Only the `None`-ness of the bound
  changes the bytes; its value is used by `CompilerPanic` checks only (`_observe_stack_height`, line 478).
- `vyper/venom/stack_safety.py`:
  - `max_safe_current_height` (lines 39-61): `None` unless `bb` is must-halt, the caller height is defined and the
    regional growth from `bb` is defined; otherwise `1024 - caller height - growth`. `stack_height_bound`
    (lines 63-71) is `None` iff the current height exceeds it, i.e. it is defined iff
    `caller height + projected height + growth <= 1024`.
  - `_max_caller_stack_height` (lines 93-114): the entry function contributes 0; each caller (from
    `FCGGlobalAnalysis.get_call_sites`) contributes its own caller height + `_max_function_frame_growth(caller)`;
    `None` if any caller's height is `None` or there is no contribution; otherwise the maximum.
  - `_max_function_frame_growth` (lines 116-133) = distinct variables of the function + the max over its
    instructions of `len(operands) + 2`. That is HOL's `LENGTH (cleanup_frame_vars fn) + cleanup_max_transient fn`.
  - `_max_growth_from_block` / `_stack_growth_summary` (lines 150-204): memoised DFS over CFG successors.
    The summary of `bb` is the set of variables of the blocks reachable from `bb` and the max transient there;
    an `invoke` adds `_max_growth_from_function(callee)` (lines 135-148, the summary from the callee's entry
    block) to its transient. It is `None` iff a CFG cycle is reachable from `bb` (a block met while active,
    line 164) or a reachable `invoke` has a callee with `None` growth (line 181). The growth is
    `len(variables) + transient`.

#### Fix plan (codegen definitions only)
1. `venom/codegen/defs/stackPlanTypesScript.sml`: add three fields to `plan_state` (lines 33-39) and initialise
   them in `init_plan_state` (line 145):
   ```
   ps_cleanup_height : num option;                 (* read-only: caller stack height of the function *)
   ps_cleanup_growth : (string # num option) list; (* read-only: growth summary of every function *)
   ps_cleanup_promised : bool                      (* Python's stack_height_bound is not None *)
   ```
   with `ps_cleanup_height := NONE; ps_cleanup_growth := []; ps_cleanup_promised := F`.
2. `venom/codegen/defs/stackPlanGenScript.sml`: add `fcgDefs` to `Ancestors` (it needs only `venomInst`,
   `relation` and `cfgDefs`). Replace the comment at lines 495-498 and `cleanup_elision_safe` (line 511) by a
   port of `stack_safety.py`:
   ```
   (* _max_function_frame_growth *)
   cleanup_frame_growth fn = LENGTH (cleanup_frame_vars fn) + cleanup_max_transient fn

   (* _max_caller_stack_height; fuel LENGTH ctx.ctx_functions (call graphs are acyclic) *)
   (cleanup_caller_height 0 ctx fcg name = NONE) /\
   (cleanup_caller_height (SUC n) ctx fcg name =
      let callers = FILTER (λc. MEM name (fcg_get_callees fcg c.fn_name)) ctx.ctx_functions in
      let hs = (if ctx.ctx_entry = SOME name then [SOME 0] else []) ++
               MAP (λc. OPTION_MAP (λh. h + cleanup_frame_growth c)
                                   (cleanup_caller_height n ctx fcg c.fn_name)) callers in
      if NULL hs \/ EXISTS IS_NONE hs then NONE else SOME (FOLDL MAX 0 (MAP THE hs)))

   (* the transient of one instruction (_stack_growth_summary, lines 171-186) *)
   cleanup_inst_transient growth inst =
     if inst.inst_opcode = INVOKE then
       (case inst.inst_operands of
          Label callee :: _ =>
            (case ALOOKUP growth callee of
               SOME (SOME g) => SOME (LENGTH inst.inst_operands + 2 + g)
             | _ => NONE)
        | _ => NONE)
     else SOME (LENGTH inst.inst_operands + 2)

   cleanup_block_summary growth bb =
     OPTION_MAP (λts. (FLAT (MAP (λinst. operand_vars inst.inst_operands ++ inst.inst_outputs)
                                 bb.bb_instructions),
                       FOLDL MAX 0 ts))
                (OPT_MMAP (cleanup_inst_transient growth) bb.bb_instructions)

   (* labels reachable from lbl *)
   (cleanup_reach_iter 0 cfg ls = ls) /\
   (cleanup_reach_iter (SUC n) cfg ls =
      cleanup_reach_iter n cfg (nub (ls ++ FLAT (MAP (cfg_succs_of cfg) ls))))
   cleanup_reach cfg fn lbl = cleanup_reach_iter (LENGTH fn.fn_blocks) cfg [lbl]

   (* labels from which a CFG cycle is reachable: repeatedly drop the labels without a
      successor in the set *)
   (cleanup_peel 0 cfg ls = ls) /\
   (cleanup_peel (SUC n) cfg ls =
      cleanup_peel n cfg (FILTER (λl. EXISTS (λs. MEM s ls) (cfg_succs_of cfg l)) ls))
   cleanup_cyclic cfg fn =
     cleanup_peel (LENGTH fn.fn_blocks) cfg (MAP (λbb. bb.bb_label) fn.fn_blocks)

   (* _max_growth_from_block *)
   cleanup_region_growth growth cfg fn lbl =
     if MEM lbl (cleanup_cyclic cfg fn) then NONE else
     case OPT_MMAP (λl. case lookup_block l fn.fn_blocks of
                          NONE => NONE
                        | SOME bb => cleanup_block_summary growth bb)
                   (cleanup_reach cfg fn lbl) of
       NONE => NONE
     | SOME sums => SOME (LENGTH (nub (FLAT (MAP FST sums))) + FOLDL MAX 0 (MAP SND sums))

   (* _max_growth_from_function of every function reachable from the entry, callees first *)
   cleanup_growth_table ctx fcg =
     case ctx.ctx_entry of
       NONE => []
     | SOME e =>
         FOLDL (λtbl name.
                  case lookup_function name ctx.ctx_functions of
                    NONE => tbl
                  | SOME func =>
                      case fn_entry_label func of
                        NONE => tbl
                      | SOME l => (name, cleanup_region_growth tbl (cfg_analyze func) func l) :: tbl)
               [] (fcg_postorder fcg e)

   (* stack_height_bound bb h is not None *)
   cleanup_elision_safe ch growth cfg fn bb h <=>
     MEM bb.bb_label (must_halt_labels cfg fn) /\
     case (ch, cleanup_region_growth growth cfg fn bb.bb_label) of
       (SOME c, SOME g) => c + h + g <= 1024
     | _ => F
   ```
   `fcg_get_callees` (`venom/analysis/fcg/defs/fcgDefsScript.sml:89`) records only the functions reachable from
   the entry, as `FCGGlobalAnalysis` does, and `fcg_postorder` (line 54) lists callees before callers. Call graphs
   are acyclic: `check_contract` requires `contract_call_graph_acyclic`
   (`semantics/type/vyperTypeCallGraphScript.sml:180`), and the Venom pipeline returns NONE unless
   `reachable_fcg_acyclic` holds (`venom/defs/venomPipelineDriverScript.sml:99-101`). The entry function is
   `ctx.ctx_entry` (`__entry` for runtime, `__deploy` for deploy; `lowering/defs/compileVyperScript.sml:965`,
   `:996`), Python's `ctx.entry_function` (`vyper/codegen_venom/module.py:125-126`, `:194-195`).
3. Rewrite the `SOME pred_bb` branch of `clean_stack_plan` (lines 553-574) to compute the partition first and to
   test and record the promise:
   ```
   | SOME pred_bb =>
       let inputs = ... ; layout = ... ; to_pop = ... in          (* unchanged *)
       let physical = FILTER (λop. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop) in
       let retained = FILTER (λop. below_all_live op inputs ps.ps_stack) physical in
       let to_cleanup = FILTER (λop. ¬MEM op retained) physical in
       let ok = (ps.ps_cleanup_promised \/
                 cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb
                   (LENGTH ps.ps_stack - LENGTH to_cleanup)) in
       let promised = (ps.ps_cleanup_promised \/ (ok /\ ¬NULL retained)) in
       if NULL inputs ∧ ok then
         ([], ps with <| ps_stack := MAP (K dead_stack_marker) ps.ps_stack;
                         ps_cleanup_promised := promised |>)
       else if ok then
         let (ops, ps') = popmany_plan to_cleanup ps in
         (ops, ps' with <| ps_stack := mark_dead_stack retained ps'.ps_stack;
                           ps_cleanup_promised := promised |>)
       else popmany_plan (MAP Var to_pop) ps
   ```
   The promise is path-carried with no further change: `generate_succs_plan` gives every successor
   `ps_g with <| ps_stack := saved_stack; ps_spilled := saved_spilled |>` of the block's own final state and
   copies only `ps_alloc` and `ps_label_counter` back from a child.
4. Thread the two read-only values. `generate_fn_plan_analyzed liveness dfg cfg ch growth fn spill_base lbl_ctr`,
   `generate_fn_plan ch growth fn spill_base lbl_ctr` and `generate_fn_plan_fuel fuel ch growth fn spill_base
   lbl_ctr` (lines 1096-1130) build the initial state as
   `(init_plan_state spill_base) with <| ps_label_counter := lbl_ctr; ps_cleanup_height := ch;
   ps_cleanup_growth := growth |>`. `generate_context_plan_with gen ctx` (line 1197) computes
   `fcg = fcg_analyze ctx` and `growth = cleanup_growth_table ctx fcg` and passes
   `(λfn. gen (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx fcg fn.fn_name) growth fn)` to the
   unchanged `generate_context_regions` (line 1158). `generate_context_plan` and `generate_context_plan_fuel`
   keep their text and signatures. `generate_fn_plan_aux*`, `generate_block_plan` and `clean_stack_plan` keep
   their signatures.

#### Proof / repo impact
- `venom_asm_rel` (`venom/codegen/defs/codegenRelScript.sml:319`) reads only `ps_stack`, `ps_spilled` and
  `ps_alloc`. Add the simp lemma that it is unchanged by updates of the three new fields.
- `clean_ops_sim` (`venom/codegen/proofs/cleanOpsSimScript.sml:646`) case-splits only on the predicate
  (`Cases_on \`cleanup_elision_safe cfg fn bb\``, line 674) and uses `venom_asm_rel_mark_all_dead`,
  `venom_asm_rel_mark_dead_stack` and `popmany_plan_sim_under17`, none of which depends on it. Change the
  `Cases_on` term to `ok` and add the new simp lemma. No file outside `stackPlanGenScript.sml` and
  `cleanOpsSimScript.sml` mentions `cleanup_elision_safe`, `cleanup_frame_vars`, `cleanup_max_transient` or
  `must_halt_labels`. The 1024 bound is not part of any verified statement, so the new test adds no proof
  obligation.
- `venom/codegen/proofs/allocMonoScript.sml:1000-1022` (`clean_stack_plan_spill_base`/`_next_offset`,
  `every_case_tac`) and `genBlockSimScript.sml:5716` (`gen_block_plan_decompose`) re-run unchanged in substance;
  the new field updates do not touch `ps_alloc`.
- Extra arguments (mechanical): `allocMonoScript.sml:1144`/`1174` (`generate_fn_plan(_fuel)_alloc_mono`),
  `contextPlanLayoutPropsScript.sml` (`generate_context_plan_with_layout`, line 113: the hypothesis on `gen`
  quantifies over `ch growth` too; `generate_context_plan_layout_wf`), `planSpillBoundsScript.sml:554`
  (`generate_context_plan_with_access_bounded`: the `Cases_on` term names the new lambda), and the
  `init_plan_state … with ps_label_counter := ctr` lemmas (`planSpillBoundsScript.sml:113`,
  `genBlockSimScript.sml:1103`) get the two new initial fields. `codegenCorrectnessScript.sml:264`,
  `codegenOracleRegressionScript.sml:43` and the `plan_state_component_equality` proofs (`doSwapSimScript.sml`,
  `genBlockSimScript.sml`) unfold or compare whole states and only see the new fields as unchanged.
  The theorems at `stackPlanGenScript.sml:1225` and `:1237` are about `generate_context_regions` and do not
  change. The 12 EVAL fixtures in `lowering/defs/bytecode/eval/` that call `generate_fn_plan*`,
  `generate_context_plan_with_def` or `init_plan_state` get the extra arguments (`NONE`/`[]` reproduce today's
  external-function bytes only where they match Python; re-check the expected outputs).
- Whitelist: none. This is a codegen gap that the whitelist does not hide. Every supported internal function
  with a halting branch (an `assert`, a `raise`, an external call with a failure check, an overflow check whose
  revert block has a single predecessor, ...) is affected.
- New fixtures: p92, p106, p74 and p76 (p74, p76 and p106 also need a05-02).

#### Validation
Prototype: an SML file inserted into the comparison procedure below (optionally also with the a05-02
fix). It defines the functions of step 2 under `ex_` names, a copy of the planner with step 3 (`ex_clean`,
`ex_block_plan`, `ex_aux`/`ex_succs`, `ex_fn_plan`) that threads the caller height, the growth table and the
promise as explicit arguments, and overrides `generate_context_plan` in the EVAL compset; no rebuild is needed.
Results at 0273aab9 (`check_contract` ACCEPT/ACCEPT throughout):
- p92, a08 and a14 `ctl05_internal_raise` and e01 `MATCH`;
  e02 `PARITY (hol 187B, real 191B)` with the differences only in `g` (a05-01).
- With a05-02: p74, p76, a06 `x02_extcall_internal`, a08 `ctl04_internal_extcall`
  `MATCH`; p106 `MATCH` (without the prototype `PARITY (hol 669B, real 667B)`).
- With a05-01 and a05-02 (the a05-01 diff applied): e02, p107 and p39 `MATCH`; p108 differs only in the placement of `f`'s code (a05-05). Without the prototype: e02 `PARITY (hol 190B, real 191B)`, p107 `PARITY (hol 218B, real 215B)`.

After the fix, re-run the same probes with the comparison procedure below; expect the same verdicts.

#### Dependencies / overlaps
- Validation only: p74, p76, x02, ctl04 and p106 compile only with a05-02; e02, p107 and p108 match only with
  a05-01 (internal-function loop variables).
- The code change is independent of a05-01, a05-02, a05-03, a05-05, a05-06 and a05-07.

#### Estimate
M. The definitions are small fuel-bounded folds; the plan-state fields and the extra arguments are the bulk of
the work. The proof risk is low, because the simulation proof is generic in the predicate.

### Fix plan a05-03: ConcretizeMemLoc ignores callee memory (`mems_used`) in the caller's liveness, fill and eom
Status: confirmed (by IR comparison; not prototyped). Area: a05. Severity: parity-only. (HOL's
layout is still safe. It only omits reservations at points where no caller alloca is live across the
call. Positions and the frame size differ from real Vyper.)

#### Witnesses
All are `check_contract` ACCEPT in both modes, real Vyper OK,
`supported_program: F`. Behaviour checked with an EVM interpreter (`foo("abc")` for p47) gives the same results.

| witness | shape | baseline verdict | observed layout difference (disassembly diff, real IR) |
|---|---|---|---|
| `p21_for_body_call.vy` | external `foo`: `s` local; `for i in range(3): s = self.f(s)` | `PARITY_DEFECT runtime@54 (hol 159B, real 161B)` | real: `s` at 0x60, `i` at 0x40, above `f`'s frame `[0,0x40)`; HOL: `s` at 0x20, `i` at 0 |
| `p62_for_body_call_clobber.vy` | as p21 with `s = 100` | `PARITY_DEFECT runtime@54 (hol 160B, real 162B)` | real `s` at 0x60, `i` at 0x40; HOL `s` at 0x20, `i` at 0. Both return 0x67 |
| `p45_for_body_call_loopvar.vy` | loop variable passed to an internal call in the loop | `PARITY_DEFECT runtime@54 (hol 176B, real 177B)` | two caller allocas: real at 0x60 and 0x40, HOL at 0x40 and 0 |
| `p47_len_of_string_call.vy` | `len(self.f(s))` with a String return | `PARITY_DEFECT runtime@54 (hol 220B, real 221B)` | two caller buffers: real at 0 and 0x40, HOL at 0x40 and 0. Before the first `CALLDATACOPY`, real pushes 0x40 and 0 and adds `SWAP3 SWAP2`; HOL pushes 0x40 twice |
| `p51_augassign_call.vy` | `s += self.f(y); self.x += self.f(s)` | `PARITY_DEFECT runtime@54 (hol 192B, real 193B)` | caller allocas: real at 0 and 0x40, HOL at 0x20 and 0; both return 6 for `foo(3)` |
| `p09_int_chain.vy` | `foo -> f -> g` | NONE (a05-02); with a05-01 + a05-02: `PARITY_DEFECT runtime@127 (hol 155B, real 155B)` | `f`'s dead return-temp alloca: real at 64 (`f` eom 96), HOL at 32 (`f` eom 64) |
| `p01_int_local_word.vy` | internal with a local | with a05-01 + a05-02: `MATCH` | `runtime` eom: real 64, HOL 32. The eom has no effect on the bytes here |

Real IR for p21 (`vyper -f ir_runtime --experimental-codegen -O none --evm-version prague`):
`function "internal 0 f(uint256)_runtime" [fmp_lowered, eom=64]` (param `y` at 0, dead return-temp
at 32). In `runtime` (`[fmp_lowered, eom=128]`), the loop counter is at 64 and `s` at 96. So the
whole loop, and not only the INVOKE, avoids `[0,64)`.

#### Root cause
HOL, `venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml`:
- `compute_alloc_map_fuel_in_context` (line 825) runs
  `mem_liveness_analyze_fuel fuel bpr (K ([] : allocation list)) ...` (line 832). The analysis has a
  `mems_used` parameter (`ml_liveat_inst`, line 188; the comment at line 194 reads "INVOKE: add callee
  mems_used + all operand base ptrs"), but the pass passes the constant empty function, so no callee
  allocation is ever live in the caller.
- As a substitute, `call_frame_at_addr` (line 784) and `call_frame_reservations` (line 805) reserve
  `[0, callee.fn_eom)` while allocating an alloca, **only when that alloca's own liveset contains
  the INVOKE instruction**. Allocas that are not live at the invoke (a loop counter that is written
  but never read across the call, or a value reloaded before the call and rewritten after it) are
  free to overlap the callee frame.
- The dead-alloca fill (`complete_alloc_positions*`) and the function eom do not see the callee
  frame either.

Real Vyper:
- `vyper/venom/analysis/mem_liveness.py:86` (liveat) and `:132` (used): at an `invoke`, the
  callee's `mem_allocator.mems_used[fn]` is added to both sets. The liveset of each callee
  allocation in the caller is `liveat ∩ used`. Through the backward dataflow it spans from earlier
  uses to the invoke, and around loop back-edges it covers the whole loop body.
- `vyper/venom/passes/concretize_mem_loc.py:33-53`: callee allocations are `already_allocated`
  (line 33; their positions are fixed by the callee's concretization, and `end_fn_allocation`
  records the callee's `mems_used`, `memory_allocator.py:90`). Every new caller alloca whose liveset intersects a callee
  allocation's liveset reserves it. `allocator.add_allocated` (line 39) puts them in `allocated_fn`, so
  `reserve_all()` (line 53) makes the dead-alloca fill avoid them, and the function's `eom`
  includes them (`compute_fn_eom`, `memory_allocator.py:94-101`).

#### Fix plan (Venom pass only)
1. Record per-function memory usage when a function is concretized: add
   `fn_mems_used : (allocation # num # num) list` to the function record next to `fn_eom`
   (`venom/defs/venomInstScript.sml:165`): each allocation with its position and size, **transitively**
   including the `fn_mems_used` of every function it invokes (`memory_allocator.py:90` sets
   `mems_used[fn] = allocated_fn`, and `allocated_fn` already contains the callee allocations added
   by `add_allocated`). Use the `Allocation` identities as they are: an allocation is the `inst_id`
   of its ALLOCA (`venom/analysis/shared/defs/memLocDefsScript.sml:25`), and `lowering_context_ok`
   (`lowering/defs/vyperCompilerScript.sml:395-401`) requires `ctx_inst_ids_distinct`
   (`venom/defs/venomWfScript.sml:605`), so the identities are unique across the functions of a
   context. The proofs of this plan carry `ctx_inst_ids_distinct` to the ConcretizeMemLoc step.
2. In `compute_alloc_map_fuel_in_context`, pass
   `mems_used = λcallee. MAP FST (callee's fn_mems_used)` to `mem_liveness_analyze_fuel`, and
   let `alloca_sizes` answer for callee allocations.
3. Treat the callee allocations that appear in the caller's livesets as `already` items, with their
   recorded positions (as `pre_allocated` does for forced positions). `allocate_with_livesets*`
   then reserves them exactly when the livesets intersect. Delete `call_frame_reservations` and
   `call_frame_at_addr`.
4. Add all callee allocations of the function (live or not) to the reserved/occupied list that
   `complete_alloc_positions_with_items` uses for the dead-alloca fill (Python `reserve_all`), and
   to the computation of `fn_eom`.
5. Order: Python runs the function passes callee-first, a DFS post-order over the call graph from the
   entry function (`_run_fn_passes_r`, `vyper/venom/__init__.py:200-228`). HOL does the same: the
   pipeline driver runs the function passes, ConcretizeMemLoc included, with `run_callee_first` over
   `fcg_postorder frozen_fcg entry` (`venom/defs/venomPipelineDriverScript.sml:106-107`), and the
   dispatcher concretizes one function at a time with `concretize_function_fuel_in_context`
   (`venom/defs/venomPassDispatcherScript.sml:166-167`). So every callee's `fn_mems_used` exists when
   its callers are concretized, whatever the order of `ctx_functions`. After a05-05 (which reorders
   `ctx_functions`) lands, re-run the Validation probes to confirm it.

#### Proof / repo impact
- `concretizeMemLocDefs`: `compute_alloc_map_fuel_in_context`, `call_frame_*`,
  `complete_alloc_positions*`, and the eom computation. `mk_raw_function`
  (`venom/defs/venomInstScript.sml:176`) sets the new `fn_mems_used` field to `[]`.
- Proofs: `concretizeMemLocTransitionProofs` and `staticLayoutCompletionProofs` (they unfold
  `concretize_function_fuel_in_context` and `complete_alloc_positions*`), and
  `venom/props/venomPassDispatcherPropsScript.sml`, which uses their ConcretizeMemLoc metadata and
  eom lemmas. No proof mentions `call_frame_reservations`, `call_frame_at_addr`,
  `compute_alloc_map_fuel_in_context` or `mem_liveness_analyze_fuel`. The semantic argument gets
  *stronger*: callee memory is disjoint from every caller alloca whose liveset meets it.
- Parity fixtures: the `*_matches_python_oracle` theorems compare with the pinned Python bytes, so
  re-run the whole fixture corpus; every fixture must stay proved.
- Whitelist rows this enables: the `For`-body restriction
  (`~supported_stmts_expr_exists expr_internal_call_root body` in `supported_stmt ... For`,
  `lowering/supported/supportedStmtsScript.sml:127-130`), and the internal-calls-in-internal
  restriction (`supportedProgramScript.sml:18-20`), together with a05-01 and a05-02.

#### Validation
- Re-probe `p21 p45 p62 p47 p51` with the comparison procedure below: expect `MATCH`.
- With a05-01 and a05-02 applied: `p09 p10 p11 p41 p44 p60`. With only those two fixes they are
  `PARITY_DEFECT` with memory-position differences only; with this
  fix, expect `MATCH`.
- Compare `eom` per function with the real IR (header `[fmp_lowered, eom=N]`) using
  the HOL IR of the same compilation.
- After a05-05 lands, re-run these probes (step 5).

#### Dependencies / overlaps
- a05-02 must be fixed for nested internal calls to compile at all.
- a05-01: once internal locals become allocas, they are subject to the same callee-frame
  reservations.
- a05-05 reorders `ctx_functions`; re-run the Validation after it lands (step 5).

#### Estimate
M-L. The definition change is moderate. Getting `mems_used` threaded through the
callee-first concretization, and its proofs, is the main cost. Risk: the livesets of callee
allocations around loops must equal Python's; the loop witnesses p21, p45 and p62 check them.

### Witness sources

The sources of the remaining witnesses named in this issue are in the first comment of this issue. The two
witnesses taken over from #557:

`ctl_local_internal`:
```vyper
@internal
def g() -> uint256:
    y: uint256 = 3
    return y

@external
def f() -> uint256:
    return self.g()
```

`nm_local_return_buf`:
```vyper
@internal
def g() -> uint256:
    __return_buf__: uint256 = 3
    return __return_buf__

@external
def f() -> uint256:
    return self.g()
```

### Validation procedure
Compare a program by compiling it with the pinned Vyper (0.5.0a4, commit cd74ce4f) with the settings of
`lowering/defs/bytecode/python_o1_bytecode_oracle.py` (`optimize=NONE`, `evm_version="prague"`,
`experimental_codegen=True`, no bytecode metadata), and with the HOL compiler: export the AST with
`vyper -f annotated_ast,layout`, convert it with `tests/sanitize_check_contract_json.py`, build the input with
`vyperCheckContractFrontendLib.prepare_check_input`, run `vyperCheckContractLib.check_contract`, and `EVAL`
`compile_vyper (K SOME) (o1_policy all_capabilities) tops`. Verdicts: MATCH (checker accepts, deploy and runtime
bytecode equal); PARITY_DEFECT (checker accepts, bytecode differs or `compile_vyper` gives `NONE`). Behaviour checks
run both runtime bytecodes in an EVM interpreter and compare return values and storage. Run every witness of the four
plans' Validation sections, the internal-call programs that MATCH today (p15, p16, p22, p27, p28, p29, p35, p37,
p38, p59, p72, p75, p77, p78, p79, p81, p83, p84, p91; they must stay MATCH), and after all four land the whole
parity corpus.

`minievm` in this issue is a small Python EVM interpreter used for the behaviour checks: it runs a runtime bytecode on
the given calldata and storage and reports the return data, revert and storage writes. Any EVM implementation
(for example py-evm) gives the same results.

### Done when
- [ ] a05-01 and a05-02 landed together; `staticLayoutAllocatorProofs` re-proved; dependent theories rebuild without
  cheats.
- [ ] `cleanup_elision_safe` is `stack_safety.py`'s test (caller height, growth table, promise in the plan state);
  codegen proofs rebuild without cheats.
- [ ] Callee `mems_used` drives caller liveness, fill and `fn_eom`; `call_frame_reservations` deleted;
  ConcretizeMemLoc proofs re-established without cheats.
- [ ] The witnesses above MATCH (except the residuals owned by #549, #556, #558, #560, #566); p39, p40 return 5 on both sides.
- [ ] Whitelist conjuncts relaxed: `supported_internal_stmts_shape` and the internal-body
  `~supported_stmts_expr_exists expr_internal_call_root` in `supported_function_body`, and the `For`-body
  `expr_internal_call_root` conjunct in `supported_stmt` (the internal-call ones only together with #546's a05-05).
- [ ] Parity fixtures added: p74, p76, p92, p106 (inside today's whitelist), p39, p40 (behavioural), p01, p03, p04,
  p06, p09, p10, p41, p21, `ctl_local_internal`, `nm_local_return_buf` (from #557; next to its
  `lowering/defs/bytecode/name-collisions/` fixtures) (p57 once #558 lands).

<!-- parts: a05-01, a05-02, a05-08, a05-03 -->



## Issue comments

## Witness sources (continued)

Sources of the witnesses named in #545 that do not fit in the issue body.

`p39_int_local_clobber`:
```vyper
# internal local (fixed MemLoc in HOL) vs caller local live across the call
x: uint256

@internal
def bar(y: uint256):
    z: uint256 = y + 1
    self.x = z

@external
def foo(x: uint256) -> uint256:
    a: uint256 = x
    self.bar(x)
    return a
```

`p02_int_local_string`:
```vyper
# internal function with a String local (AnnAssign of non-word type)
@internal
def bar(s: String[10]) -> String[10]:
    t: String[10] = s
    return t

@external
def foo(s: String[10]) -> String[10]:
    return self.bar(s)
```

`p58_int_bytes_local`:
```vyper
# internal with a Bytes local built by concat
@internal
def f(b: Bytes[4]) -> Bytes[8]:
    c: Bytes[8] = concat(b, b)
    return c

@external
def foo(b: Bytes[4]) -> Bytes[8]:
    return self.f(b)
```

`p74_int_ext_call`:
```vyper
# internal function performing an external staticcall
interface I:
    def bar(x: uint256) -> uint256: view

@internal
@view
def f(t: address, y: uint256) -> uint256:
    return staticcall I(t).bar(y)

@external
@view
def foo(t: address, x: uint256) -> uint256:
    return self.f(t, x)
```

`x02_extcall_internal`:
```vyper
# extcall inside an internal function
interface Peer:
    def get() -> uint256: nonpayable

@internal
def g(t: address) -> uint256:
    return extcall Peer(t).get()

@external
def f(t: address) -> uint256:
    return self.g(t)
```

`ctl04_internal_extcall`:
```vyper
# control (no a08 builtin): external call inside an internal function (revert-bubbling block in internal fn)
interface I:
    def f(x: uint256) -> uint256: nonpayable
@internal
def h(t: address, x: uint256) -> uint256:
    return extcall I(t).f(x)
@external
def foo(t: address, x: uint256) -> uint256:
    return self.h(t, x)
```

`p92_int_revert_branch`:
```vyper
# internal function with a terminating revert branch (no strings) and stack params live at the branch
@internal
def f(y: uint256, z: uint256) -> uint256:
    if y == 3:
        raise
    return y + z

@external
def foo(x: uint256) -> uint256:
    return self.f(x, 1)
```

`p21_for_body_call`:
```vyper
# internal call inside a For body of an external function
@internal
def f(y: uint256) -> uint256:
    return y + 1

@external
def foo() -> uint256:
    s: uint256 = 0
    for i: uint256 in range(3):
        s = self.f(s)
    return s
```

`p05_int_local_dynarray`:
```vyper
# internal function with a DynArray local
@internal
def bar(y: uint256) -> uint256:
    a: DynArray[uint256, 3] = [y]
    a.append(y + 1)
    return len(a)

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
```

`p43b_int_local_word_types2`:
```vyper
# internal function with locals of several word types (no keccak)
@internal
def f(y: uint256) -> bool:
    a: int128 = -1
    b: address = msg.sender
    c: bytes4 = 0x01020304
    d: bool = y > 1
    return d and a < 0 and b != empty(address) and c != empty(bytes4)

@external
def foo(x: uint256) -> bool:
    return self.f(x)
```

`rc23_internal_fn`:
```vyper
# raw_call with outsize inside an internal function
@internal
def h(t: address) -> Bytes[32]:
    return raw_call(t, b"\x01", max_outsize=32)
@external
def foo(t: address) -> Bytes[32]:
    return self.h(t)
```

`rc27_internal_fn_nolit`:
```vyper
# raw_call with outsize inside an internal function (argument data)
@internal
def h(t: address, d: Bytes[8]) -> Bytes[32]:
    return raw_call(t, d, max_outsize=32)
@external
def foo(t: address, d: Bytes[8]) -> Bytes[32]:
    return self.h(t, d)
```

`rc28_internal_fn_noret`:
```vyper
# raw_call (no outsize) inside an internal function, internal returns uint256
@internal
def h(t: address, d: Bytes[8]) -> uint256:
    raw_call(t, d)
    return 1
@external
def foo(t: address, d: Bytes[8]) -> uint256:
    return self.h(t, d)
```

`nm_local_return_buf`:
```vyper
# local named __return_buf__ inside an internal function
@internal
def g() -> uint256:
    __return_buf__: uint256 = 3
    return __return_buf__

@external
def f() -> uint256:
    return self.g()
```

`ctl_local_internal`:
```vyper
# control for nm_local_return_buf: same shape with local named y
@internal
def g() -> uint256:
    y: uint256 = 3
    return y

@external
def f() -> uint256:
    return self.g()
```

`p40_int_for_clobber`:
```vyper
# internal For loop variable (fixed MemLoc in HOL) vs caller local live across the call
x: uint256

@internal
def bar(y: uint256):
    for i: uint256 in range(2):
        self.x += i + y

@external
def foo(x: uint256) -> uint256:
    a: uint256 = x
    self.bar(x)
    return a
```

`p01_int_local_word`:
```vyper
# internal function with a word-typed local (AnnAssign)
@internal
def bar(y: uint256) -> uint256:
    z: uint256 = y + 1
    return z

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
```

`p06_int_for_range`:
```vyper
# internal function with a range For loop (no AnnAssign)
x: uint256

@internal
def bar():
    for i: uint256 in range(3):
        self.x += i

@external
def foo() -> uint256:
    self.bar()
    return self.x
```

`p07_int_for_array`:
```vyper
# internal function iterating over an array argument
x: uint256

@internal
def bar(a: uint256[3]):
    for v: uint256 in a:
        self.x += v

@external
def foo(a: uint256[3]) -> uint256:
    self.bar(a)
    return self.x
```

`p08_int_for_local`:
```vyper
# internal function with an accumulator local and a For loop
@internal
def bar(n: uint256) -> uint256:
    s: uint256 = 0
    for i: uint256 in range(n, bound=10):
        s += i
    return s

@external
def foo(n: uint256) -> uint256:
    return self.bar(n)
```

`p42_int_for_dynarray_arg`:
```vyper
# internal function iterating over a DynArray argument
x: uint256

@internal
def bar(a: DynArray[uint256, 3]):
    for v: uint256 in a:
        self.x += v

@external
def foo(a: DynArray[uint256, 3]) -> uint256:
    self.bar(a)
    return self.x
```

`p36_int_for_return`:
```vyper
# internal function returning from inside a For loop
@internal
def f(n: uint256) -> uint256:
    for i: uint256 in range(10):
        if i == n:
            return i
    return 99

@external
def foo(n: uint256) -> uint256:
    return self.f(n)
```

`p67_int_local_int128`:
```vyper
# internal function with a single int128 local (narrowing p43b)
@internal
def f(y: uint256) -> bool:
    a: int128 = -1
    return a < 0

@external
def foo(x: uint256) -> bool:
    return self.f(x)
```

`p68_int_local_bytes4`:
```vyper
# internal function with a single bytes4 local (narrowing p43b)
@internal
def f(y: uint256) -> bool:
    c: bytes4 = 0x01020304
    return c != empty(bytes4)

@external
def foo(x: uint256) -> bool:
    return self.f(x)
```

`p03_int_local_array`:
```vyper
# internal function with a fixed-array local
@internal
def bar(y: uint256) -> uint256:
    a: uint256[3] = [y, y + 1, y + 2]
    return a[1]

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
```

`p04_int_local_struct`:
```vyper
# internal function with a struct local
struct P:
    a: uint256
    b: uint256

@internal
def bar(y: uint256) -> uint256:
    p: P = P(a=y, b=2)
    return p.b + p.a

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
```

`p57_int_struct_local_return`:
```vyper
# internal returning a struct built in a local
struct P:
    a: uint256
    b: uint256

@internal
def f(y: uint256) -> P:
    p: P = P(a=y, b=y)
    p.b = 7
    return p

@external
def foo(x: uint256) -> uint256:
    return self.f(x).b
```

`p76_int_assert_raise`:
```vyper
# internal function containing assert and raise
@internal
def f(y: uint256) -> uint256:
    assert y != 3, "three"
    if y == 4:
        raise "four"
    return y

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
```

`p09_int_chain`:
```vyper
# internal -> internal call chain
@internal
def g(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    return self.g(y)

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
```

`p10_int_diamond`:
```vyper
# diamond: two internals both calling a shared internal
@internal
def h(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    return self.h(y)

@internal
def g(y: uint256) -> uint256:
    return self.h(y)

@external
def foo(x: uint256) -> uint256:
    a: uint256 = self.f(x)
    return self.g(a)
```

`p11_int_deep`:
```vyper
# deep internal call chain (4 levels)
@internal
def d(y: uint256) -> uint256:
    return y + 4

@internal
def c(y: uint256) -> uint256:
    return self.d(y)

@internal
def b(y: uint256) -> uint256:
    return self.c(y)

@internal
def a(y: uint256) -> uint256:
    return self.b(y)

@external
def foo(x: uint256) -> uint256:
    return self.a(x)
```

`p41_int_local_and_call`:
```vyper
# internal function with a local initialised from another internal call
@internal
def g(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    z: uint256 = self.g(y)
    return z * 2

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
```

`p62_for_body_call_clobber`:
```vyper
# For-body internal call whose callee frame overlaps the loop counter in HOL
@internal
def f(y: uint256) -> uint256:
    return y + 1

@external
def foo() -> uint256:
    s: uint256 = 100
    for i: uint256 in range(3):
        s = self.f(s)
    return s
```

`p45_for_body_call_loopvar`:
```vyper
# external For body calling internal with loop variable, result to storage
x: uint256

@internal
def f(y: uint256) -> uint256:
    return y * y

@external
def foo() -> uint256:
    for i: uint256 in range(4):
        self.x += self.f(i)
    return self.x
```

`p47_len_of_string_call`:
```vyper
# internal String return used inside a builtin (len)
@internal
def f(s: String[10]) -> String[10]:
    return s

@external
def foo(s: String[10]) -> uint256:
    return len(self.f(s))
```

`p51_augassign_call`:
```vyper
# internal call as AugAssign value (storage and local)
x: uint256

@internal
def f(y: uint256) -> uint256:
    return y + 1

@external
def foo(y: uint256) -> uint256:
    s: uint256 = 1
    s += self.f(y)
    self.x += self.f(s)
    return self.x
```

`c07_annassign_str_same_len`:
```vyper
# a11: String local initialised from a String argument of the same type
@external
def f(s: String[10]) -> String[10]:
    t: String[10] = s
    return t
```

`p44_int_for_calls_int`:
```vyper
# internal function with a For loop whose body calls another internal function
x: uint256

@internal
def g(y: uint256):
    self.x += y

@internal
def f():
    for i: uint256 in range(3):
        self.g(i)

@external
def foo() -> uint256:
    self.f()
    return self.x
```

`p60_int_view_reads_and_local`:
```vyper
# view internal with a local reading storage, called twice
x: uint256

@internal
@view
def f(y: uint256) -> uint256:
    t: uint256 = self.x
    return t + y

@external
def foo(y: uint256) -> uint256:
    self.x = y
    a: uint256 = self.f(1)
    b: uint256 = self.f(a)
    return b
```

`ctl05_internal_raise`:
```vyper
# a14 (from a08): internal function with a halting revert block; extra POPs (owned by a05-08)
@internal
def h(x: uint256) -> uint256:
    if x == 0:
        raise
    return x
@external
def foo(x: uint256) -> uint256:
    return self.h(x)
```

