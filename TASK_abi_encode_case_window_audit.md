# Whole-builtin window applicability audit

Scope: C1.7.2. This is a premise ledger, not a certificate that the expression case or a whole-builtin execution theorem has been proved.

## Candidate boundary

The desired consumer boundary is the following implication schema (not a new assumption on the frozen theorem):

```
lower_abi_encode ensure mid src ei maxlen st = (out,final) /\
  [the actual operand endpoint: stmt_state_rel, expr_val_rel,
   expr_val_at, typing/plan/layout facts, compiler invariants and freshness]
==>
?bytes Q.
  evaluate_type_builtin cx (AbiEncode ensure source_mid) tuple_ty arg_tys vals
    = INL (BytesV bytes) /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
  (!fn'. fn_has_code st final fn' /\ fn_inst_ids_distinct fn' /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP ==>
          MEM i (fn_insts func)) /\
     (st.cs_blocks = final.cs_blocks \/
      !bb. lookup_block final.cs_current_bb fn'.fn_blocks = SOME bb ==>
           phi_prefix_length bb.bb_instructions = 0) ==>
     ?t. Q t /\ ~t.vs_halted /\
       t.vs_current_bb = final.cs_current_bb /\
       t.vs_inst_idx = LENGTH final.cs_current_insts /\
       abi_decode_sim ctx fn' initial t)
```

Here Q must expose the output operand, length word, payload bytes, allocations/growth, old variables, locals and world preservation sufficient to reconstruct `vv_post` relative to the *original* func. It must NOT include `abi_decode_sim` or resource facts indexed by fn'. This schema deliberately records the still-missing boundary; it is not an SML theorem declaration or an admission. The actual endpoint hypotheses must be instantiated separately in each compiler branch; they have not yet been compressed into a validated common predicate.

## Producer ledger

Common code decomposition: `lower_abi_encode_trace` gives setup, recursive body and finish; `lower_abi_encode_extends` gives compiler extension. `abi_builtin_encode_setup_shape` and `abi_builtin_encode_finish_shape` give phase counters and positions. These are shape facts, not ownership proofs.

| Requirement | Producer / remaining obligation |
|---|---|
| Admissible ei | Requires compiler plan -> admissibility using the source plan/layout interface. Not supplied by stmt_state_rel alone. |
| Window input at the operand endpoint | Memory: `abi_encoder_source_footprint_rep` yields encoding-equivalent ct/rv and open input at `val_footprint tv v`; `abi_encoder_open_input_window` converts it. No declared-capacity inference is needed or permitted. Word: explicit staging MSTORE of its 32-byte source; source representative/word encoding theorem needed. Tuple: per-argument suppliers and open tuple staging/assembly, not merely LIST_REL. |
| Source pointer/live variables | `expr_val_rel` yields the pointer; compiler operand liveness and counter monotonicity must preserve it through setup. Setup supplies the new destination operand and its evaluation. |
| fn_has_code and distinct IDs | Compiler hypotheses and phase subfragment restriction. Available for original func and bridge fn'. |
| alloca_inv and room before setup | Direct from `stmt_state_rel_def`; also from stmt_state_rel conjunct in `abi_args_post`. |
| Setup allocation row and exact size | `stmt_state_rel_def` ties reused ALLOCA rows to their literal size; compiler trace must identify the setup site. Fresh allocation uses frontier. `alloca_site_execute` is the resource-level candidate. |
| Setup resource transport | `abi_window_setup_room` / `abi_window_setup_alloca_inv` only equate the endpoint to `abi_builtin_allocate_state`. They do not establish resources of that allocated state. A small allocation-state bridge is still needed. |
| Source below frontier | `abi_encode_owned_footprint_frontier` for memory, `abi_encode_argument_footprint_frontier` for Args: conclusion is **zero footprint OR bounded**. Cannot erase the zero alternative. Word/tuple staged allocation row plus `alloca_site_registered_below` bounds the staged buffer. |
| Destination below frontier | New/reused setup allocation row, encoded length <= maxlen, rounding (`abi_builtin_word_size_capacity` etc.). Include logical selector offset 0/4. |
| Source/destination separation | For fresh source/staging rows, interval containment plus `alloca_site_registered_disjoint`. Memory local source needs local-region exclusion against later IDs; expr_val_at alone is not a universal separation statement. Zero windows need an explicit special route: window pre asks sb+cap <= frontier even if cap=0. |
| Reused body scratch | `stmt_state_rel_def` + actual body ALLOCA shape gives sz=32. Pairwise row disjointness protects staged source and setup destination. Local sources additionally need local-region/ALLOCA ID exclusion. Actual sites only: no full instruction-interval charge. |
| Method-id store | Physical write is 32 bytes at p+32; logical prefix is 4 bytes. Source must survive the physical window, not just the four logical bytes. `abi_window_builtin_setup_observed` supplies method bytes and world fields but requires full `abi_encoder_input`, not window input. Memory footprint producer gives only open/window input; need setup preservation directly for window input using its frame and memory agreement. |
| Body execution | `compile_abi_encode_to_buf_window_strong_run`, already checked in task-owned wrapper. It requires **alloca_room ctx executing_func**. See decisive uniformity issue below. |
| Method bytes survive body | `abi_encoder_window_effect_bytes` plus actual-site effect and disjointness of the method bytes from body output and all final scratch rows. Output starts at p+36 for SOME; source/destination disjointness alone does not discharge scratch exclusion of [p+32,p+36). Use setup parent row, sizes and alloca_inv at body endpoint. |
| Finish | `abi_window_builtin_finish` keeps the concatenated bytes, adds header store and composes body registered effects. It requires bytes already assembled at p+32, buf liveness and p<dimword. Its registered effect is relative to the *post-setup* initial state: setup effect still needs composition. |
| Final statement relation/vv_post | Need old allocation preservation, fmp_room/immutable/local/world fields and output placement under original func. Strong result gives room/invariant, registered effect, growth and labels; observed setup gives world fields. Finish does not by itself expose every world field. A no-world-change/observer endpoint theorem is still necessary. |

## Actual prefix branches

1. **Singleton word (~ensure):** `compile_abi_encode_word_trace` isolates lower_value, 32-byte allocation, MSTORE and suffix. expr_vv simulation provides word value, stmt_state_rel and frame; its expr_val_at is vacuous for words. Thus the 32-byte source window must be established by staging execution, not by expr_val_at. The staging allocation and setup allocation are distinct sites even on reentry.
2. **Singleton memory (~ensure):** `compile_abi_encode_memory_trace` isolates compile_expr/unwrap and suffix. expr_post supplies value/location and frame. `abi_encoder_source_footprint_rep` handles noncanonical representative types and actual footprints. There are allocated, local and zero-footprint location alternatives; each needs separate ownership handling for reused setup/body rows. In particular `abi_window_setup_input` is not applicable directly (its premise is full input).
3. **Tuple (all other cases):** `compile_abi_encode_tuple_trace` isolates Args, tuple allocation and stores. Frozen `abi_args_post_def` supplies statement relation, per-op value/location and wb_frame. `abi_encode_argument_footprint_frontier` extracts the same zero-or-bounded disjunction. It does NOT directly produce tuple input, simultaneous row exclusions, or staging execution. Existing open-input tuple preparation/assembly is the candidate, with overlap premises to be discharged from the per-argument ownership alternatives. Empty args/zero-size tuples must not assume a positive source allocation.

## Decisive bridge uniformity gap

`abi_decode_sim_gas_path` quantifies over fn' with code/distinctness, non-STOP instruction inclusion and end-PHI conditions. It does **not** give `lookup_function fn'.fn_name ctx.ctx_functions = SOME fn'`.

But `alloca_room ctx fn' s`, required by the window precondition, includes exactly that equality (`exprLoweringPropsScript.sml:245-253`). Task-owned checked theorem `abi_encode_window_room_function` proves:

```
alloca_room ctx func s /\ alloca_room ctx other t /\
other.fn_name = func.fn_name ==> other = func
```

Consequently room for the original function cannot simply be transported to a STOP-modified, same-name bridge function. Non-STOP instruction inclusion may transport pending allocation sizes/inequalities, but cannot establish lookup equality. No assumption in `abi_args_post` or singleton expr_post fixes this; adding lookup equality to the frozen bridge is forbidden. This is an incompatibility of the selected window theorem with the bridge's uniform execution premise, **not evidence that the frozen bridge or Args theorem is false/insufficient for the task in general**.

Missing exact resource claim one must NOT silently assume:

```
alloca_room ctx func s /\
[fn' code, distinctness, non-STOP inclusion as in bridge]
==> alloca_room ctx fn' s
```

A viable route needs an execution interface under allocation-size credit without exact ctx-function registration, or a justified conversion that keeps resource accounting indexed by original func while executing fn'. Merely wrapping the existing window theorem does not provide this. Changing ctx also changes the resulting abi_decode_sim and requires an independently proved context-independence argument; it is not a tactical substitution.

## Consequences / stop point

Return-data stability of output observations is already checked by `abi_encode_output_returndata`; the new window frame/growth/resource-observation closure must be checked separately. Uniformity fails before that closure is useful. Do not invest in the branch proofs until strategist reviews this ledger.

Old scratch-dependent future consumers C1.2-C1.5 need a route update; the already checked Interface effect lemma can stay but does not discharge window resource premises. No frozen statement, Args export, GasBridge export, overlay, or production definition has changed. No counterexample to `compile_abi_encode_case` has been established.

## C1.7.4: registered observer route probe and remaining ledger

Checked in `exprSimAbiEncodeObserver`:
- `abi_encode_alloc_observer fn n` replaces the function blocks by a single `entry` block containing ALLOCA id 0 with literal n and output `out`, then STOP id 1.
- `abi_encode_observer_context ctx fn n` replaces only ctx_functions by that singleton, preserving all other context fields.
- `abi_encode_alloc_observer_no_calls` and `_no_reach` establish the empty direct-call/reachability relations. `_room` derives actual registered room from the pending literal-size bound, not from registration alone.
- `abi_encode_alloc_observer_prefix` uses `alloca_site_execute`, constructs the observer step and cut reflexivity, and transports the prefix to arbitrary original_ctx using C1.7.3. The existing-row premise is `!b sz. FLOOKUP s.vs_allocas 0 = SOME (b,sz) ==> sz = w2n n`; it covers both fresh and reused rows without assuming freshness. The result includes output value, exact row, and alloca_inv. The cut is (entry,1), immediately before STOP. No general encoder observer is claimed.

General-route ledger:

1. **Observer construction (missing).** Need a task-owned construction from `lower_abi_encode ... st = (out,final)` giving an observer function obs, cut `(final.cs_current_bb,LENGTH final.cs_current_insts)`, and region R. Exact desired outputs: `fn_has_code st final obs`, `fn_inst_ids_distinct obs`, `region_code_agrees obs fn' cut R` for every bridge fn', `observer_region_safe obs cut R`, `observer_region_closed synthetic_ctx obs cut R`, and initial control membership in R. `abiEncoderObserver` supplies same-block and jump/PHI examples and generic extraction/transfer consumers, not this construction for arbitrary nested encoder blocks. The observer must exclude old prefix code and external suffix INVOKEs, while preserving PHI prefixes needed for entry.

2. **Use the region-safe extraction theorem, not the older global observer_closed.** `observer_closed` demands preservation of nonhaltedness even on initially halted states; an ordinary allocation/update preserves haltedness and therefore does not satisfy that condition. `observer_region_safe` restricts its safety clauses to nonhalted states. Exact consumer: `observer_region_run_prefix` requires region safety, region closure, initial region membership, ~halted and `run_from fuel synthetic_ctx obs s = Halt h`; it concludes a prefix to u and `stop_view u = h`. `abi_decode_sim_stop_run` supplies such a terminating run from a window endpoint at a literal STOP. `observer_region_run_prefix_transfer` additionally handles region agreement with the target embedding. Context transport is now checked separately.

3. **Initial observer credit (missing general lemma).** Need `pending_alloca_size obs s <= pending_alloca_size original_func s` plus singleton no-call registration to derive room for obs from original room. Mere instruction-set inclusion does not control SUM multiplicity. Distinct IDs plus an injection/sublist of actual ALLOCA instructions is the proposed producer. The exact comparison is on FILTER of unallocated ALLOCA instructions, then SUM/MAP alloca_lit_size (`pending_alloca_size_def`). This must be established from actual code shape, not assumed for arbitrary fn'.

4. **Recover original room after execution (missing general lemma).** Synthetic room at t does not imply original room at t. Required conclusion is `alloca_room original_ctx original_func t` from original room at s and the actual observer prefix whose ALLOCAs are instructions of original_func with correct reused sizes. A prefix induction can use `alloca_site_execute`/`alloca_room_fresh`, allocation-field preservation for other opcodes and `fmp_room_exec_alloca` for the original fmp charge. Strong window result's `window_alloca_growth` has only a lower bound on frontier growth; registered_effect constrains rows and memory but gives no upper frontier charge. Those endpoint facts alone are not a replacement for this preservation argument. This is an explicit new dependency, not a consequence claimed in this audit.

5. **Stop observations (partly available, still incomplete).** `stop_view_fields` preserves memory, vars, allocas, frontier, world and labels; `stop_view_operand` preserves operand evaluations. It hides haltedness and returndata by design. The displayed list does NOT expose vs_fmp, vs_call_ctx, vs_data_section, vs_prev_bb or vs_immutables; consumers needing these require direct stop_view field projections or preservation along the prefix. Do not insert execution relations into Q; Q must remain returndata-insensitive. `window_strong_result` exposes labels, actual-site effects and growth, while registered_effect already exposes accounts/transient/logs/requests/deletions. Full original `stmt_state_rel`/vv_post reconstruction remains a separate boundary proof.

The small probe validates synthetic registration -> explicit allocation prefix -> context transport. It does not validate the general nested encoder observer, multiplicity-controlled initial credit, or original resource recovery. The earlier source-window/zero-footprint/reused-row/physical-selector-write obligations remain unchanged. Stop here for route review before whole-suffix or branch work.
