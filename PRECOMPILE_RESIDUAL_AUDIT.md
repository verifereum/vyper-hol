# Residual continuation audit (C1.3.0)

This is a review artifact, NOT a proved theory, admitted skeleton, or change to
any theorem statement. Candidate contracts below require strategist approval.
Current checked baseline: `bodyPtrPrecompileBuiltinsOperandComposeTheory` and
`bodyPtrPrecompileBuiltinsCasesTheory` build (TO_precompile-20261106T071746Z_m0182_t001).

## 1. Proposed common value-level continuation contract

One contract covers all three cases, avoiding three copies of the frame. Its
three specializations are bt=ECRecover, xs=[h;v;r;sig]; bt=ECAdd,
xs=[p1;p2]; bt=ECMul, xs=[p;scalar]. The compiler disjunction fixes the residual
compiler in each specialization. It is deliberately value-level, not the
Value-wrapped `ec_source_tail` level. All free parameters are quantified.

```sml
!d ctx PG func cenv cx env ty ann bt args xs vs
 es sa s0 G0 tn0 gs ee sf t G tn op sb.
 (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
 expr_body_pre cenv cx env (Builtin ann bt args) es /\
 expr_sim_inv cenv cx env ee /\
 eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
 LENGTH args = LENGTH vs /\ LENGTH xs = LENGTH args /\
 ((bt = ECRecover /\ LENGTH xs = 4 /\
   compile_ecrecover (EL 0 xs) (EL 1 xs) (EL 2 xs) (EL 3 xs) sf = (op,sb)) \/
  (bt = ECAdd /\ LENGTH xs = 2 /\
   compile_ecadd_points (EL 0 xs) (EL 1 xs) sf = (op,sb)) \/
  (bt = ECMul /\ LENGTH xs = 2 /\
   compile_ecmul_point (EL 0 xs) (EL 1 xs) sf = (op,sb))) /\
 stmt_state_rel ctx func cenv cx es s0 /\
 stmt_state_rel ctx func cenv cx ee t /\
 wb_frame cenv es sa s0 t /\
 sa.cs_next_var <= sf.cs_next_var /\ sa.cs_next_id <= sf.cs_next_id /\
 fn_has_code sf sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
 ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 ghost_inv d cenv cx ee G tn t /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 LIST_REL (\ev x.
   expr_val_rel cx (expr_type (FST ev)) (SND ev) x t /\
   expr_val_at cenv cx (expr_type (FST ev)) sa sf ee (SND ev) x t /\
   ptr_val_ok cx (expr_type (FST ev)) (SND ev) x G tn t /\
   (~is_word_type (expr_type (FST ev)) ==> ptr_buf_ok cenv (FST ev) x G t) /\
   (!z. x = Var z ==> not_fresh_at sf z) /\ (!l. x <> Label l))
   (ZIP (args,vs)) xs /\
 ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
 t.vs_inst_idx = LENGTH sf.cs_current_insts ==>
 gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (\st. case exprSimWordArgs$builtin_result cx st.accounts ann bt
                  (MAP expr_type args) vs of
      INR ex => (INR ex,st)
    | INL v => (do precompile_call_success bt; return v od) st)
   (ee,t,G,tn)
   (\res ff H tau u. ?v. res = INL v /\
     expr_post ctx func cenv cx (Builtin ann bt args)
       es sa sb s0 ff v op u /\
     u.vs_current_bb = sb.cs_current_bb /\
     u.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv d cenv cx ff H tau u /\
     ptr_val_ok cx (expr_type (Builtin ann bt args)) v op H tau u /\
     (~is_word_type (expr_type (Builtin ann bt args)) ==>
       ptr_buf_ok cenv (Builtin ann bt args) op H u) /\
     ghost_kept cenv es sa G0 tn0 s0 H tau)
   (\res ff ghosts r. expr_exit res r)
```

This is an interface proposal, not a claim that list post transport is already
proved. In particular the LIST_REL premise must be produced by operand
composition, not passed as a new hypothesis to the frozen target. The unused
`ty` can be removed on approval. Check compiler/result-type compatibility in
integration: recovery returns a StackValue, arithmetic a LocatedValue; their
lower_value/unwrap bridge must be used, not an assumed universal stack bridge.

## 2. Source boundary still missing

The following exact candidate equation avoids mixing value and value-or-place:

```sml
!cx ann bt args.
 (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
 builtin_args_length_ok bt (LENGTH args) ==>
 bind (eval_expr cx (Builtin ann bt args)) (read_result cx) =
 bind (eval_exprs cx args)
   (\vs st. case exprSimWordArgs$builtin_result cx st.accounts ann bt
                   (MAP expr_type args) vs of
      INR ex => (INR ex,st)
    | INL v => (do precompile_call_success bt; return v od) st)
```

Recovery's matching equation exists only as local
`exprSimPrecompiles.eval_expr_ecrecover_read_action` (source 1592-1598).
Arithmetic `ec_source_tail` (exprSimECArith 776-782) returns `Value v`, NOT v.
A source equation must either prove the equation above or compose its tail
with `read_result cx`. It is not valid to insert ec_source_tail unchanged
into a value continuation. Source error cases are INR builtin_result and
failed/missing precompile outcomes; operand exceptions bypass the residual.
No source exception is allowed to disappear under a normal-only trace.

## 3. Premise/provider inventory

Signatures are pinned to the following checked source reads. A provider listed
as partial is NOT a missing-premise discharge. Sizes are input/output:
recovery 128/32 (+ zero store); ECAdd 128/64; ECMul 96/64.

| Required premise | Exact provider/interface and remaining work |
|---|---|
| Residual compiler allocation/store/suffix equations | `bodyPtrPrecompileBuiltinsCompilerStages` contains compiler shape lemmas; CompletePrefixes 24-53 gives ECMul equations literally. Obtain stage witnesses by unfolding only the residual compiler and using these equations. This is implementation-level work inside the residual boundary. |
| Allocation instructions are members of fn_insts | `fn_has_code sf sb func` plus stage extensions and emitted-list membership. Do not require this again from body theorem. The two MEM premises of `ecmul_complete_prefix_checked` are lines 40-43; allocation site id and fresh output name must match exactly. |
| Three normal prefix runs and intermediate stmt_state_rel | `allocated_payload_run_witnesses` (RunWitnesses 5-76) takes the two allocation equations, emitted concatenation, membership/freshness, and a payload callback, and returns the full run plus individual runs and relations. `recovery_payload_run` (PayloadCallbacks 10-28) gives the 4 MSTORE payload run and exact bytes. Arithmetic callbacks in that same theory supply the corresponding two point copies / point+scalar payload. These are conditional run witnesses, not counted paths by themselves. |
| Allocation bounds and scratch separation | RunWitnesses concludes `w2n pi+insz < dimword(:256)`, `w2n po+outsz < dimword(:256)`, output/input regions_disjoint, and output/local and old-allocation disjointness (40-68). `emitted_allocation_spatial_frame` (PrefixFrames 179ff) supplies local spatial separation. `local_region_allocation_growth_disjoint` (166-170) gives DISJOINT local interval/new_site_bytes for a single ALLOCA. Operand point versus new-site separation still needs threading from expr_val_at's local/old-allocation alternatives through the first allocation. |
| Point coverage at final operand state | `ec_point_covers_kept` (Operands 71-78): expr_post, point expr_type, earlier ptr_val_ok, ghost_kept, old Var, and eval preservation imply `?p. x=Var p /\ ptr_covers G tn p u 64`. |
| Point cleanliness at final operand state | `ec_point_clean_kept` (Operands 44-53): additionally expr_sim_inv and value_has_type, and eval preservation imply all 64 bytes NOTIN tn.t_mem. Coverage alone does NOT imply this. |
| Scalar taint AND provenance | `word_ptr_val_ok_kept` (Operands 33-37) transports full ptr_val_ok from word type, earlier ptr_val_ok, ghost_kept and stale Var. `typed_args_post_ptr` (external typedWordArgsPostPtr 8-13) only stores EVERY op_taint={} and is NOT sufficient for the new word op_prov=NONE condition by itself. |
| Complete checked prefix | `ecmul_complete_prefix_checked` 24-74 consumes equations, runs, stmt relations, membership, point bounds/cleanliness/disjointness, scalar evaluation/taint/nonlabel/staleness; returns all-index inst_seq_ptr, input/output ptr_covers, clean input, exact memory-taint formula, exterior memory and old-variable preservation. `ecadd_complete_prefix_checked` and `recovery_complete_prefix_checked` are the corresponding interfaces in the same owned file. Recovery additionally zeroes output, so empty return bytes are safe. These are NOT body-level frame lemmas. |
| Count prefix | Use run_inst_seq_gas_path_ptr with complete-prefix inst_seq_ptr and compiler emitted membership/prefix equations. Fixed-run frag_exec_ptr or an erased S1 path is not a substitute. |
| Computed call checked + counted | `computed_emitted_suffix_paths` (SuffixPaths 57-86): compiler suffix, stale src/dst, evaluations, computed_precompile request, coverage of input/output, clean input, allocas_from, no dalloca, storage/transient dead-set inclusion, nonhalted and instruction-prefix => step witnesses, exact G'/tn' and normal/revert counted paths. Normal specialized provider `computed_suffix_success_path` (115-130) additionally requires SOME(SOME data), successful oracle head, and inst_seq_ptr. Failure `computed_suffix_failure_path` (142-156) requires SOME NONE. Oracle failure `computed_suffix_oracle_failure_path` (165-179) requires computed_precompile and empty or unsuccessful outcome head. All branches remain necessary. |
| Original local ghost invariant at end of prefix | `complete_prefix_ghost_frame` (PrefixFrames 112-133): ghost_inv + represented pointer/provenance/lookup preservation + scoped value footprint exterior to alloc1 UNION alloc2 UNION writes1 UNION writes2 + exterior memory + exact taint formula + storage/transient/imm and call/accounts/transient preservation => ghost_inv. `scoped_prefix_footprint_exterior` 140-151 supplies footprint from local_ptrs_rel and local disjointness. Must establish imm preservation too; CompletePrefixes' abbreviated output is not enough by name alone. |
| Ghost after call / composition | `suffix_ghost_kept` (SuffixGhost 171-177) requires fresh GAS and call outputs, exact step_prov/step_taint and tn2.t_mem SUBSET tn.t_mem. `ghost_kept_subset_trans` and `ghost_inv_exterior_frame` are shared frame boundaries in that theory; they still need the actual scratch exterior and memory change equations. |
| Arithmetic entire output clean | `returned_prefix_clean` (SuffixGhost 183-187) requires exact difference by returned prefix AND clean untouched suffix. For a successful EC arithmetic call, establish full 64-byte result, not just output coverage. For recovery with zero returned bytes, use the initialized clean 32 bytes instead. |
| Recovery final MLOAD | CompilerStages `computed_load_suffix_compiler_shape` exposes it. Existing suffix path ends after ASSERT; it does not count this MLOAD. Need a counted checked MLOAD boundary proving op_prov=NONE, op_taint={}, preserving ghost_inv and original ghost_kept. No matching body-level residual or complete recovery-load theorem found in prefixed source. |
| Value and original S1 post | S1 `ec_points_path` (reference 1974-2023) gives only an ordinary gas_marked_path and vv_post for Value-wrapped tail. `ecrecover_success_path` (current source 1603-1623) gives ordinary path + expr_post with AddressV and oracle tail. They can supply semantic witnesses, never pointer safety by erasure. Need to align the SAME run with pointer path, use deterministic run/step equations, and supply the value-level arithmetic read bridge. |

Source reads supporting table: m0184 (S1 ec_points_path), m0185 (recovery consumer),
m0187 (operand ghost/coverage/cleanliness), m0189 (exact judgment post), m0190
(ECMul complete prefix), m0193-94 (source tails and recovery equation/path),
m0195 (all suffix path signatures), m0196 (prefix frame), m0198-99 (typed list
posts), m0201-02 (run witness/callback), m0205-06 (suffix frame/zeroing).
All are TO_precompile-20261106T071746Z_ prefixed tool output IDs.

## 4. Exact small missing boundary proposal: clean recovery load

This candidate factors pointer checking and counting, not source result decoding.
It intentionally uses the existing primitive instruction vocabulary.

```sml
!D lo ctx fn PG G tn s t x y id bb.
 step_inst_base (mk_inst id MLOAD [Var x] [y]) s = OK t /\
 ptr_covers G tn x s 32 /\
 (!w. lookup_var x s = SOME w ==>
   !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
 ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 isPREFIX [mk_inst id MLOAD [Var x] [y]]
   (DROP s.vs_inst_idx bb.bb_instructions) ==>
 ?H tau.
 gas_path_ptr D lo ctx fn PG G tn s 0 H tau
   (OK (t with vs_inst_idx := s.vs_inst_idx+1)) /\
 op_prov H (Var y) = NONE /\ op_taint tau (Var y) = {}
```

The count is `0`: `straight_line_ptr_edge` (fragGasSeqPtr 53-63,
TO_precompile-20261106T071746Z_m0208_t001) counts 1 only for GAS, and
MLOAD is not GAS. The GAS/STATICCALL/ASSERT three-step suffix counts 1.
Search before adding: per-instruction MLOAD facts already exist in toolkit;
prefer applying them plus run_inst_seq_gas_path_ptr rather than adding this
convenience theorem if the combined use is short. Frame transport is separate.

## 5. Downstream bind use and both certificate premises

For each operand use
`source = bind (eval_expr cx e) (read_result cx)` and
`next = (\v. bind (remaining forced operands) (residual v))` in
`pointer_outcome_bind_success` (OperandCompose 28-49). Its Q is precisely the
normal lambda in section 1, R is `\res ee gt r. expr_exit res r`.
The normal operand P must include `res=INL v`, expr_post, current PC,
ghost_inv, ptr_val_ok, ptr_buf_ok for nonword, and ghost_kept. Derive the
section-1 LIST_REL premise from these posts with Operands transport across
subsequent operands. The existential source witness added by
pointer_outcome_source_witness supplies actual evaluation, needed to recurse
through body_exprs_ptr_ok. At the last operand, the remaining source is exactly
the value-level lambda in section 1. This unifies Q/R syntactically; proving
operand-list/frame assembly is still integration work, not a proved fact.

Both exemption obligations have exact providers (m0203, original m0151):

* `gas_exempt_cert ...error_value`: for value source a, certificate for
  `ignore_bind a (return ())` yields certificate for `bind a k` with unchanged
  marks/error/leaf/finish. Instantiate k with
  `\v. ignore_bind (next v) (return ())` for first bind-success obligation.
* `gas_exempt_cert ...bind_value`: gas_marked_exec F source with left, INL v,
  mid, OK t and certificate for `k v` at `(mid with gas_obs:=[],t)` with right
  yield certificate for bind source k at left++right. Same k discharges second
  obligation. No hypothesis may be omitted.

At the eval_exprs (list-valued) boundary the value constructors do NOT apply
by type; use a list-specific certificate constructor if exported, or avoid
that generic bind by composing forced operands one value at a time. The latter
matches the existing pointer_outcome_bind_success signature exactly. The
proposed source equation is at list-level only for readability; its operational
consumer should expand to nested value binds before using that theorem.

## 6. Review requested

Do not authorize a monolithic residual proof from this audit alone. Missing
interfaces are: common value-source equation; operand post assembly including
word provenance (external typed_args_post_ptr does not retain it); deriving
spatial exterior for point operands and represented locals at scratch
allocations; frame/counted-run alignment; recovery clean final load. Existing
owned frame/prefix/run/call infrastructure should be reused rather than
copied. Arithmetic vv/value bridging and exact lower_value output type remain
integration risks. No checked counterexample to the frozen target was found.
