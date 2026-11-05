(* Necessary entry projections, not sufficient counterexample hypotheses. *)
Theory bodyPtrBopInBoundary
Ancestors bodyPtrPreds exprLoweringProps bodySim

Theorem stmt_state_rel_context_lookup:
  stmt_state_rel ctx func cenv cx es s ==>
  lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[stmt_state_rel_def, alloca_room_def]
QED

Theorem body_inv_supported_program:
  body_inv tops ctx cenv cx ==> supported_program tops
Proof
  simp[body_inv_def]
QED

Theorem body_inv_lowered_context:
  body_inv tops ctx cenv cx ==>
  ?rpolicy unit.
    (if cx.in_deploy then
       ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
     else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
    ctx = unit.cu_context /\ cenv.ce_target = rpolicy.rpol_target
Proof
  simp[body_inv_def] >> metis_tac[]
QED

(* Entry inventory (definition-level, no hidden reachability premise):
   bodyPtrPreds:20-25 universally quantifies d, PG, tops, ctx, func, cenv,
     env, ty, es. Outer premises: body_inv and expr_body_pre only.
   bodySim:61-87 fixes supported tops, lowered ctx/target, source module,
     dynamic ABI implication, compiler function/event/struct/hashmap/array
     metadata, ctor flag, alloca locals, and distinct top-level keys.
   exprSimHypsDefs:148-161 fixes expr_sim_inv, typing, byte widths,
     allocation limits, call safety, no EVM run, supported call modules,
     ABI-decode occurrence and dynamic ABI compatibility. It does NOT require
     supported_expr e or occurrence of e itself in the source program.
   bodyPtrDefs:216-260 inner premises for BOTH judgments:
     1. exact lowering equation from arbitrary sa to sb (lower_value/op for
        value judgment; compile_expr/vv for place judgment);
     2. fn_has_code sa sb func and fn_inst_ids_distinct func;
     3. local_ptrs_reserved cenv sa, no ctx dalloca, not ctor;
     4. return buffer and PC variable names not_fresh_at sa;
     5. gas_admissible source computation (value judgment binds read_result
        and uses expr_res_ok; place judgment uses expr_vv_res_ok);
     6. stmt_state_rel ctx func cenv cx es s0;
     7. ghost_inv d cenv cx es G0 tn0 s0;
     8. not halted, current block = sa block, cursor = LENGTH sa instructions.
   exprLoweringProps:412-421 expands (6) to state_rel, alloca_inv,
     alloca_room, fmp_room, immutable separation/base-zero, recorded ALLOCA
     sizes. alloca_room:245-253 forces actual context lookup, finite acyclic
     reachable callees, and enough unwrapped allocation space.
   fragExec:112-118 constrains emitted blocks by exact lookup and sb current
     instructions by isPREFIX in its actual function block. It does not assert
     sa is compiler-reachable or e occurs in tops.
   Existing source/runtime probes certify only their stated parameters.
   A joint supported unit/function/code placement remains UNRESOLVED; no
     existing old probe simultaneously meets items 1-8 for the string witness.
   In particular G0/tn0 and runtime variable values must meet ghost_inv and
     state_rel, not merely a chosen deterministic isolated run. *)

(* Additional inventory detail:
   compileEnv:1465-1480 state_rel relates locals/pointers, storage and its
     variable metadata, transient state and metadata, accounts, immutables,
     logs, call/transaction/block contexts, nonstatic flags, outcomes,
     requests, and pending deletions. It does not require fresh temporary
     variable names to be unbound or carry any specific ghost provenance.
   compileEnv:921-930 local_ptrs_reserved excludes MemLoc locals, makes local
     pointer names old and injective, and separates an old immutable pointer.
   bodyPtrDefs:80-92 ghost_inv constrains live local pointer coverage and
     untainted-memory value representation, return buffer coverage, empty
     return-PC taint, and storage taint. There is no global assertion about
     provenance/taint of every fresh temporary in the machine state.
   gasContext:25-29 gas_admissible quantifies over ALL gas observations;
     an isolated successful evaluation is not by itself that certificate.
   These details are necessary checks for an arbitrary sa and runtime state;
     neither such state nor its ghost is asserted compiler-reachable. *)
