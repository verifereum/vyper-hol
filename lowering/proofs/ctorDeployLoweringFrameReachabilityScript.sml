Theory ctorDeployLoweringFrameReachability
Ancestors
  ctorDeployLoweringFrameTrace callTrace e2eDeployChecks stackPlanGen

(* Terminal steps need not re-establish an executable-state invariant. *)
Theorem frame_obs_tr_no_root_call_guarded[local]:
  !d obs s r s'.
    (!t. P t /\ ISL (FST (step t)) ==> P (SND (step t))) /\
    (!t. P t /\ LENGTH t.contexts = d ==>
         ~observable_call (FST (HD t.contexts))) /\
    P s /\ step s = (r,s') /\ obs.pending = NONE ==>
    (frame_obs_tr d obs s (r,s')).entries = obs.entries /\
    (frame_obs_tr d obs s (r,s')).pending = NONE
Proof
  recInduct frame_obs_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `~observable_call (FST (HD s.contexts)) \/ LENGTH s.contexts <> d` by metis_tac[] >>
  `(observe d s (r,s') obs).entries = obs.entries /\
   (observe d s (r,s') obs).pending = NONE` by
    (irule observe_no_root_call >> simp[] >> metis_tac[]) >>
  simp[Ntimes frame_obs_tr_def 2] >>
  Cases_on `ISR r \/ LENGTH s'.contexts < d` >> simp[] >>
  `P s'` by
    (qpat_x_assum `!t. P t /\ ISL _ ==> _` (qspec_then `s` mp_tac) >>
     Cases_on `r` >> gvs[]) >>
  first_x_assum (qspec_then `observe d s (r,s') obs` mp_tac) >>
  Cases_on `r` >> gvs[]
QED

Theorem call_trace_empty_guarded_step_invariant:
  (!t. P t /\ ISL (FST (step t)) ==> P (SND (step t))) /\
  (!t. P t /\ LENGTH t.contexts = LENGTH es.contexts ==>
       ~observable_call (FST (HD t.contexts))) /\ P es ==>
  call_trace es = []
Proof
  strip_tac >> simp[call_trace_def, frame_obs_def] >>
  mp_tac (Q.SPECL
    [`LENGTH es.contexts`, `<|entries := []; readings := []; pending := NONE|>`,
     `es`, `FST (step es)`, `SND (step es)`]
    frame_obs_tr_no_root_call_guarded) >> simp[]
QED

(* Producer-invariant diagnostic (C1.reachability_design).

   Audited direct emitters, not a proved compiler-wide exclusion theorem:

   Source branch                    Emitter / exclusion
   Call ExtCall                     exprLowering 1005-1045: CALL/STATICCALL
   Call Send                        exprLowering 2717-2734: CALL
   Call RawCall{,Calldata}Target     builtinSystem 80-86: DELEGATECALL,
                                    STATICCALL, CALL
   Call CreateTarget                builtinCreate 65-67,207-209,261-263:
                                    CREATE/CREATE2
   Call IntCall                     INVOKE, not an observable EVM call;
                                    forbidden as well by constructor_call_root
   Builtin Sha256                   builtinHashing 101,116,132: STATICCALL
   Builtin ECRecover/ECAdd/ECMul      builtinMisc 48,72,94,128,152: STATICCALL

   constructor_call_root excludes EVERY Call, regardless of target, and
   exactly the four listed builtin tags by precompile_builtin_def. Recursion
   over argument expressions still needs a producer theorem using the total
   supported_stmts_expr_exists traversal. No uncovered direct call emitter
   was found in lowering/defs. In particular, moduleLowering's generated
   deploy prologue/argument decoding/lock/epilogue use no call opcodes;
   abiEncoder uses CALLDATACOPY for padding, not an identity-precompile call.
   TopLevelName in compile_expr_body returns a location or emits INVALID;
   compile_name_vv likewise does not recompile a constant's initializer.
   This is NOT a proof that every generated instruction is call-free.

   Important reachability distinction: lower_vyper_deploy_unit maps ALL
   int_fns when a constructor exists, and compile_generate_deploy compiles
   these AFTER the constructor's epilogue. Their bodies are not covered by
   constructor_call_free. Runtime bytes are also opaque data. Consequently
   a whole-unit or whole-bytecode no-call assertion is the WRONG invariant.

   Proposed static intermediate (inline, no new definition): for a unit u,
     !name fn. MEM name (fcg_analyze u.cu_context).fcg_reachable /\
       venomInst$lookup_function name u.cu_context.ctx_functions = SOME fn ==>
       EVERY (\i. ~MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2])
         (fn_insts fn).
   It is not proved here. Prove constructor entry has no INVOKE plus local
   call exclusion, then FCG reachability/pruning should remove the unrestricted
   internal functions. Existing fcgPruning.lookup_function_prune_fcg_reachable
   and prune_fcg_reachable_direct_callee concern lookup/reachability, not this
   opcode invariant. Source coverage comes from deploy_source_ok; selected
   entry/code artifacts come from deploy_phases. No new source hypothesis is
   proposed, but typing/supported-statement arity facts must be consumed when
   proving local lowering (HD/EL in builtin dispatch are total).

   Missing preservation chain, not supplied by this diagnostic:
   - lowering: compilation-state extension only emits safe instructions for
     call-free bodies; prologue/epilogue entry closure; no reachable INVOKE.
   - fixed O1 prewalk: SimplifyCFG, DretDesugar, discard analyses; preserve
     direct-call exclusion and entry reachability before frozen FCG analysis.
   - pruning: restrict all retained functions by frozen_fcg reachability.
   - callee-first passes: MakeSSA, LowerDload, ConcretizeMemLoc, FmpLowering,
     MakeSSA, SimplifyCFG, SingleUseExpansion, DFT, CFGNormalization. Need
     opcode nonintroduction (or weaker reachable exclusion) at every stage;
     context lookup/label transformations must preserve entry confinement.
     The policy resolves target capabilities; it is NOT an arbitrary pass
     callback. The schedule is fixed by o1_pipeline_spec.
   - codegen: generate_emit_ops maps direct opcodes via venom_to_evm_name;
     synthesized branches emit JUMP/JUMPI/INVALID, not calls. Need extension
     through stack setup, labels, function layout and execute_plan. DJMP and
     RET emit a bare JUMP, so label validity alone cannot establish confinement.
   - assembly: establish parsing at instruction boundaries and control-flow
     preservation for assemble prog ++ args_bytes, including PUSH data widths,
     labels, wrapping, and code_end data. deploy_phases uses codegen_assembly
     and assemble directly: no assembly finalizer preservation is needed here.
     asm_data_at_end only constrains syntactic placement of data, NOT semantic
     unreachability under arbitrary dynamic jumps.

   Exact weakest semantic target for the proposed bridge is, with es fixed,
     !t. RTC (\s t. ISL (FST (step s)) /\ t = SND (step s)) es t /\
         LENGTH t.contexts = LENGTH es.contexts ==>
         ~observable_call (FST (HD t.contexts)).
   RTC is over execution_state. Initial membership and guarded preservation
   are relational closure facts; call_trace_empty_guarded_step_invariant
   above validates the consumer, without requiring terminal-state closure.
   This safety claim remains substantial new work: static opcode exclusion
   alone does NOT imply it without machine-PC/jump confinement. No candidate
   or task counterexample follows from the inspected equations. Stop for
   strategist review rather than expanding these obligations into admissions.
*)
