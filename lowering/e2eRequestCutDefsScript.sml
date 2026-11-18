(* Request-cut definitions for the closed-world call outcomes theorem:
 * s1_request_prefix, vyper_call_staging, vyper_closed_world and
 * call_guard_gas_link_stmt.
 *
 * The notes below describe which cases arise under supported_program
 * (the gated scope) and which arise only outside it.
 *
 * (A) Prefix horizon.  s1_request_prefix's prefix arm assumed valid_horizon
 *     on obs_pre only but concluded whole-run raw_unit_memory_ok,
 *     ptr_discipline 0, taint_within, mem_inv dload_offset_ok and
 *     termination.  Now: those facts hold only up to the request cut
 *     (raw_safe_rq_upto: every reachable raw state that has made at most k
 *     requests, k = recorded_outcomes_count obs_pre, so the states up to and
 *     including the one making the k-th request), and termination is gone.
 *     The raw run's k-th request is stated through the reachable state
 *     (raw_reachable) whose step issues it, instead of a final state.  The
 *     cut facts are claimed
 *     only when rq is not a computed precompile: at a precompile outcome the
 *     states with at most k requests run on past obs_pre, into storage reads
 *     that H need not cover.
 *     Scope: GATED.  In-gate example:
 *       interface I:
 *           def g() -> uint256: nonpayable
 *       arr: DynArray[uint256, 2]
 *       @external
 *       def f(a: address) -> DynArray[uint256, 2]:
 *           x: uint256 = extcall I(a).g()
 *           return self.arr
 *     with g's outcome leaving arr's length word at 2^200.  The gate admits
 *     it: DynArray of a full-word leaf is a storage type
 *     (supportedTypesScript.sml:88,141-144) and an external return type
 *     (supportedDeclsScript.sml:12-15); the extcall returns a value
 *     (supportedExprFormsScript.sml:253-257).  The lowering copies the 3
 *     static words, length included, unchecked (exprLoweringScript.sml:
 *     1018-1028, 2039-2043; contextScript.sml:544-556), and the return
 *     encoder's AbiDynArray arm loops on the MLOADed length with no bound
 *     (abiEncoderScript.sml:191-226, 280-301): at i = 2 it reads past the
 *     96-byte source alloca and writes past the 128-byte return buffer.  The
 *     source fails "read_storage_slot decode" (vyperStorageScript.sml:
 *     380-386), a non-exempt error, and obs_pre (the trace before g's
 *     outcome) is a valid horizon.
 *
 * (B) Outcome index.  Requests are indexed by
 *     recorded_outcomes_count obs_pre, and the outcome is read from the raw
 *     state s whose step issues request k, before its take_outcome: HD
 *     s.vs_outcomes, or failed_outcome rq when s.vs_outcomes = [].  The step
 *     is not an INVOKE, so no builtin runs between s and the take.
 *     Scope: GATED.  The four builtins are admitted
 *     (supportedExprFormsScript.sml:115-117) and take an oracle entry.
 *     Since record_request keeps every request and the four builtins take
 *     their entry through take_call_outcome, each oracle entry taken has its
 *     StorageOutcome and its request, so recorded_outcomes_count counts every
 *     StorageOutcome.
 *
 * (C) Closed world.  vyper_call_staging combines vyper_frame_staging, a
 *     dispatched_vyper_call and the call trace bound.  For a non-static
 *     re-entry into tx.target, vyper_closed_world requires frame staging.
 *     If calldata dispatches to an external entry, it also requires
 *     dispatched_vyper_call with the trace bound and the call's source
 *     facts.  The dispatch predicate leaves nr and dflts existential:
 *     - __default__ re-entry (an ETH refund) and calldata matching no
 *       selector when __default__ exists: calldata_dispatch maps them to
 *       ("__default__", []).  GATED (__default__ is admitted).
 *     - calldata matching no selector with no __default__, a short static
 *       head, a failed decode: calldata_dispatch = NONE, where the compiled
 *       contract reverts with empty return data before any body (the
 *       dispatches-to-nothing case of loweringCalldataCorrect).  No source
 *       facts are required.  GATED.
 *     - a nonreentrant entry: dispatched_vyper_call with nr = T.  With the lock
 *       held the source call fails RuntimeError "nonreentrant lock", which
 *       is not exempt, so the arm's source conjuncts hold; with the lock free
 *       it runs as an ordinary call.  GATED (the gate doesn't restrict nr).
 *     - external default arguments: the gate forces NULL defaults for
 *       external entries.  COMPLETE ONLY.
 *     - computed precompiles: the EVERY ~computed_precompile conjuncts on
 *       the caller's and every re-entry's call trace are dropped; (B) makes
 *       them unnecessary.  GATED.
 *     Not fixed here: a contract that delegatecalls runs other code as
 *     tx.target, so the frame half is false for that frame.  COMPLETE ONLY
 *     (raw_call is outside the gate).
 *
 * (D) call_guard_gas_link takes the new s1_request_prefix and
 *     vyper_call_staging.  One marking, Skolemized from the S1 certificate
 *     (s1_request_prefix's ?marks), serves the certificate and the prefix
 *     arm, as before.  The prefix arm is s1_request_prefix's new arm at txp
 *     plus ctx_rq_upto: the optimized run's requests up to index k are the
 *     raw run's, up to the dead bytes.  ctx_rq_upto is the cut version of
 *     ctx_abort_rq; it is what the consumer composes with the source/raw
 *     alignment, and is the new S4 obligation of the route through
 *     focus_producer_finalizer.  The codegen request prefix (EVM call trace
 *     against the optimized Venom run up to the cut) belongs to the
 *     consumer, not this header.  Scope: GATED, as (A).
 *     The header is the Definition call_guard_gas_link_stmt, the statement
 *     as a predicate, so this file type-checks it with no cheat.
 *
 * Fitted to the current definitions:
 * - request_agree takes the call's target address; the arms pass
 *   tx.target, as call_result_rel does.  Its gas conjunct (a source gas cap
 *   is the Venom request's) comes with it.  gas_readings_rel takes the
 *   predicate alone now, where it took a run and the outcome T; the link
 *   drops the T, as call_result_rel does.
 * - The source call count bound is the length of the outcome list (vs, the
 *   S1 prefix) or of the call trace (es, staging and every re-entry), as
 *   the call tops state it.
 * - raw_mem_ok carries the DALLOCA no-wrap and the free-memory-pointer
 *   floor of raw_unit_memory_ok, so raw_safe_rq_upto's raw clause does too.
 * - A source call that finds no outcome left now fails, and a Venom call
 *   aborts, so the failed_outcome arm of (B) is never taken at a recorded
 *   request; it is kept so the text reads as signed.
 * - dispatched_vyper_call, source_unit_execution_correct_with,
 *   opt_entry_state and raw_variant are the existing definitions.
 *   recorded_outcomes_count is defined here.
 *)
Theory e2eRequestCutDefs
Ancestors
  e2eDefs sourceUnitExecution vyperLoweringCorrect supportedProgram compileVyper
  vyperStorageFootprint extCallOracle vyperInterpreter vyperCalldata
  callTrace frameOutcome vfmExecution vfmState vfmAccountFrame
  venomExecSemantics passSimulationDefs ptrDiscipline unitMemInv
  unitTransformDefs lowerDloadDefs contextRawReachable o1PassContract
  o1RequestContract o1PipelineCorrect codegen stackPlanGen symbolResolve
  asmOptimizer staticAbortDefs codegenSymRel memSafeRun
  loweringStateRelDefs loweringCalldataCorrect
  gasSummary e2eEntry e2eProducers fragGasOrigin fragExec ptrSafeRun
  gasShadowUnit gasExplicitSites fragGasOriginPtr venomCompilerTypes

(* ===== Request count ===== *)

Definition recorded_outcomes_count_def:
  recorded_outcomes_count observations =
    LENGTH (FILTER (\observation. case observation of
      StorageOutcome rq outcome => T | _ => F)
      observations)
End

(* ===== (A) Request cut ===== *)

(* s has made at most k external-call requests: the states up to and
   including the one making the request at index k.  Requests only grow,
   and every call records one, computed precompiles included
   (record_request). *)
Definition request_cut_def:
  request_cut (k:num) (s:venom_state) <=> LENGTH s.vs_requests <= k
End

(* ptr_discipline_upto with the request cut in place of the gas cut. *)
Definition ptr_discipline_rq_upto_def:
  ptr_discipline_rq_upto (lo:num) k ctx vs <=>
    lo <= vs.vs_alloca_next /\
    (?P. EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           ctx.ctx_functions) /\
    !stk PG G tn fn inst s.
      frame_reachable vs ctx stk PG G tn fn inst s /\ request_cut k s ==>
      access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
      allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s)
End

(* taint_within_upto with the request cut, at the pre-step state, in place
   of the gas cut.  The state making the k-th request is inside the cut, so
   that request's storage taint is dead. *)
Definition taint_within_rq_upto_def:
  taint_within_rq_upto D k ctx vs <=>
    (!stk PG G tn fn inst s fuel s'.
       frame_reachable vs ctx stk PG G tn fn inst s /\ request_cut k s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = OK s' /\
       LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
       tn.t_stor SUBSET
         D.d_stor s.vs_call_ctx.cc_address
           (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
       tn.t_trans SUBSET
         D.d_trans s.vs_call_ctx.cc_address
           (s.vs_transient s.vs_call_ctx.cc_address)) /\
    (!stk PG G tn fn inst s fuel s_h.
       frame_reachable vs ctx stk PG G tn fn inst s /\ request_cut k s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = Halt s_h ==>
       (step_taint inst s s_h tn).t_stor SUBSET
         D.d_stor s_h.vs_call_ctx.cc_address
           (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
       (step_taint inst s s_h tn).t_trans SUBSET
         D.d_trans s_h.vs_call_ctx.cc_address
           (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
       (step_taint inst s s_h tn).t_imm SUBSET D.d_imm s_h.vs_immutables /\
       ret_taint tn inst s SUBSET D.d_ret s_h.vs_returndata)
End

(* The four S3 facts of the old prefix arm (raw_unit_memory_ok,
   ptr_discipline lo, taint_within D, mem_inv dload_offset_ok), each up to
   the request cut, as o1_safe_upto states them up to the gas cut. *)
Definition raw_safe_rq_upto_def:
  raw_safe_rq_upto D lo k ctx vs <=>
    ptr_discipline_rq_upto lo k ctx vs /\ taint_within_rq_upto D k ctx vs /\
    !fn inst s.
      raw_reachable vs ctx fn inst s /\ request_cut k s ==>
      raw_mem_ok ctx fn inst s /\ dload_offset_ok ctx fn inst s /\
      inst_dload_in_section inst s
End

(* The cut version of ctx_abort_rq: every request the run of ctx' from s'
   makes at an index up to k was made, up to the dead bytes D, by the run
   of ctx from s at the same index. *)
Definition ctx_rq_upto_def:
  ctx_rq_upto D k ctx ctx' s s' <=>
    !fn' inst' t' i.
      raw_reachable s' ctx' fn' inst' t' /\ i <= k /\
      i < LENGTH t'.vs_requests ==>
      ?fn inst t.
        raw_reachable s ctx fn inst t /\ i < LENGTH t.vs_requests /\
        request_agree_except D (EL i t.vs_requests) (EL i t'.vs_requests)
End

(* ===== s1_request_prefix (A, B) ===== *)

(* The same marking supplies the unit certificate and request alignment.
   The shadow is chosen by the program, before am, tx, ret and vs.  At each
   outcome whose preceding trace obs_pre is a valid horizon for H and whose
   request rq is not a computed precompile: the source's k-th request
   (k = recorded_outcomes_count obs_pre) is rq, the raw run is safe up to
   the request cut k, and the reachable raw state s whose step issues the
   raw k-th request makes one that agrees with rq, and the outcome is the
   oracle entry s is about to take (or the failure once none is left). *)
Definition s1_request_prefix_def:
  s1_request_prefix tops <=>
    !rpolicy unit.
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      supported_program tops ==>
      ?shadow_ctx. !am tx ret vs.
        source_typing_ok tops am tx /\
        source_deployment_rel tops am tx /\
        dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
        LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
        initial_venom_state_rel tops am tx vs /\
        code_layout_valid vs /\
        EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
                    accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes /\
        LENGTH vs.vs_outcomes < 2 ** 64 /\
        vs.vs_fmp = vs.vs_initial_fmp /\
        w2n vs.vs_initial_fmp < 2 ** 254 /\
        unit_alloca_budget unit.cu_context +
          32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
        ?marks.
          source_unit_execution_correct_with shadow_ctx marks
            tops ret am tx unit vs /\
          !tail res am' rqs obs obs_pre rq outcome sfx H.
            call_external_trace (SOME vs.vs_outcomes)
              (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
              (res,am',rqs,obs) /\
            ~source_exempt tops (res,am',rqs) /\
            obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
            valid_horizon
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am []) H obs_pre ==>
            (computed_precompile rq ==>
               outcome.co_accounts = rq.cr_accounts /\
               outcome.co_tStorage = rq.cr_tStorage) /\
            (~computed_precompile rq ==>
               recorded_outcomes_count obs_pre < LENGTH rqs /\
               EL (recorded_outcomes_count obs_pre) rqs = rq /\
               raw_safe_rq_upto
                 (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 (recorded_outcomes_count obs_pre) unit.cu_context vs /\
               ?fn inst s fuel s'.
                 raw_reachable vs unit.cu_context fn inst s /\
                 inst.inst_opcode <> INVOKE /\
                 LENGTH s.vs_requests = recorded_outcomes_count obs_pre /\
                 step_inst fuel unit.cu_context inst s = OK s' /\
                 recorded_outcomes_count obs_pre < LENGTH s'.vs_requests /\
                 request_agree H tx.target
                   rq (EL (recorded_outcomes_count obs_pre) s'.vs_requests) /\
                 outcome =
                   (if s.vs_outcomes = [] then failed_outcome rq
                    else HD s.vs_outcomes))
End

(* ===== Staging and the closed world (C) ===== *)

(* es is a fresh call frame of the compiled contract, related to am and tx.
   Frame staging allows both static and non-static calls. *)
Definition vyper_frame_staging_def:
  vyper_frame_staging fin policy tops runtime_bc am tx es <=>
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    (?deploy_bc. compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc)) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    ~MEM tx.target es.rollback.toDelete
End

(* Staging keeps the original tx and real es.  The gas link supplies the
   phase witnesses. *)
Definition vyper_call_staging_def:
  vyper_call_staging fin policy tops runtime_bc am tx ret es <=>
    vyper_frame_staging fin policy tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
End

(* H holds every region and lock of the call's source trace, whatever gas
   observations it reads. *)
Definition horizon_covers_def:
  horizon_covers H am tx os <=>
    !gobs.
      EVERY (\r. MEM r (FST H))
        (storage_trace_regions (source_storage_trace am tx os gobs)) /\
      EVERY (\l. MEM l (SND H))
        (storage_trace_locks (source_storage_trace am tx os gobs)) /\
      storage_roots_fit (source_storage_trace am tx os gobs)
End

(* One horizon H for the caller and every re-entry into it during es's run.
   A re-entry is a non-static frame executing as tx.target pushed by a step
   reachable from es.  It is a fresh frame of the same compiled contract
   (vyper_frame_staging, which pins its code to runtime_bc and needs no
   pending deletions), on the caller's sources and layouts, whose calldata
   either dispatches to nothing (the compiled contract reverts with empty
   return data before any body) or dispatches to an external entry, of any
   nonreentrancy, whose source call H covers and that never ends in an
   exempt error.  Static frames write nothing.  A delegatecall or callcode
   from the contract runs other code as tx.target, so the re-entry clause
   excludes it.  The contract existed before the transaction, so no frame's
   self-destruct deletes it (run_call_to_delete), and the caller's call never
   ends in an exempt error either: the source adopts callee outcomes before
   it decodes.  Computed precompiles are allowed: s1_request_prefix reads
   each outcome from the raw state that issues its request. *)
Definition vyper_closed_world_def:
  vyper_closed_world fin policy tops runtime_bc am tx H es <=>
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) (FST H) /\
    horizon_covers H am tx (MAP SND (call_trace es)) /\
    ~account_empty (lookup_account tx.target es.originalAccounts) /\
    (!gobs. ~source_exempt tops
              (call_external (SOME (MAP SND (call_trace es))) gobs am tx)) /\
    !s u e.
      run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
      step s = (INL u, e) /\
      LENGTH s.contexts < LENGTH e.contexts /\
      (FST (HD e.contexts)).msgParams.callee = tx.target /\
      ~(FST (HD e.contexts)).msgParams.static ==>
      ?am_e tx_e.
        am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
        vyper_frame_staging fin policy tops runtime_bc am_e tx_e e /\
        (calldata_dispatch tops
           (buffer_to_list (FST (HD e.contexts)).msgParams.data) = NONE \/
         (?ret_e. dispatched_vyper_call tops tx_e
                    (buffer_to_list (FST (HD e.contexts)).msgParams.data) ret_e) /\
         LENGTH (call_trace e) < 2 ** 64 /\
         horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
         !gobs. ~source_exempt tops
                  (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e))
End

(* ===== call_guard_gas_link (D) ===== *)

(* The call guard's gas link, stated as a predicate so that this file
   type-checks it without proving it.  Its consumer proves
   Theorem call_guard_gas_link: call_guard_gas_link_stmt. *)
Definition call_guard_gas_link_stmt_def:
  call_guard_gas_link_stmt <=>
  !fin policy tops runtime_bc am tx ret es r es'.
    vyper_call_staging fin policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    run_call es = SOME (r, es') /\
    ~frame_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs.
         ?rpolicy unit out prog prog' cp fmp vs marks tail.
           gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
           resolve_o1_policy policy = SOME rpolicy /\
           lower_vyper_runtime_unit tops rpolicy = SOME unit /\
           o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
           codegen_assembly rpolicy out.po_unit = SOME prog /\
           generate_context_plan out.po_unit.cu_context = SOME cp /\
           fin rpolicy prog = SOME prog' /\
           runtime_bc = assemble prog' /\
           w2n (opt_entry_state prog prog' cp es).vs_initial_fmp <= w2n fmp /\
           w2n fmp < 2 ** 254 /\
           unit_alloca_budget unit.cu_context +
             32 * ctx_dload_count unit.cu_context <= w2n fmp /\
           raw_variant fmp vs (opt_entry_state prog prog' cp es) /\
           (!H':(bool # bytes32 # type_value) list # num list.
              (?fr. terminates (run_context fr unit.cu_context vs)) /\
              raw_unit_memory_ok unit.cu_context vs /\
              ptr_discipline 0 unit.cu_context vs /\
              taint_within
                (cx_dead H' (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                unit.cu_context vs /\
              mem_inv dload_offset_ok unit.cu_context vs /\
              mem_inv dload_headroom_ok unit.cu_context vs /\
              mem_inv
                (\ctx fn inst s. inst_dload_in_section inst s /\
                  s.vs_code = vs.vs_code /\
                  s.vs_data_section = vs.vs_data_section)
                unit.cu_context vs ==>
              ctx_sim
                (cx_dead H' (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                unit.cu_context out.po_unit.cu_context vs
                (opt_entry_state prog prog' cp es) /\
              ctx_abort_rq
                (cx_dead H' (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                unit.cu_context out.po_unit.cu_context vs
                (opt_entry_state prog prog' cp es) /\
              (fin = asm_opt_finalizer ==>
               code_end_offset_ok
                 (\ctx fn inst s.
                   raw_reachable (opt_entry_state prog prog' cp es) ctx fn inst s /\
                   ~in_static_abort_prefix fn s)
                 out.po_unit.cu_context) /\
              ((o1_lowered_inv out.po_unit.cu_context (opt_entry_state prog prog' cp es) /\
                (fin = asm_opt_finalizer ==>
                 code_end_offset_ok
                   (raw_reachable (opt_entry_state prog prog' cp es))
                   out.po_unit.cu_context)) \/
               ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
                  mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                            lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
                    out.po_unit.cu_context (opt_entry_state prog prog' cp es)) /\
                !fuel. terminates (run_context fuel unit.cu_context vs) ==>
                       ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u))) /\
           source_unit_execution_correct_at marks tops ret am (tx with code := (opt_entry_state prog prog' cp es).vs_code) unit vs /\
           !tail' res am' rqs obs obs_pre rq outcome sfx H.
             call_external_trace (SOME vs.vs_outcomes)
               (gas_explicit marks vs.vs_gas_readings ++ tail') am (tx with code := (opt_entry_state prog prog' cp es).vs_code) =
               (res,am',rqs,obs) /\
             ~source_exempt tops (res,am',rqs) /\
             obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
             valid_horizon
               (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE)
               (initial_state am []) H obs_pre ==>
             (computed_precompile rq ==>
                outcome.co_accounts = rq.cr_accounts /\
                outcome.co_tStorage = rq.cr_tStorage) /\
             (~computed_precompile rq ==>
                recorded_outcomes_count obs_pre < LENGTH rqs /\
                EL (recorded_outcomes_count obs_pre) rqs = rq /\
                raw_safe_rq_upto
                  (cx_dead H (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                  0 (recorded_outcomes_count obs_pre) unit.cu_context vs /\
                (?fn inst s fuel s' fn' inst' t fuel' t'.
                   raw_reachable vs unit.cu_context fn inst s /\
                   inst.inst_opcode <> INVOKE /\
                   LENGTH s.vs_requests = recorded_outcomes_count obs_pre /\
                   step_inst fuel unit.cu_context inst s = OK s' /\
                   recorded_outcomes_count obs_pre < LENGTH s'.vs_requests /\
                   request_agree H tx.target
                     rq (EL (recorded_outcomes_count obs_pre) s'.vs_requests) /\
                   outcome =
                     (if s.vs_outcomes = [] then failed_outcome rq
                      else HD s.vs_outcomes) /\
                   raw_reachable (opt_entry_state prog prog' cp es)
                     out.po_unit.cu_context fn' inst' t /\
                   inst'.inst_opcode <> INVOKE /\
                   LENGTH t.vs_requests = recorded_outcomes_count obs_pre /\
                   step_inst fuel' out.po_unit.cu_context inst' t = OK t' /\
                   recorded_outcomes_count obs_pre < LENGTH t'.vs_requests /\
                   request_agree_except
                     (cx_dead H (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                     (EL (recorded_outcomes_count obs_pre) s'.vs_requests)
                     (EL (recorded_outcomes_count obs_pre) t'.vs_requests) /\
                   t.vs_outcomes = s.vs_outcomes) /\
                ctx_rq_upto
                  (cx_dead H (initial_evaluation_context am.sources am.layouts (tx with code := (opt_entry_state prog prog' cp es).vs_code) NONE))
                  (recorded_outcomes_count obs_pre)
                  unit.cu_context out.po_unit.cu_context
                  vs (opt_entry_state prog prog' cp es) /\
                (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
                  mem_inv (\ctx fn inst s. (request_cut (recorded_outcomes_count obs_pre) s /\ ~in_static_abort_prefix fn s) ==>
                    lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s) out.po_unit.cu_context (opt_entry_state prog prog' cp es)) /\
                (fin = asm_opt_finalizer ==>
                  code_end_offset_ok (\ctx fn inst s. raw_reachable (opt_entry_state prog prog' cp es) ctx fn inst s /\
                    request_cut (recorded_outcomes_count obs_pre) s /\ ~in_static_abort_prefix fn s) out.po_unit.cu_context)))
End
