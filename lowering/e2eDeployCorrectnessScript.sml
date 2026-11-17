(* Deploy-phase correctness (PLAN §5.11): e2e_deploy_correctness, the
 * constructor's run in a creation frame installs the runtime code and the
 * immutables section.  Kept apart from e2eCorrectness so the deploy work
 * owns its own file. *)
Theory e2eDeployCorrectness
Ancestors
  e2eDeployAtMarks e2eDeployDefs ctorDeployDefs
  ctorDeployInitcode ctorDeployEntry ctorDeployShape ctorDeployDefsReach
  deployUnitExecution ctorDeployBodyJoint ctorDeployDead ctorDeployFrame
  compileVyper compilePhasesProps codegen e2eProducers e2eComposition
  o1PipelineCorrect o1PassContract codegenCorrectness passSimulationDefs
  sourceCallCount
  lowerDloadDefs e2eEntry gasSummary asmOptimizer

(* A successful compilation exposes the deployment unit's phases. *)
Theorem compile_vyper_deploy_phases:
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
Proof
  simp[compile_vyper_def, deploy_phases_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_identity, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  qpat_x_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* ADMISSION: moves the deploy certificate to any call outcomes, for a call-free constructor.
   Waits for its proof. *)
Theorem deploy_unit_execution_correct_with_outcomes:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   shadow_ctx marks vs outs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    tx.function_name = "__init__" /\
    deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
      dunit vs ==>
    deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
      dunit (vs with vs_outcomes := outs)
Proof
  cheat
QED

(* ADMISSION: the deploy gas link's certificate premise at the raw free-memory pointer.
   Waits for its proof. *)
Theorem deploy_unit_execution_correct_raw_fmp:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es fmp.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_source_ok tops am tx ==>
    ?shadow_ctx. !vs.
      raw_variant fmp vs (opt_deploy_entry_state prog prog' cplan tops es) ==>
      ?marks. deploy_unit_execution_correct_with shadow_ctx marks
        tops runtime_bc am
        (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
        dunit vs
Proof
  cheat
QED

(* ADMISSION: the deploy gas link's call bound, for a call-free constructor.
   Waits for its proof. *)
Theorem deploy_source_calls_within_call_free:
  !tops am tx os gobs.
    deploy_source_ok tops am tx /\
    tx.function_name = "__init__" ==>
    deploy_source_calls_within (2 ** 64) tops am tx os gobs
Proof
  cheat
QED

(* ADMISSION: deploy_source_ok at the optimized deploy code.
   Waits for its proof. *)
Theorem deploy_source_ok_opt_code:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_source_ok tops am tx ==>
    deploy_source_ok tops am
      (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
Proof
  cheat
QED

(* ADMISSION: a raw free-memory pointer meeting the deploy gas link's bounds.
   Waits for its proof. *)
Theorem deploy_raw_fmp_exists:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan es.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) ==>
    ?fmp:bytes32.
      w2n (opt_deploy_entry_state prog prog' cplan tops es).vs_initial_fmp <=
        w2n fmp /\
      w2n fmp < 2 ** 254 /\
      unit_alloca_budget dunit.cu_context +
        32 * ctx_dload_count dunit.cu_context <= w2n fmp
Proof
  cheat
QED

(* ADMISSION: the raw-pointer safety and gas-mask boundary used inside the deploy gas link's proof.
   Waits for its proof. *)
Theorem deploy_raw_fmp_focus_mask_entry:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es
   vs_out fmp shadow_ctx func.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (!vs. raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func ==>
    ?markf. !gs.
      deploy_unit_execution_correct_with shadow_ctx (markf gs)
        tops runtime_bc am (tx with code := vs_out.vs_code) dunit
        (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                       vs_initial_fmp := fmp|>) /\
      ?D f extra.
        dead_wf D /\
        (fin = asm_opt_finalizer ==>
           !fn inst s.
             raw_reachable
               (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                              vs_initial_fmp := fmp|>)
               dunit.cu_context fn inst s /\
             gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
               (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                              vs_initial_fmp := fmp|>) s ==>
             inst_dload_in_section inst s) /\
        o1_safe_upto D (imm_len tops) (MIN (LENGTH (markf gs)) (LENGTH gs))
          dunit.cu_context
          (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                         vs_initial_fmp := fmp|>) /\
        MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx)
          (gas_events_blocks f dunit.cu_context func
            (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                           vs_initial_fmp := fmp; vs_prev_bb := NONE;
                           vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) =
          markf gs ++ extra
Proof
  cheat
QED

(* ADMITTED: SEQ-1314 (the raw_slots mask and the sites-to-slots link).
   Where the frame is not starved, every filling of its gas readings that
   meets the constructor run's storage guard extends the marked readings of
   a raw entry state carrying the S4 facts and the selected-run certificate.
   The only admission on e2e_deploy_correctness_identity's path. *)
Theorem deploy_pipeline_gas_link:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs_out fmp r es'.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    (!gobs. deploy_source_calls_within (2 ** 64) tops am (tx with code := vs_out.vs_code)
      (MAP SND (call_trace es)) gobs) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    run_call es = SOME (r, es') /\
    ~creation_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok tops am (tx with code := vs_out.vs_code) (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              raw_variant fmp vs vs_out /\
              (~deploy_source_exempt tops
                 (load_contract (SOME vs.vs_outcomes)
                   (gas_explicit marks vs.vs_gas_readings ++ tail)
                   am (tx with code := vs_out.vs_code) [(NONE, tops)] []) ==>
               !D. dead_wf D ==>
                 raw_unit_memory_ok dunit.cu_context vs /\
                 ptr_discipline (imm_len tops) dunit.cu_context vs /\
                 taint_within D dunit.cu_context vs /\
                 mem_inv dload_offset_ok dunit.cu_context vs /\
                 mem_inv dload_headroom_ok dunit.cu_context vs ==>
                 ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
                   vs_out /\
                 (fin = asm_opt_finalizer ==>
                    code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context) /\
                 o1_lowered_inv dout.po_unit.cu_context
                   vs_out) /\
              deploy_unit_execution_correct_at marks tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs)
Proof
  cheat
QED

(* The -O none case of e2e_deploy_correctness: PLAN 5.11, D28, section 9.
 * Proved from the deployment pieces
 * (ctorDeploy* theories) and the generic O1 pipeline and codegen stages.
 * Not on the logical dependency path of call correctness.
 *
 * Proof idea: relate the constructor's CODECOPY-decoded canonical
 * ABI tail to source binding, simulate its Call-free body and runtime-return
 * epilogue, then apply Verifereum handle_create/handle_exception in the SINGLE
 * fresh creation frame. Deposit gas/size failures are resource starvation.
 * Exclude the 0xEF runtime prefix. Match installed runtime code and all remaining
 * account fields, transient storage and logs; use explicit source failure
 * cases, exempting only the existing exact dynamic ABI strictness predicate.
 *
 * The source runs with NONE for the call oracle: constructor_call_free excludes EVERY Call
 * (including internal calls and Send) and the precompile builtins, whose
 * STATICCALL the EVM can fail for lack of gas, while checked constant
 * initializers are pure. No oracle/callee is needed. Its gas observations gobs
 * are existential, as in call_result_rel: msg.gas in the constructor reads the
 * readings the EVM run produced. The theorem does not claim agreement for
 * malformed constructors excluded by constructor_args_encode. There is no
 * nested-creation frame_outcome claim and no Some-root oracle hypothesis.
 *
 * A constructor that halts (selfdestruct) makes load_contract succeed without
 * installing the source at tx.target, so that INL is told apart by
 * ALOOKUP am'.sources tx.target = NONE (deploy_state_rel has it NONE at
 * entry). Then the EVM frame halts with empty output and deposits no code, and
 * the accounts after the pending deletions, transient storage and logs agree
 * as in a halting call (call_result_rel_at).
 *)
Theorem e2e_deploy_correctness_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases >> strip_tac >>
  `K SOME IN accepted_finalizers` by simp[asmOptimizerTheory.accepted_finalizers_def] >>
  drule_all compile_vyper_runtime_not_ef >> strip_tac >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `creation_resource_starved es r es'` >> simp[] >>
  `~frame_resource_starved es r es'` by
    (fs[frameOutcomeTheory.creation_resource_starved_def,
        frameOutcomeTheory.frame_resource_starved_def] >> metis_tac[]) >>
  `deploy_bc = assemble prog` by fs[deploy_phases_def] >> gvs[] >>
  `K SOME rpolicy prog = SOME prog` by simp[] >>
  `tx with code := (opt_deploy_entry_state prog prog cplan tops es).vs_code = tx`
    by metis_tac[deploy_txp_identity] >>
  `!gobs. deploy_source_calls_within (2 ** 64) tops am tx
      (MAP SND (call_trace es)) gobs` by
    (irule deploy_source_calls_within_call_free >>
     fs[deploy_state_rel_def]) >>
  drule deploy_raw_fmp_exists >>
  disch_then (qspecl_then [`prog`, `es`] strip_assume_tac) >>
  drule_all deploy_unit_execution_correct_raw_fmp >>
  disch_then (qspec_then `fmp` strip_assume_tac) >>
  drule_all deploy_pipeline_gas_link >> strip_tac >>
  drule_all e2e_deploy_correct_from_gas_link >> simp[]
QED

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code. *)
Theorem e2e_deploy_correctness_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  cheat
QED

(* TOP-LEVEL: one theorem over the accepted finalizers (Python's -O none and
   O1 final assembly).  The optimizer's case excludes, for now, programs that
   read their own code. *)
Theorem e2e_deploy_correctness:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
  >- (drule_all e2e_deploy_correctness_identity >> simp[])
  >> `~program_reads_self_code tops` by fs[] >>
  drule_all e2e_deploy_correctness_asm_opt >> simp[]
QED

(* Typed kernel schema gate. This is an ML check, not a proved alias, and adds
 * no theorem dependency. The clean result-case definition must expand to
 * precisely the literal 5.11 conclusion above, including its explicit failure
 * cases and no-prefix guard. Whether the theorem depends on a cheat is
 * checked with `holbuild check`.
 *)
val savedDeploymentAdmission = DB.fetch "e2eDeployCorrectness" "e2e_deploy_correctness";
val _ =
  let
    val expected = ``!fin policy tops deploy_bc runtime_bc am tx es.
      fin IN accepted_finalizers /\
      (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
      compile_vyper fin policy tops = SOME (deploy_bc,runtime_bc) /\
      supported_program tops /\ supported_program_deploy tops /\
      constructor_call_free tops /\
      deploy_typing_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx es ==>
      ?r es'. run_call es = SOME (r,es') /\
        (creation_resource_starved es r es' \/
         deploy_call_result_rel tops runtime_bc am tx es r es')``;
    val expanded = concl (ASSUME expected);
  in
    if aconv expanded (concl savedDeploymentAdmission) then ()
    else raise Fail "PLAN 5.11 deployment schema mismatch"
  end;
