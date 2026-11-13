(* Deploy-phase correctness (PLAN §5.11): e2e_deploy_correctness, the
 * constructor's run in a creation frame installs the runtime code and the
 * immutables section.  Kept apart from e2eCorrectness so the deploy work
 * owns its own file. *)
Theory e2eDeployCorrectness
Ancestors
  e2eDeployDefs ctorDeployDefs
  ctorDeployInitcode ctorDeployEntry ctorDeployShape ctorDeployDefsReach
  ctorDeployLowering ctorDeployMemory ctorDeployDload ctorDeployDead
  ctorDeployFrame
  compileVyper compilePhasesProps codegen e2eProducers e2eComposition
  o1PipelineCorrect o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs e2eEntry gasSummary asmOptimizer
  codegenAsmOpt e2eAsmOpt e2eDeployAsmOpt

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
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?gobs. case load_contract NONE gobs am tx [(NONE, tops)] [] of
         INL (am', rqs) =>
           if ALOOKUP am'.sources tx.target = NONE then
             let cx = initial_evaluation_context
                        ((tx.target, [(NONE, tops)]) :: am'.sources) am'.layouts tx NONE in
             ?lgs.
               frame_outcome es r es' NONE [] lgs /\
               (lookup_account tx.target es'.rollback.accounts).code = [] /\
               accounts_agree cx am'.accounts
                 (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
               transient_agree cx am'.tStorage es'.rollback.tStorage /\
               logs_correspond (compiled_event_info tops) (type_env tops)
                 tx.target am'.logs lgs
           else
           let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
            ?section lgs.
              immutables_section_rel tops (account_immutables am' tx.target) section /\
              frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
              (lookup_account tx.target es'.rollback.accounts).code = runtime_bc ++ section /\
             (!a. a <> tx.target ==>
                  lookup_account a es'.rollback.accounts =
                  lookup_account a am'.accounts) /\
             (lookup_account tx.target es'.rollback.accounts) with code := [] =
             (lookup_account tx.target am'.accounts) with
               <| code := [];
                  storage := (lookup_account tx.target es'.rollback.accounts).storage |> /\
             storage_agree
               (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
               (lookup_account tx.target am'.accounts).storage
               (lookup_account tx.target es'.rollback.accounts).storage /\
             transient_agree cx am'.tStorage es'.rollback.tStorage /\
             logs_correspond (compiled_event_info tops) (type_env tops)
               tx.target am'.logs lgs
       | INR (AssertException s) =>
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                         (exc = Reverted \/ s = "UNREACHABLE")
       | INR (Error e) =>
           unspecified_behaviour_exempt tops e \/
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
       | INR BreakException => F
       | INR ContinueException => F
       | INR (ReturnException _) => F)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases >> strip_tac >>
  drule compile_vyper_runtime_nonempty >> strip_tac >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  qspecl_then [`deploy_dead tops runtime_bc am tx`, `imm_len tops`, `rpolicy`,
               `dunit`, `dout`, `deploy_entry_state prog cplan tops es`] mp_tac
    run_venom_pipeline_correct >>
  impl_tac >- fs[deploy_dead_wf] >> strip_tac >>
  Cases_on `?marks. deploy_source_exempt tops
              (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                 [(NONE, tops)] [])`
  >- (fs[] >> qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> simp[] >> disj2_tac >>
      qexists_tac `gas_explicit marks vs_in.vs_gas_readings` >>
      Cases_on `load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                  [(NONE, tops)] []` >>
      fs[deploy_source_exempt_def] >>
      rename1 `INR exc` >> Cases_on `exc` >> fs[]) >>
  pop_assum (strip_assume_tac o SIMP_RULE bool_ss []) >>
  drule_all deploy_unit_execution_correct >> strip_tac >- metis_tac[] >>
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >>
     qexists_tac `deploy_entry_state prog cplan tops es` >> fs[o1_run_state_ok_def]) >>
  drule_all deploy_unit_memory_ok >> strip_tac >>
  drule_all deploy_unit_dload_ok >> strip_tac >>
  `ctx_sim (deploy_dead tops runtime_bc am tx) dunit.cu_context dout.po_unit.cu_context vs_in
     (deploy_entry_state prog cplan tops es) /\
   o1_lowered_inv dout.po_unit.cu_context (deploy_entry_state prog cplan tops es)` by
    metis_tac[] >>
  `terminates (run_context fuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?fuel'. dead_result_rel (deploy_dead tops runtime_bc am tx) (run_context fuel dunit.cu_context vs_in)
             (run_context fuel' dout.po_unit.cu_context
                (deploy_entry_state prog cplan tops es))` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
         [(NONE, tops)] [])` by metis_tac[] >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`,
               `gas_explicit marks vs_in.vs_gas_readings`] mp_tac
    deploy_venom_result_rel_dead >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `(deploy_entry_state prog cplan tops es).vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[deploy_entry_state_def, entry_venom_state_def] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `Inv`,
               `deploy_entry_state prog cplan tops es`, `shadow_root es`] mp_tac
    codegen_correct >>
  impl_tac >- fs[] >> disch_tac >>
  qspecl_then [`tops`, `runtime_bc`, `deploy_bc`, `am`, `tx`, `es`,
               `load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                  [(NONE, tops)] []`,
               `run_context fuel' dout.po_unit.cu_context
                  (deploy_entry_state prog cplan tops es)`] mp_tac deploy_venom_frame >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`r`, `es'`] strip_assume_tac) >>
  qexistsl_tac [`r`, `es'`] >> fs[] >>
  disj2_tac >> qexists_tac `gas_explicit marks vs_in.vs_gas_readings` >>
  fs[deploy_result_rel_def]
QED

(* An exempt source result is an exempt Error. *)
Theorem deploy_source_exempt_error[local]:
  !tops res.
    deploy_source_exempt tops res ==>
    ?e. res = INR (Error e) /\ unspecified_behaviour_exempt tops e
Proof
  rpt gen_tac >> Cases_on `res` >- simp[deploy_source_exempt_def] >>
  Cases_on `y` >> simp[deploy_source_exempt_def]
QED

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code. *)
Theorem e2e_deploy_correctness_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?gobs. case load_contract NONE gobs am tx [(NONE, tops)] [] of
         INL (am', rqs) =>
           if ALOOKUP am'.sources tx.target = NONE then
             let cx = initial_evaluation_context
                        ((tx.target, [(NONE, tops)]) :: am'.sources) am'.layouts tx NONE in
             ?lgs.
               frame_outcome es r es' NONE [] lgs /\
               (lookup_account tx.target es'.rollback.accounts).code = [] /\
               accounts_agree cx am'.accounts
                 (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
               transient_agree cx am'.tStorage es'.rollback.tStorage /\
               logs_correspond (compiled_event_info tops) (type_env tops)
                 tx.target am'.logs lgs
           else
           let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
            ?section lgs.
              immutables_section_rel tops (account_immutables am' tx.target) section /\
              frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
              (lookup_account tx.target es'.rollback.accounts).code = runtime_bc ++ section /\
             (!a. a <> tx.target ==>
                  lookup_account a es'.rollback.accounts =
                  lookup_account a am'.accounts) /\
             (lookup_account tx.target es'.rollback.accounts) with code := [] =
             (lookup_account tx.target am'.accounts) with
               <| code := [];
                  storage := (lookup_account tx.target es'.rollback.accounts).storage |> /\
             storage_agree
               (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
               (lookup_account tx.target am'.accounts).storage
               (lookup_account tx.target es'.rollback.accounts).storage /\
             transient_agree cx am'.tStorage es'.rollback.tStorage /\
             logs_correspond (compiled_event_info tops) (type_env tops)
               tx.target am'.logs lgs
       | INR (AssertException s) =>
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                         (exc = Reverted \/ s = "UNREACHABLE")
       | INR (Error e) =>
           unspecified_behaviour_exempt tops e \/
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
       | INR BreakException => F
       | INR ContinueException => F
       | INR (ReturnException _) => F)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases_asm_opt >> strip_tac >>
  drule compile_vyper_runtime_nonempty_asm_opt >> strip_tac >>
  drule compile_vyper_deploy_nonempty_asm_opt >> strip_tac >>
  qpat_x_assum `deploy_bc = assemble prog'` SUBST_ALL_TAC >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  (* The Venom side runs on vs_out: es's entry state with prog's layout.
     The deployment stages S1 run on es_p, a frame with prog's code whose
     entry state is vs_out up to GAS readings and call outcomes. *)
  drule_all opt_deploy_frame >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  `o1_run_state_ok (vs_out with vs_outcomes := [])` by
    metis_tac[gas_variant_run_state_ok] >>
  `o1_run_state_ok vs_out` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def, code_layout_valid_def] >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
  `vs_out.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs_out.vs_code = assemble prog ++ vs_out.vs_data_section` by
    simp[Abbr `vs_out`, opt_deploy_entry_state_def, opt_entry_state_def,
         entry_venom_state_def] >>
  `LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (`LENGTH vs_out.vs_code <= dimword (:256) DIV 2` by
       fs[o1_run_state_ok_def, code_layout_valid_def] >>
     `0 < LENGTH (assemble prog)` by (Cases_on `assemble prog` >> fs[]) >>
     qpat_x_assum `0 < _` mp_tac >>
     qpat_x_assum `LENGTH vs_out.vs_code <= _` mp_tac >>
     qpat_x_assum `vs_out.vs_code = _` (fn th => REWRITE_TAC [th]) >> simp[]) >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  qspecl_then [`deploy_dead tops runtime_bc am tx`, `imm_len tops`, `rpolicy`,
               `dunit`, `dout`, `vs_out`] mp_tac
    o1_pipeline_code_end_offset_ok >>
  impl_tac >-
    (qpat_assum `!fn inst. _ ==> ~MEM (Label "code_end") _`
       (fn th => REWRITE_TAC [th]) >>
     fs[deploy_dead_wf]) >> strip_tac >>
  `gas_variant (vs_in with vs_outcomes := [])
     (deploy_entry_state prog cplan tops es_p)` by
    (gvs[gas_variant_def, venomStateTheory.venom_state_component_equality]) >>
  drule_all deploy_unit_outcomes_free >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `?marks. deploy_source_exempt tops
              (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                 [(NONE, tops)] [])`
  >- (pop_assum strip_assume_tac >>
      qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> conj_tac >- first_assum ACCEPT_TAC >>
      disj2_tac >> qexists_tac `gas_explicit marks vs_in.vs_gas_readings` >>
      drule deploy_source_exempt_error >> strip_tac >>
      qpat_x_assum `load_contract _ _ _ _ _ _ = INR _` SUBST1_TAC >> simp[]) >>
  pop_assum (strip_assume_tac o SIMP_RULE bool_ss []) >>
  `?marks fuel.
     deploy_venom_result_rel tops runtime_bc tx
       (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
          [(NONE, tops)] [])
       (run_context fuel dunit.cu_context vs_in)` by metis_tac[] >>
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >>
     qexists_tac `vs_out` >> fs[o1_run_state_ok_def]) >>
  `raw_unit_memory_ok dunit.cu_context vs_in /\
   ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
   taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context vs_in /\
   mem_inv dload_offset_ok dunit.cu_context vs_in /\
   mem_inv dload_headroom_ok dunit.cu_context vs_in /\
   mem_inv (\c f inst s. inst_dload_in_section inst s /\
                         s.vs_code = vs_in.vs_code /\
                         s.vs_data_section = vs_in.vs_data_section)
     dunit.cu_context vs_in` by metis_tac[] >>
  `ctx_sim (deploy_dead tops runtime_bc am tx) dunit.cu_context
     dout.po_unit.cu_context vs_in vs_out /\
   o1_lowered_inv dout.po_unit.cu_context vs_out /\
   code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context` by
    metis_tac[] >>
  `terminates (run_context fuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?fuel'. dead_result_rel (deploy_dead tops runtime_bc am tx)
             (run_context fuel dunit.cu_context vs_in)
             (run_context fuel' dout.po_unit.cu_context vs_out)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
         [(NONE, tops)] [])` by metis_tac[] >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`,
               `gas_explicit marks vs_in.vs_gas_readings`] mp_tac
    deploy_venom_result_rel_dead >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  (* The optimizer case's static facts of the constructor's O1 output. *)
  `o1_source_unit_ok dunit` by metis_tac[] >>
  `label_flow_ok dout.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok dout.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  `code_layout_valid vs_out` by fs[o1_run_state_ok_def] >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_codegen_asm_entry_rel >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_asm_frame_rel >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs_out`, `vs_out`, `shadow_root es`] mp_tac
    codegen_correct_asm_opt >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[Abbr `vs_out`]) >>
  disch_tac >>
  qspecl_then [`tops`, `runtime_bc`, `assemble prog'`, `am`, `tx`, `es`,
               `load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                  [(NONE, tops)] []`,
               `run_context fuel' dout.po_unit.cu_context vs_out`] mp_tac
    deploy_venom_frame >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`r`, `es'`] strip_assume_tac) >>
  qexistsl_tac [`r`, `es'`] >> fs[] >>
  disj2_tac >> qexists_tac `gas_explicit marks vs_in.vs_gas_readings` >>
  fs[deploy_result_rel_def]
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
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?gobs. case load_contract NONE gobs am tx [(NONE, tops)] [] of
         INL (am', rqs) =>
           if ALOOKUP am'.sources tx.target = NONE then
             let cx = initial_evaluation_context
                        ((tx.target, [(NONE, tops)]) :: am'.sources) am'.layouts tx NONE in
             ?lgs.
               frame_outcome es r es' NONE [] lgs /\
               (lookup_account tx.target es'.rollback.accounts).code = [] /\
               accounts_agree cx am'.accounts
                 (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
               transient_agree cx am'.tStorage es'.rollback.tStorage /\
               logs_correspond (compiled_event_info tops) (type_env tops)
                 tx.target am'.logs lgs
           else
           let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
            ?section lgs.
              immutables_section_rel tops (account_immutables am' tx.target) section /\
              frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
              (lookup_account tx.target es'.rollback.accounts).code = runtime_bc ++ section /\
             (!a. a <> tx.target ==>
                  lookup_account a es'.rollback.accounts =
                  lookup_account a am'.accounts) /\
             (lookup_account tx.target es'.rollback.accounts) with code := [] =
             (lookup_account tx.target am'.accounts) with
               <| code := [];
                  storage := (lookup_account tx.target es'.rollback.accounts).storage |> /\
             storage_agree
               (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
               (lookup_account tx.target am'.accounts).storage
               (lookup_account tx.target es'.rollback.accounts).storage /\
             transient_agree cx am'.tStorage es'.rollback.tStorage /\
             logs_correspond (compiled_event_info tops) (type_env tops)
               tx.target am'.logs lgs
       | INR (AssertException s) =>
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                         (exc = Reverted \/ s = "UNREACHABLE")
       | INR (Error e) =>
           unspecified_behaviour_exempt tops e \/
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
       | INR BreakException => F
       | INR ContinueException => F
       | INR (ReturnException _) => F)
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
      deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx es /\
      ~(?t. runtime_bc = 0xEFw :: t) ==>
      ?r es'. run_call es = SOME (r,es') /\
        (frame_resource_starved es r es' \/
         ?gobs. deploy_result_rel tops runtime_bc tx es r es'
           (load_contract NONE gobs am tx [(NONE,tops)] []))``;
    val expanded = concl (REWRITE_RULE [deploy_result_rel_def] (ASSUME expected));
  in
    if aconv expanded (concl savedDeploymentAdmission) andalso
       null (Thm.hyp savedDeploymentAdmission) then ()
    else raise Fail "PLAN 5.11 deployment schema mismatch"
  end;
