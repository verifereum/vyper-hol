(* Deploy-phase correctness (PLAN §5.11): e2e_deploy_correctness, the
 * constructor's run in a creation frame installs the runtime code and the
 * immutables section.  Kept apart from e2eCorrectness so the deploy work
 * owns its own file. *)
Theory e2eDeployCorrectness
Ancestors
  e2eCorrectness e2eDeployDefs ctorDeployDefs
  ctorDeployInitcode ctorDeployEntry ctorDeployShape ctorDeployDefsReach
  ctorDeployLowering ctorDeployMemory ctorDeployDload ctorDeployDead
  ctorDeployFrame
  compileVyper compilePhasesProps codegen e2eProducers e2eComposition
  o1PipelineCorrect o1PipelineCompose o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs e2eEntry gasSummary

Definition deploy_gas_replay_def:
  deploy_gas_replay policy tops deploy_bc runtime_bc es gs <=>
    ?rpolicy unit out prog cp vs_in.
      deploy_phases policy tops (deploy_bc, runtime_bc)
        (rpolicy, unit, out, prog, cp) /\
      o1_gas_replay rpolicy unit out vs_in (deploy_entry_state prog cp tops es) /\
      gs = vs_in.vs_gas_readings
End

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

Theorem gas_variant_code_layout_valid[local]:
  gas_variant si so /\ code_layout_valid so ==> code_layout_valid si
Proof
  rw[gas_variant_def] >> qpat_x_assum `so = _` SUBST_ALL_TAC >>
  fs[code_layout_valid_def]
QED

(* TOP-LEVEL: PLAN 5.11, D28, section 9. Proved from the deployment pieces
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
 * initializers are pure. No oracle/callee is needed. Its gas observations
 * select explicit reads from the canonical O1 replay of the EVM's readings.
 * The theorem does not claim agreement for
 * malformed constructors excluded by constructor_args_encode. There is no
 * nested-creation frame_outcome claim and no Some-root oracle hypothesis.
 *)
Theorem e2e_deploy_correctness:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?marks gs. deploy_gas_replay policy tops deploy_bc runtime_bc es gs /\
       case load_contract NONE (gas_explicit marks gs) am tx [(NONE, tops)] [] of
         INL (am', rqs) =>
           let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
            ?section.
              immutables_section_rel tops (account_immutables am' tx.target) section /\
              frame_outcome es r es' NONE (runtime_bc ++ section) am'.logs /\
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
             transient_agree cx am'.tStorage es'.rollback.tStorage
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
  `gas_variant vs_in (deploy_entry_state prog cplan tops es)` by
    metis_tac[o1_gas_replay_variant] >>
  `deploy_gas_replay policy tops deploy_bc runtime_bc es vs_in.vs_gas_readings` by
    (rewrite_tac[deploy_gas_replay_def] >>
     qexistsl_tac [`rpolicy`, `dunit`, `dout`, `prog`, `cplan`, `vs_in`] >> simp[]) >>
  Cases_on `?marks. deploy_source_exempt tops
              (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
                 [(NONE, tops)] [])`
  >- (fs[] >> qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> simp[] >> disj2_tac >>
      qexistsl_tac [`marks`, `vs_in.vs_gas_readings`] >> simp[] >>
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
  disj2_tac >> qexistsl_tac [`marks`, `vs_in.vs_gas_readings`] >> simp[] >>
  fs[deploy_result_rel_def, exception_outcome_rel_def]
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
    val expected = ``!policy tops deploy_bc runtime_bc am tx es.
      compile_vyper (K SOME) policy tops = SOME (deploy_bc,runtime_bc) /\
      supported_program tops /\ constructor_call_free tops /\
      deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx es /\
      ~(?t. runtime_bc = 0xEFw :: t) ==>
      ?r es'. run_call es = SOME (r,es') /\
        (frame_resource_starved es r es' \/
         ?marks gs. deploy_gas_replay policy tops deploy_bc runtime_bc es gs /\
           deploy_result_rel tops runtime_bc tx es r es'
             (load_contract NONE (gas_explicit marks gs) am tx [(NONE,tops)] []))``;
    val expanded = concl (REWRITE_RULE
      [deploy_result_rel_def, exception_outcome_rel_def] (ASSUME expected));
  in
    if aconv expanded (concl savedDeploymentAdmission) andalso
       null (Thm.hyp savedDeploymentAdmission) then ()
    else raise Fail "Gas-linked deployment schema mismatch"
  end;
