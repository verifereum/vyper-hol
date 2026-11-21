(* The raw FMP stays fixed on paths that never reach its operations. *)
Theory callRejectMemory
Ancestors
  contextRawReachable contextCodegenRel venomState venomInst venomExecSemantics
  venomExecProofs venomInstProofs1 ctxLookupAgreeHelpers frameAllocationEffects
  ctxLookupAgree unitTransformDefs o1PassContract vyperCalldata callRawVariant
  vyperLoweringCorrect supportedProgram e2eDefs ptrDiscipline words arithmetic list

Theorem no_raw_fmp_step[local]:
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[exec_alloca_preserves_fmp]) >>
  `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> DALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def, is_raw_fmp_opcode_def]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem enters_block_fmp[local]:
  enters_block fn s t ==> t.vs_fmp = s.vs_fmp
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o AP_TERM (Term `\u:venom_state. u.vs_fmp`)) >>
  simp[]
QED

Theorem raw_reachable_fmp_unchanged[local]:
  !vs0 ctx fn inst s. raw_reachable vs0 ctx fn inst s ==>
    (!f i u. raw_reachable vs0 ctx f i u ==>
      ~is_raw_fmp_opcode i.inst_opcode /\ i.inst_opcode <> INVOKE) ==>
    s.vs_fmp = vs0.vs_fmp
Proof
  ho_match_mp_tac raw_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac
  >- (drule enters_block_fmp >> simp[])
  >- (simp[] >> imp_res_tac no_raw_fmp_step >> metis_tac[])
  >- (imp_res_tac enters_block_fmp >> imp_res_tac no_raw_fmp_step >> metis_tac[])
  >> metis_tac[]
QED

(* GATE_ADMISSION: held, runtime reject path reaches no fmp ops *)
Theorem lower_vyper_runtime_unit_reject_reaches_no_fmp_ops:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    ctx_has_dalloca unit.cu_context /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  cheat
QED

Theorem call_reject_raw_variant_no_wrap:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  ctx_has_dalloca unit.cu_context /\
  unit_alloca_budget unit.cu_context <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  raw_variant fmp vi vs ==>
  !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
    dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp
Proof
  strip_tac >>
  `initial_venom_state_rel tops am tx vi` by
    metis_tac[raw_variant_initial_venom_state_rel] >>
  `vi.vs_call_ctx = vs.vs_call_ctx` by metis_tac[raw_variant_call_ctx] >>
  `vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp` by
    (fs[raw_variant_def, gas_variant_def, venom_state_component_equality] >> metis_tac[]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vi`] mp_tac
    lower_vyper_runtime_unit_reject_reaches_no_fmp_ops >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `s.vs_fmp = vi.vs_fmp /\ s.vs_initial_fmp = vi.vs_initial_fmp` by
    metis_tac[raw_reachable_fmp_unchanged, raw_reachable_initial_fmp] >>
  first_x_assum drule >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by metis_tac[is_raw_fmp_opcode_def] >>
  simp[dalloca_no_wrap_def]
QED
