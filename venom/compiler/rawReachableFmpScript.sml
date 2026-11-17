(*
 * The free-memory pointer of a context with no FMP operation and no
 * DALLOCA: every state the raw semantics reaches keeps the initial
 * state's vs_fmp.  Only DALLOCA, the FMP operations pre_fmp_opcode
 * excludes, and an INVOKE whose callee returns through RETFMP or DRET
 * move it; a plain RET adopts nothing.
 *
 * TOP-LEVEL:
 *   run_defs_adopt_fmp_none - a run without RETFMP/DRET returns adopting
 *                             no FMP
 *   raw_reachable_fmp_fixed - every reachable state keeps vs_fmp
 *)
Theory rawReachableFmp
Ancestors
  venomExecSemantics venomInst venomState contextRawReachable
  contextCodegenRel venomInstProofs1 venomExecProofs opcodeClass
  frameAllocationEffects ctxLookupAgreeHelpers ptrDiscipline
  o1PassContract list

Theorem step_inst_base_terminator_fmp[local]:
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def] >> pairarg_tac >> gvs[]
QED

(* A non-INVOKE step outside the FMP operations keeps vs_fmp. *)
Theorem step_inst_base_fmp_fixed[local]:
  ~is_raw_fmp_opcode inst.inst_opcode /\
  step_inst_base inst s = OK t ==> t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_terminator_fmp] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[exec_alloca_preserves_fmp]) >>
  `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> DALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def, is_raw_fmp_opcode_def]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem run_defs_no_adopt_fmp:
  (!fuel ctx inst s ret t.
     step_inst fuel ctx inst s = IntRet ret t /\
     inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET ==>
     ret.iret_adopt_fmp = NONE) /\
  (!fuel ctx bb s ret t.
     exec_block fuel ctx bb s = IntRet ret t /\
     EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
       bb.bb_instructions ==>
     ret.iret_adopt_fmp = NONE) /\
  (!fuel ctx fn s ret t.
     run_blocks fuel ctx fn s = IntRet ret t /\
     EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
       (fn_insts fn) ==>
     ret.iret_adopt_fmp = NONE)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
          once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()]) >>
      gvs[step_inst_non_invoke] >>
      drule step_inst_base_intret_opcodes >> strip_tac >> gvs[] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs()])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      once_rewrite_tac[exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb _ = SOME inst` >>
      `inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET` by
        gvs[get_instruction_def, EVERY_EL] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_blocks_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  TRY (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
         eval_phis_ok_or_error_defs >> gvs[] >> NO_TAC) >>
  `EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
     bb.bb_instructions` by
    (irule EVERY_fn_block >> qexists_tac `fn` >>
     metis_tac[lookup_block_MEM]) >>
  metis_tac[]
QED

Theorem run_defs_adopt_fmp_none:
  (!fuel ctx inst s ret t.
     step_inst fuel ctx inst s = IntRet ret t /\
     inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET ==>
     ret.iret_adopt_fmp = NONE) /\
  (!fuel ctx bb s ret t.
     exec_block fuel ctx bb s = IntRet ret t /\
     EVERY (\i. pre_fmp_opcode i.inst_opcode) bb.bb_instructions ==>
     ret.iret_adopt_fmp = NONE) /\
  (!fuel ctx fn s ret t.
     run_blocks fuel ctx fn s = IntRet ret t /\ pre_fmp_ops fn ==>
     ret.iret_adopt_fmp = NONE)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[run_defs_no_adopt_fmp]
  >- (`EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
         bb.bb_instructions` by
        (fs[EVERY_MEM, pre_fmp_opcode_def] >> metis_tac[]) >>
      metis_tac[run_defs_no_adopt_fmp]) >>
  `EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
     (fn_insts fn)` by
    (fs[pre_fmp_ops_def, EVERY_MEM, pre_fmp_opcode_def] >> metis_tac[]) >>
  metis_tac[run_defs_no_adopt_fmp]
QED

(* The callee's frame starts at the caller's vs_fmp, and an INVOKE whose
   callee returns without adopting an FMP keeps the caller's. *)
Theorem invoke_fmp_fixed[local]:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t /\
  EVERY no_raw_fmp_ops ctx.ctx_functions ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()] >> strip_tac >>
  `MEM callee_fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `EVERY (\i. i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET)
     (fn_insts callee_fn)` by
    (fs[EVERY_MEM, no_raw_fmp_ops_def] >> rpt strip_tac >>
     res_tac >> Cases_on `i.inst_opcode` >> fs[is_raw_fmp_opcode_def]) >>
  `ret.iret_adopt_fmp = NONE` by metis_tac[run_defs_no_adopt_fmp] >>
  drule (SIMP_RULE (srw_ss()) [update_var_def]
    (Q.ISPEC `\s:venom_state. s.vs_fmp` bind_outputs_preserves)) >>
  simp[adopt_return_fmp_def]
QED

Theorem raw_reachable_no_raw_fmp_fixed:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==>
    EVERY no_raw_fmp_ops ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\ active_inst fn inst s /\
    s.vs_fmp = vs0.vs_fmp
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `enters_block _ _ _`
        (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o AP_TERM (Term `\u:venom_state. u.vs_fmp`)) >>
      simp[] >> strip_tac >> simp[] >> metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (fn_insts fn)` by
        (gvs[no_raw_fmp_ops_def, EVERY_MEM] >>
         metis_tac[]) >>
      imp_res_tac EVERY_active_inst >> gvs[] >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (drule_all invoke_fmp_fixed >> simp[]) >>
      gvs[step_inst_non_invoke] >> drule_all step_inst_base_fmp_fixed >> simp[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `enters_block _ _ _`
        (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o AP_TERM (Term `\u:venom_state. u.vs_fmp`)) >>
      simp[] >> strip_tac >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> gvs[is_terminator_def]) >>
      gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_terminator_fmp >> simp[])
  >> rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `enters_block _ _ _`
        (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o AP_TERM (Term `\u:venom_state. u.vs_fmp`)) >>
      simp[] >> strip_tac >> drule setup_callee_frame >> simp[] >>
  metis_tac[lookup_function_MEM]
QED

Theorem raw_reachable_fmp_fixed:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==>
    EVERY pre_fmp_ops ctx.ctx_functions /\ ~ctx_has_dalloca ctx ==>
    MEM fn ctx.ctx_functions /\ active_inst fn inst s /\
    s.vs_fmp = vs0.vs_fmp
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `EVERY no_raw_fmp_ops ctx.ctx_functions` by
    (fs[EVERY_MEM, no_raw_fmp_ops_def, pre_fmp_ops_def,
        ctx_has_dalloca_def, EXISTS_MEM] >> rpt strip_tac >>
     rename1 `MEM i (fn_insts f)` >> res_tac >>
     Cases_on `i.inst_opcode` >>
     fs[pre_fmp_opcode_def, is_raw_fmp_opcode_def] >> metis_tac[]) >>
  drule_all raw_reachable_no_raw_fmp_fixed >> simp[]
QED
