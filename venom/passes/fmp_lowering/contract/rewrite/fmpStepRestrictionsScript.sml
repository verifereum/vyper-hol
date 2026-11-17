(* Reference and opcode restriction interfaces for FMP lowering. *)
Theory fmpStepRestrictions
Ancestors
  fmpStepLayout fmpStepPredicateTransport fmpStepRestrictionClosure
  fmpLowerInvokeProps o1PassContract venomInst dretDesugarDefs list

Theorem fmp_lower_function_no_raw:
  fmp_lower_function ctx s fn = SOME (fn',s') ==> no_raw_fmp_ops fn'
Proof
  strip_tac >> Cases_on `analyze_fmp_context ctx` >>
  gvs[fmpLowerDefsTheory.fmp_lower_function_def] >>
  rename1 `analyze_fmp_context ctx = SOME infos` >>
  Cases_on `fmp_lower_input infos ctx fn`
  >- (irule fmpLowerPropsTheory.fmp_lower_function_removes_raw_ops >>
      goal_assum (drule_at (Pat `analyze_fmp_context _ = _`)) >>
      simp[fmpLowerDefsTheory.fmp_lower_function_def] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `fn.fn_fmp_signature` >>
  gvs[fmpLowerDefsTheory.fmp_lower_function_with_info_def]
QED

Theorem fmp_lower_function_no_dret:
  fmp_lower_function ctx s fn = SOME (fn',s') ==> no_dret fn'
Proof
  strip_tac >> drule fmp_lower_function_no_raw >>
  simp[no_raw_fmp_ops_def, no_dret_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[is_raw_fmp_opcode_def]
QED

Theorem fmp_lower_function_dalloca_nonopaque:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  !inst x. MEM inst (fn_insts fn') /\ inst.inst_opcode = DALLOCA /\
    MEM x inst.inst_outputs ==> ~gas_var fn' x /\ ~retpc_var fn' x
Proof
  strip_tac >> drule fmp_lower_function_no_raw >>
  simp[no_raw_fmp_ops_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[is_raw_fmp_opcode_def]
QED

Theorem fmp_lower_function_invoke_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ fn_invoke_ok names fn ==>
  fn_invoke_ok names fn'
Proof
  strip_tac >>
  drule fmp_lower_function_every >>
  disch_then (qspec_then
    `\j. j.inst_opcode = INVOKE ==> ?lbl rest.
      j.inst_operands = Label lbl::rest /\ MEM lbl names` mp_tac) >>
  simp[EVERY_MEM, fn_invoke_ok_def, AND_IMP_INTRO] >>
  (impl_tac >- (rpt conj_tac
  >- gvs[fn_invoke_ok_def]
  >- (rpt strip_tac >> drule_at (Pat `fmp_lower_inst _ _ _ _ _ = _`)
        fmp_lower_inst_invoke_ok >>
      disch_then (qspec_then `names` mp_tac) >>
      simp[EVERY_MEM] >> impl_tac
      >- (gvs[fn_invoke_ok_def] >> metis_tac[]) >> metis_tac[])
  >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
  simp[EVERY_MEM, MEM_APPEND] >> metis_tac[])) >> simp[]
QED

Theorem fmp_lower_function_entry_no_return:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ entry_fn_no_return fn ==>
  entry_fn_no_return fn'
Proof
  strip_tac >> drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. ~MEM j.inst_opcode [RET; RETFMP; DRET]` mp_tac) >>
  simp[GSYM entry_fn_no_return_def] >>
  (impl_tac >- (rpt conj_tac
    >- (rpt strip_tac >>
        drule_at (Pat `fmp_lower_inst _ _ _ _ _ = _`) fmp_lower_inst_no_return >>
        gvs[entry_fn_no_return_def, EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
        simp[EVERY_MEM] >> metis_tac[]) >>
    rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
    simp[EVERY_MEM, MEM_APPEND] >> metis_tac[])) >> simp[]
QED

Theorem fmp_lower_function_no_halt:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY (\j. ~MEM j.inst_opcode [STOP; RETURN]) (fn_insts fn) ==>
  EVERY (\j. ~MEM j.inst_opcode [STOP; RETURN]) (fn_insts fn')
Proof
  strip_tac >> drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. ~MEM j.inst_opcode [STOP; RETURN]` mp_tac) >>
  (impl_tac >- (rpt conj_tac
    >- simp[]
    >- (rpt strip_tac >> irule fmp_lower_inst_no_halt >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
        simp[EVERY_MEM] >> metis_tac[]) >>
    rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
    simp[EVERY_MEM, MEM_APPEND] >> metis_tac[])) >> simp[]
QED

Theorem fmp_lower_inst_no_alloca:
  inst.inst_opcode <> ALLOCA /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. j.inst_opcode <> ALLOCA) out
Proof
  rpt strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

(* FmpLowering adds no ALLOCA: it lowers DALLOCA, never ALLOCA. *)
Theorem fmp_lower_function_no_alloca:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY (\j. j.inst_opcode <> ALLOCA) (fn_insts fn) ==>
  EVERY (\j. j.inst_opcode <> ALLOCA) (fn_insts fn')
Proof
  strip_tac >> drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. j.inst_opcode <> ALLOCA` mp_tac) >>
  (impl_tac >- (rpt conj_tac
    >- simp[]
    >- (rpt strip_tac >> irule fmp_lower_inst_no_alloca >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >>
        drule_at (Pat `fmp_emit_restores _ _ _ = _`)
          fmpStepRewriteTheory.fmp_emit_restores_every >>
        disch_then irule >> simp[mk_inst_def]) >>
    rpt strip_tac >>
    gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs(),
        mk_inst_def, fmpLowerDefsTheory.set_param_index_def,
        callLayoutDefsTheory.OPTION_TO_LIST_def] >>
    drule split_fmp_entry_retpc_restrictions >>
    rw[EVERY_MEM] >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def])) >> simp[]
QED

Theorem fmp_lower_function_entry_no_params:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  fn_is_context_entry ctx fn /\ entry_fn_no_params fn ==>
  entry_fn_no_params fn'
Proof
  strip_tac >> drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. ~is_param_opcode j.inst_opcode` mp_tac) >>
  simp[GSYM entry_fn_no_params_def] >>
  (impl_tac >- (rpt conj_tac
    >- (rpt strip_tac >> irule fmp_lower_inst_no_params >>
        gvs[entry_fn_no_params_def, EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
        simp[EVERY_MEM] >> metis_tac[]) >>
    rpt strip_tac >> drule_all fmp_make_root_layout_entry_no_params >>
    simp[EVERY_APPEND])) >> simp[]
QED

Theorem fmp_lower_function_label_refs_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ fn_label_refs_ok fn ==>
  fn_label_refs_ok fn'
Proof
  strip_tac >> drule fmp_lower_function_preserves_labels >> strip_tac >>
  simp[fn_label_refs_ok_def] >>
  drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. !l.
    MEM (Label l) j.inst_operands /\ j.inst_opcode <> INVOKE ==>
    MEM l (fn_labels fn) \/ reserved_label l` mp_tac) >>
  simp[EVERY_MEM] >>
  (impl_tac >- (rpt conj_tac
    >- (gvs[fn_label_refs_ok_def] >> metis_tac[])
    >- (rpt strip_tac >>
        drule_at (Pat `fmp_lower_inst _ _ _ _ _ = _`) fmp_lower_inst_label_refs >>
        disch_then (qspec_then `fn_labels fn` mp_tac) >>
        simp[EVERY_MEM] >> impl_tac
        >- (gvs[fn_label_refs_ok_def] >> metis_tac[]) >> metis_tac[])
    >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
        simp[EVERY_MEM] >> metis_tac[]) >>
    rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
    simp[EVERY_MEM, MEM_APPEND] >> metis_tac[])) >> metis_tac[]
QED
