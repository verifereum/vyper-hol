(* Observable root opcode/output fingerprint for FMP lowering. *)
Theory fmpStageOpBaseRoot
Ancestors
  fmpLowerDefs fmpLowerProps callLayoutDefs fmpStageRel fmpStepLayout fmpStepRewrite o1PassContract
  list rich_list finite_map venomInst

Theorem fmp_lower_inst_root_free[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  inst.inst_opcode <> INITIAL_FMP /\ inst.inst_opcode <> FMP_PARAM ==>
  EVERY (\i. i.inst_opcode <> INITIAL_FMP /\ i.inst_opcode <> FMP_PARAM) out
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- gvs[fmp_lower_inst_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- gvs[fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- gvs[fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- gvs[fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- gvs[fmp_lower_inst_def, AllCaseEqs()] >>
  gvs[fmp_lower_inst_ordinary, AllCaseEqs()]
QED

Theorem fmp_lower_blocks_root_free[local]:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> INITIAL_FMP /\
    i.inst_opcode <> FMP_PARAM) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. i.inst_opcode <> INITIAL_FMP /\
    i.inst_opcode <> FMP_PARAM) bb.bb_instructions) out
Proof
  strip_tac >> drule fmp_lower_blocks_every >>
  disch_then (qspec_then `\i. i.inst_opcode <> INITIAL_FMP /\
    i.inst_opcode <> FMP_PARAM` mp_tac) >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> irule fmp_lower_inst_root_free >>
        gvs[EVERY_MEM] >> metis_tac[]) >>
    rpt strip_tac >> irule fmp_emit_restores_every >>
    qexistsl [`bases`, `runner`, `s''`, `s1`] >> simp[mk_inst_def])) >>
  simp[]
QED

Theorem fmp_install_root_filter[local]:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  EVERY (\bb. EVERY (\i. ~P i) bb.bb_instructions) (entry::rest) /\
  EVERY (\i. ~P i) (OPTION_TO_LIST newpc) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s)
    (entry::rest) = SOME (out,s') ==>
  FILTER P (fn_insts (fn with fn_blocks := out)) =
    FILTER P (OPTION_TO_LIST root)
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qpat_x_assum `!s'' root rest fn ctx. _` kall_tac >>
  `FILTER P users = [] /\ FILTER P tail = [] /\
   FILTER P (fn_insts (fn with fn_blocks := rest)) = [] /\
   FILTER P (OPTION_TO_LIST newpc) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  Cases_on `fn_is_context_entry ctx fn` >>
  gvs[fn_insts_def, fn_insts_blocks_def, FILTER_APPEND]
QED

Theorem fmp_make_root_layout_filter[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root newpc s') ==>
  EVERY (\i. i.inst_opcode <> INITIAL_FMP /\ i.inst_opcode <> FMP_PARAM)
    (OPTION_TO_LIST newpc) /\
  MAP (\i. (i.inst_opcode,i.inst_outputs))
    (FILTER (\i. i.inst_opcode = INITIAL_FMP \/ i.inst_opcode = FMP_PARAM)
      (OPTION_TO_LIST root)) =
    if info.fi_needs_fmp then
      [(if fn_is_context_entry ctx fn then INITIAL_FMP else FMP_PARAM,[runner])]
    else []
Proof
  strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def] >>
     metis_tac[split_fmp_entry_retpc_opcode]) >>
  gvs[fmp_make_root_layout_def, AllCaseEqs(), OPTION_TO_LIST_def,
      mk_inst_def, set_param_index_def] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_install_checked_root_filter[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  pre_fmp_ops fn ==>
  MAP (\i. (i.inst_opcode,i.inst_outputs))
    (FILTER (\i. i.inst_opcode = INITIAL_FMP \/ i.inst_opcode = FMP_PARAM)
      (fn_insts (fn with fn_blocks := out))) =
    if info.fi_needs_fmp then
      [(if fn_is_context_entry ctx fn then INITIAL_FMP else FMP_PARAM,[runner])]
    else []
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_filter >> strip_tac >>
  `EVERY (\bb. EVERY (\i. i.inst_opcode <> INITIAL_FMP /\
    i.inst_opcode <> FMP_PARAM) bb.bb_instructions) fn.fn_blocks` by
    (gvs[pre_fmp_ops_def, pre_fmp_opcode_def, fn_insts_def,
         EVERY_MEM, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all fmp_lower_blocks_root_free >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  drule_at (Pat `fmp_install_root _ _ _ _ = _`)
    (Q.INST [`P` |-> `\i. i.inst_opcode = INITIAL_FMP \/
      i.inst_opcode = FMP_PARAM`] fmp_install_root_filter) >>
  disch_then (qspecl_then [`tail`, `oldpc`] mp_tac) >> gvs[]
QED

Theorem fmp_stage_lowered_root_fingerprint:
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  fmp_stage_lowered infos ctx runner fn fn' ==>
  MAP (\i. (i.inst_opcode,i.inst_outputs))
    (FILTER (\i. i.inst_opcode = INITIAL_FMP \/ i.inst_opcode = FMP_PARAM)
      (fn_insts fn')) =
    case fmp_stage_root infos ctx fn of
      NONE => []
    | SOME p =>
        [(if fn_is_context_entry ctx fn then INITIAL_FMP else FMP_PARAM,[runner])]
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[] >> drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def]
  >- (gvs[fmp_stage_root_def, fn_insts_def, FILTER_EQ_NIL,
          pre_fmp_ops_def, pre_fmp_opcode_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_checked_root_filter >> strip_tac >>
  Cases_on `fn.fn_blocks` >>
  gvs[fmp_stage_root_def, split_fmp_entry_def, fn_insts_def] >>
  Cases_on `info.fi_needs_fmp` >> simp[]
QED
