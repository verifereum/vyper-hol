(* FmpLowering keeps every CALL/STATICCALL success check. *)
Theory fmpStepCallChecks
Ancestors
  fmpStepCallTraversal fmpStepCallEnvironment fmpStepStructural
  fmpStepLayout fmpStepOpaque fmpStepRestrictions
  fmpLowerDefs fmpLowerProps fmpWfDefs venomWf venomInst venomEffects unitShapeDefs
  o1PassContract venomFnScheduleRunner irSupply list rich_list

Theorem calls_flagged_append_tail:
  !p. calls_flagged bbs (p ++ tail) ==> calls_flagged bbs tail
Proof
  Induct >> simp[calls_flagged_def] >> metis_tac[]
QED

Theorem fmp_root_layout_no_calls:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL)
    (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, set_param_index_def,
      callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  drule fmpStepRestrictionClosureTheory.split_fmp_entry_retpc_restrictions >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[inst_shape_ok_def] >> metis_tac[]
QED

Theorem fmp_install_checked_root_calls_flagged:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  EVERY (\bb. calls_flagged dst bb.bb_instructions) blocks ==>
  EVERY (\bb. calls_flagged dst bb.bb_instructions) out
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule fmp_root_layout_no_calls >> strip_tac >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  `calls_flagged dst tail` by (drule calls_flagged_append_tail >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) users` by
    (gvs[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]) >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
  irule calls_flagged_no_calls_prefix >> simp[EVERY_APPEND]
QED

Theorem fmp_lower_function_call_checks_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==> call_checks_ok fn'
Proof
  strip_tac >>
  `call_checks_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `!vs i. flag_fails fn.fn_blocks vs i ==> flag_fails fn'.fn_blocks vs i` by
    metis_tac[fmp_lower_function_flag_fails] >>
  qpat_x_assum `fmp_lower_function _ _ _ = _` mp_tac >>
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fmp_checked_seal_some >> gvs[fmp_seal_def, call_checks_ok_def] >>
  Cases_on `root_layout` >> gvs[] >>
  rename1 `fmp_install_root _ _ _ _ = SOME (finalbbs,_)` >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `~MEM runner (fn_ir_vars fn)` by
    (drule fresh_ir_var_contract >>
     gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\bb. EVERY (\i. EVERY (\x. MEM x (fn_ir_vars fn)) i.inst_outputs)
     bb.bb_instructions) fn.fn_blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >> rename1 `MEM x inst.inst_outputs` >>
     simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `block_ir_vars bb` >> conj_tac
     >- (qexists_tac `bb` >> simp[]) >>
     simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `inst_ir_vars inst` >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >>
     simp[inst_ir_vars_def]) >>
  `EVERY (\bb. calls_flagged finalbbs bb.bb_instructions) blocks` by
    (drule_all fmp_lower_blocks_calls_flagged >>
     gvs[call_checks_ok_def]) >>
  simp[call_checks_ok_def] >>
  drule_all fmp_install_checked_root_calls_flagged >> simp[]
QED
