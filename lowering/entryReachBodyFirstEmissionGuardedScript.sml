Theory entryReachBodyFirstEmissionGuarded
Ancestors
  entryReachBodyFirstEmissionStmt compilerFirstEmission calldataRegistration
  moduleLowering externalEntryShape compileEnv fragExec emitHelper venomInst

Theorem guarded_body_empty_first_emission[local]:
  !ce key ut iv body rt a z.
  compile_guarded_body ce F key ut iv body rt a = ((),z) /\
  a.cs_current_insts = [] ==>
  !fn. fn_has_code a z fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
    i.inst_opcode <> PHI
Proof
  rpt gen_tac >>
  simp_tac (srw_ss()) [compile_guarded_body_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, comp_get_def, LET_THM] >>
  pairarg_tac >> simp_tac (srw_ss()) [] >> strip_tac >>
  drule (cj 2 first_emission_compile_stmt) >> strip_tac
  >- (gvs[block_is_terminated_def] >> Cases_on `rt` >>
      gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >>
      strip_tac >> rpt strip_tac >> drule_all fn_has_code_split >>
      strip_tac >> metis_tac[]) >>
  `cs_extends cs' z` by
    (Cases_on `block_is_terminated cs'` >> gvs[comp_return_def]
     >- simp[cs_extends_refl] >>
     Cases_on `rt` >>
     gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
     metis_tac[cs_extends_emit_inst]) >>
  rpt strip_tac >> drule_all fn_has_code_split >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem guarded_body_empty_phi:
  !ce key ut iv body rt a z fn.
  compile_guarded_body ce F key ut iv body rt a = ((),z) /\
  a.cs_current_insts = [] /\ fn_has_code a z fn ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt strip_tac >> irule first_emission_empty_phi >>
  metis_tac[guarded_body_empty_first_emission]
QED

Theorem registration_guarded_body_empty_phi:
  !ce args off a cef registered key ut iv body rt z fn.
  compile_register_positional_args ce args off a = (cef,registered) /\
  compile_guarded_body cef F key ut iv body rt registered = ((),z) /\
  a.cs_current_insts = [] /\ fn_has_code a z fn ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a registered` by
    metis_tac[first_emission_register_positional_args] >>
  `cs_extends registered z` by
    metis_tac[compile_guarded_body_labels, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  rpt strip_tac >> irule registration_suffix_empty_phi >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[guarded_body_empty_phi]
QED
