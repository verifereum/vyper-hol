Theory dftGasFromListLookup
Ancestors
  venomWf venomExecProofs contextCodegenRel contextRawReachable
  venomExecSemantics venomInst venomState list

Theorem wf_active_lookup:
  wf_function fn /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  simp[wf_function_def, active_inst_def] >> rpt strip_tac >>
  qexists_tac `bb` >> conj_tac
  >- (irule MEM_lookup_block >> gvs[fn_labels_def]) >>
  simp[get_instruction_def]
QED

Theorem entered_active_lookup:
  wf_function fn /\ enters_block fn s u /\ active_inst fn inst u ==>
  ?bb sp. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    u = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
    get_instruction bb u.vs_inst_idx = SOME inst
Proof
  strip_tac >>
  drule_all wf_active_lookup >> strip_tac >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> rpt strip_tac >>
  rename1 `eval_phis s src.bb_instructions = OK sp` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  gvs[] >> metis_tac[]
QED

Theorem lookup_wf_function:
  EVERY wf_function ctx.ctx_functions /\
  lookup_function nm ctx.ctx_functions = SOME fn ==> wf_function fn
Proof
  metis_tac[lookup_function_MEM, EVERY_MEM]
QED

Theorem raw_reachable_wf:
  !s ctx fn inst t. raw_reachable s ctx fn inst t ==>
    EVERY wf_function ctx.ctx_functions ==> wf_function fn
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt strip_tac >>
  metis_tac[lookup_wf_function]
QED
