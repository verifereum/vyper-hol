Theory o1LowerDloadSourceEntry
Ancestors
  o1LowerDloadEntryFetch o1LowerDloadOccurrenceHeadroom o1PassLift
  o1PassContract unitShapeDefs venomExecProofs venomExecSemantics
  venomWf venomInst contextCodegenRel list passSimulationDefs

Theorem ld_terminating_run_entry:
  wf_function fn /\ ~s.vs_halted /\ terminates (run_blocks k C fn s) ==>
  ?i s1. enters_block fn s s1 /\ active_inst fn i s1
Proof
  strip_tac >>
  `?s1. enters_block fn s s1` by
    (Cases_on `k` >- fs[Once run_blocks_def, terminates_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
     >- fs[Once run_blocks_def, terminates_def] >>
     rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
     `(?p. eval_phis s bb.bb_instructions = OK p) \/
      (?e. eval_phis s bb.bb_instructions = Error e)` by
       metis_tac[eval_phis_ok_or_error_defs] >>
     fs[Once run_blocks_def, terminates_def] >>
     simp[enters_block_def] >> metis_tac[]) >>
  drule_all ld_wf_enters_block_fetch >> metis_tac[]
QED

Theorem ld_ctx_shape_lookup_opaque:
  o1_ctx_shape C /\ lookup_function nm C.ctx_functions = SOME fn ==>
  opaque_use_ok fn
Proof
  simp[o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  metis_tac[o1_fn_shape_def, fn_shape_ok_def]
QED

Theorem ld_setup_callee_not_halted:
  setup_callee fn args s = SOME cs ==> ~cs.vs_halted
Proof
  simp[setup_callee_def] >>
  Cases_on `NULL fn.fn_blocks` >> simp[] >> strip_tac >> gvs[]
QED

Theorem dload_no_phi_entry:
  first_block_no_phi f /\ fn_entry_label f = SOME lbl ==>
  (enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t <=>
   t = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  Cases_on `f.fn_blocks` >> simp[fn_entry_label_def, entry_block_def] >> strip_tac >> gvs[] >>
  `phi_prefix_length h.bb_instructions = 0 /\
   (!s. eval_phis s h.bb_instructions = OK s)` by
    (qpat_x_assum `first_block_no_phi f` mp_tac >>
     simp[first_block_no_phi_def] >>
     Cases_on `h.bb_instructions` >>
     simp[phi_prefix_length_def, eval_phis_def]) >>
  simp[enters_block_def, lookup_block_def, FIND_thm] >> metis_tac[]
QED
