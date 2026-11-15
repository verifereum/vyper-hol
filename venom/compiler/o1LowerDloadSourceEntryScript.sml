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

Theorem ld_terminating_invoke_inversion:
  i.inst_opcode = INVOKE /\ step_inst k C i s = r /\ terminates r ==>
  ?nm ops fn args cs cr.
    decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    run_blocks k C fn cs = cr /\ terminates cr /\
    ((?ir se s1. cr = IntRet ir se /\
       bind_outputs i.inst_outputs ir.iret_values
         (adopt_return_fmp ir (merge_callee_state s se)) = SOME s1 /\ r = OK s1) \/
     (?se. cr = Halt se /\ r = Halt se) \/
     (?ab se. cr = Abort ab se /\ r = Abort ab se))
Proof
  strip_tac >>
  qpat_x_assum `step_inst k C i s = r` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `decode_invoke i`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `decode_invoke i = SOME dec` >> PairCases_on `dec` >>
  Cases_on `lookup_function dec0 C.ctx_functions`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  Cases_on `eval_operands dec1 s`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `lookup_function dec0 C.ctx_functions = SOME fn` >>
  rename1 `eval_operands dec1 s = SOME args` >>
  Cases_on `setup_callee fn args s`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `setup_callee fn args s = SOME cs` >>
  Cases_on `run_blocks k C fn cs` >> simp[] >>
  rpt strip_tac >> gvs[terminates_def, AllCaseEqs()] >>
  qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >> gvs[]
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
