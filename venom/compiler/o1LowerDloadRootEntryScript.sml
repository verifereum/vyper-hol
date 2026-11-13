(* Successful source root entry, before any simulation induction. *)
Theory o1LowerDloadRootEntry
Ancestors
  o1LowerDloadJointEntry o1LowerDloadEntryFetch o1PassContract
  venomExecSemantics venomExecProofs venomWf venomInst venomState
  contextCodegenRel passSimulationDefs list

Theorem ld_run_context_entry:
  run_context fuel C vs = r /\ terminates r ==>
  ?name fn lbl s0 s1.
    C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    s0 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
    enters_block fn s0 s1 /\ run_blocks fuel C fn s0 = r
Proof
  simp[run_context_def, run_function_def, AllCaseEqs()] >> strip_tac >>
  gvs[terminates_def] >>
  Cases_on `fuel` >- gvs[run_blocks_def] >>
  gvs[Once run_blocks_def] >>
  Cases_on `lookup_block lbl entry_fn.fn_blocks` >- gvs[] >>
  rename1 `lookup_block lbl entry_fn.fn_blocks = SOME bb` >>
  qspec_then `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`
    (qspec_then `bb.bb_instructions` strip_assume_tac) eval_phis_ok_or_error_defs
  >- (qexists_tac `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
      simp[enters_block_def] >> metis_tac[]) >> gvs[]
QED
