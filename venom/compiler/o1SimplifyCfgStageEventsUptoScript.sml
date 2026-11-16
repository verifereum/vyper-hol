(* Bounded GAS-site prefixes at the actual pre-walk SimplifyCFG stage. *)
Theory o1SimplifyCfgStageEventsUpto
Ancestors
  o1SimplifyCfgContextGasEvents o1ContractSimplifyCfg o1PassContract
  simplifyCfgDefs gasEvents venomPassDispatcher venomPassSchedule
  venomCompilerTypes venomExecSemantics venomInst venomState list arithmetic
  simplifyCfgProof simplifyCfgLabelProps o1PassLift unitTransformDefs

Theorem simplify_cfg_stage_events_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  o1_initial_state_ok vs /\ C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
  n <= LENGTH (gas_events_blocks fuel C fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
  ?fuel' fn'. C'.ctx_entry = SOME name /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    TAKE n (gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
    TAKE n (gas_events_blocks fuel C fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  `C'.ctx_functions = MAP simplify_cfg_fn C.ctx_functions` by
    metis_tac[simplify_cfg_stage_functions] >>
  `C'.ctx_entry = C.ctx_entry` by fs[ctx_pass_stage_def] >>
  `fn_bisim fn (simplify_cfg_fn fn)` by
    (irule simplify_cfg_fn_correct >>
     `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     gvs[o1_ctx_shape_def, EVERY_MEM] >>
     `o1_fn_shape C fn /\ simplify_cfg_fn_ok fn` by metis_tac[] >>
     gvs[o1_fn_shape_def]) >>
  `fn_entry_label (simplify_cfg_fn fn) = SOME lbl` by fs[fn_bisim_def] >>
  `lookup_function name C'.ctx_functions = SOME (simplify_cfg_fn fn)` by
    (`!f. (simplify_cfg_fn f).fn_name = f.fn_name` by
       metis_tac[simplify_cfg_fn_metadata, fn_identity_metadata_eq_def] >>
     simp[lookup_function_map]) >>
  qmatch_goalsub_abbrev_tac `gas_events_blocks fuel C fn s0` >>
  `fn_entry_state fn s0` by
    gvs[Abbr `s0`, fn_entry_state_def, o1_initial_state_ok_def] >>
  drule_all simplify_cfg_context_gas_transport >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qpat_x_assum `C'.ctx_functions = MAP _ _` kall_tac >>
  qexistsl_tac [`m`, `simplify_cfg_fn fn`] >>
  simp[TAKE_APPEND1]
QED
