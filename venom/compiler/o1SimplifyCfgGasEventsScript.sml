(* Preserve reached GAS-site prefixes through O1 SimplifyCFG. *)
Theory o1SimplifyCfgGasEvents
Ancestors
  o1ContractSimplifyCfg o1PassContract simplifyCfgDefs gasEvents gasEventsFuel gasEventsContext simplifyCfgGasEventBoundary gasCount
  venomPassDispatcher venomPassSchedule venomCompilerTypes venomExecSemantics
  venomInst venomState list arithmetic simplifyCfgComposeGasEvents
  simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgProof
  simplifyCfgLabelProps o1PassLift o1SimplifyCfgContextGasEvents

Theorem simplify_cfg_stage_gas_prefix:
  !rpolicy view C C' vs nm fn lbl.
    ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
    o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
    o1_run_state_ok vs /\ C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl ==>
    !fuel. ?fuel' fn' extra.
      lookup_function nm C'.ctx_functions = SOME fn' /\
      fn_entry_label fn' = SOME lbl /\
      gas_events_blocks fuel' C' fn'
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) =
      gas_events_blocks fuel C fn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) ++ extra /\
      (terminates (run_context fuel C vs) ==>
       extra = [] /\ terminates (run_context fuel' C' vs))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
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
  `lookup_function nm C'.ctx_functions = SOME (simplify_cfg_fn fn)` by
    (`!f. (simplify_cfg_fn f).fn_name = f.fn_name` by
       metis_tac[simplify_cfg_fn_metadata, fn_identity_metadata_eq_def] >>
     simp[lookup_function_map]) >>
  qmatch_goalsub_abbrev_tac `gas_events_blocks fuel C fn s0` >>
  `fn_entry_state fn s0` by
    gvs[Abbr `s0`, fn_entry_state_def, o1_run_state_ok_def,
        unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule_all simplify_cfg_context_gas_transport >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qpat_x_assum `C'.ctx_functions = MAP _ _` kall_tac >>
  qexistsl_tac [`m`, `simplify_cfg_fn fn`, `e`] >> simp[] >>
  simp[run_context_def, run_function_def, Abbr `s0`] >>
  metis_tac[frame_result_rel_terminates]
QED
