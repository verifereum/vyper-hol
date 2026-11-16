(* Mapped-context GAS-event transport, including nested calls. *)
Theory o1SimplifyCfgContextGasEvents
Ancestors
  o1ContractSimplifyCfg o1PassContract simplifyCfgDefs gasEvents gasEventsFuel gasEventsContext simplifyCfgGasEventBoundary gasCount
  venomPassDispatcher venomPassSchedule venomCompilerTypes venomExecSemantics
  venomInst venomState list arithmetic simplifyCfgComposeGasEvents
  simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgProof
  simplifyCfgLabelProps o1PassLift

Theorem simplify_cfg_context_gas_transport:
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  D.ctx_functions = MAP simplify_cfg_fn C.ctx_functions ==>
  !n nm f s. lookup_function nm C.ctx_functions = SOME f /\ fn_entry_state f s ==>
    ?m e. gas_events_blocks m D (simplify_cfg_fn f) s = gas_events_blocks n C f s ++ e /\
      (terminates (run_blocks n C f s) ==> e = [] /\
        frame_result_rel (run_blocks n C f s) (run_blocks m D (simplify_cfg_fn f) s))
Proof
  strip_tac >>
  `!f. MEM f C.ctx_functions ==> scfg_static f /\
    fn_bisim f (simplify_cfg_fn f)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> gen_tac >> disch_tac >>
     `o1_fn_shape C f /\ simplify_cfg_fn_ok f` by metis_tac[] >>
     conj_tac
     >- gvs[o1_fn_shape_def, scfg_static_def, fn_shape_ok_scfg_shape] >>
     irule simplify_cfg_fn_correct >> gvs[o1_fn_shape_def]) >>
  `!nm. lookup_function nm D.ctx_functions =
    OPTION_MAP simplify_cfg_fn (lookup_function nm C.ctx_functions)` by
    (gen_tac >> simp[] >> irule lookup_function_map >>
     metis_tac[simplify_cfg_fn_metadata, fn_identity_metadata_eq_def]) >>
  `!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)` by
    (gen_tac >> Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     metis_tac[lookup_function_MEM, fn_bisim_def]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  `?k e. gas_events_blocks k D f s = gas_events_blocks n C f s ++ e /\
    (terminates (run_blocks n C f s) ==> e = [] /\
      frame_result_rel (run_blocks n C f s) (run_blocks k D f s))` by
    (irule gas_events_blocks_same_caller >> simp[] >>
     rpt strip_tac >>
     `g = simplify_cfg_fn f'` by metis_tac[optionTheory.SOME_11, optionTheory.OPTION_MAP_DEF] >>
     gvs[] >> first_x_assum irule >> metis_tac[]) >>
  `scfg_static f` by metis_tac[lookup_function_MEM] >>
  drule_all scfg_fn_gas_forward >> disch_then (qspecl_then [`D`, `k`] strip_assume_tac) >>
  qexistsl_tac [`m`, `e ++ e'`] >> simp[APPEND_ASSOC] >>
  metis_tac[frame_result_rel_terminates, frame_result_rel_trans]
QED
