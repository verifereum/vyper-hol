(* The fixed pre-DFT walk only needs one native C7 entry abort to pin
   the abort reason at every terminating source fuel. *)
Theory gasFocusPreDftStaticAbortLift
Ancestors
  o1StaticPipelineCorrect o1PassLift o1PassContract ptrDiscipline
  venomExecSemantics venomState passSimulationDefs

Theorem focus_pre_dft_static_abort_lift:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0 ==>
  ctx_sim_fuel I D unit.cu_context (stage 7)
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
    (vs0 with vs_gas_readings := raw ++ [0w]) /\
  ctx_abort_rq D unit.cu_context (stage 7)
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
    (vs0 with vs_gas_readings := raw ++ [0w]) /\
  o1_inv D 7 (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]) /\
  ((?b u7. run_context b (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]) =
      Abort ExHalt_abort u7) ==>
    !fuel. terminates (run_context fuel unit.cu_context
             (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
      ?u. run_context fuel unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
          Abort ExHalt_abort u)
Proof
  strip_tac >>
  `!k. k <= 9 ==> o1_ctx_shape (stage k)` by metis_tac[] >>
  `!k. k <= 9 ==> EVERY (o1_fn_row k) (stage k).ctx_functions` by metis_tac[] >>
  `ctx_sim_fuel I D unit.cu_context (stage 7)
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
     (vs0 with vs_gas_readings := raw ++ [0w]) /\
   ctx_abort_rq D unit.cu_context (stage 7)
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
     (vs0 with vs_gas_readings := raw ++ [0w]) /\
   o1_inv D 7 (stage 7) (vs0 with vs_gas_readings := raw ++ [0w])` by
    (irule (SRULE [EVAL ``LENGTH o1_fn_passes``]
       o1_pipeline_pre_dft_sim_static_abort_fixed) >>
     metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `run_context b C v7 = Abort ExHalt_abort u7` >>
  qmatch_goalsub_abbrev_tac `run_context fuel src vi` >>
  `dead_result_rel D (run_context fuel src vi) (run_context fuel C v7)` by
    fs[ctx_sim_fuel_def] >>
  `terminates (run_context fuel C v7)` by metis_tac[dead_result_rel_terminates] >>
  `run_context fuel C v7 = Abort ExHalt_abort u7` by
    (Cases_on `C.ctx_entry` >> gvs[run_context_def, terminates_def] >>
     rename1 `C.ctx_entry = SOME name` >>
     Cases_on `lookup_function name C.ctx_functions` >> gvs[terminates_def] >>
     rename1 `lookup_function name _ = SOME fn` >>
     Cases_on `fn_entry_label fn` >> gvs[run_function_def, terminates_def] >>
     qmatch_asmsub_abbrev_tac `run_blocks fuel C fn s` >>
     `run_blocks (MAX fuel b) C fn s = run_blocks fuel C fn s` by
       (irule run_blocks_terminates_mono >> simp[terminates_def]) >>
     `run_blocks (MAX fuel b) C fn s = run_blocks b C fn s` by
       (irule run_blocks_terminates_mono >> simp[terminates_def]) >>
     metis_tac[]) >>
  Cases_on `run_context fuel src vi` >> gvs[dead_result_rel_def] >>
  rename1 `reason <> Revert_abort` >> Cases_on `reason` >> gvs[]
QED
