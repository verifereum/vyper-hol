Theory gasFocusSueContextEvents
Ancestors
  gasFocusSueFiniteEvents gasEventsContext o1ContractSue
  o1PassLift o1PassContract venomWfProps venomWf venomInst
  singleUseExpansionSupplySim option list

Theorem sue_stage_lookup_supply[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) view C C' ==>
  !nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f /\
    ?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
           sue_expand_function_supply t f = (g,t'))
    (lookup_function nm C.ctx_functions) (lookup_function nm C'.ctx_functions)
Proof
  strip_tac >> drule sue_stage_functions >> strip_tac >>
  irule list_rel_lookup_function >> conj_tac
  >- (simp[] >> metis_tac[sue_expand_function_supply_identity]) >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[sue_expand_function_supply_identity]
QED

Theorem sue_stage_finite_gas_events:
  ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY (o1_fn_row 6) C.ctx_functions /\
  lookup_function nm C.ctx_functions = SOME fn /\
  lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_state fn st ==>
  ?m extra.
    gas_events_blocks m C' fn' st = gas_events_blocks n C fn st ++ extra /\
    (terminates (run_blocks n C fn st) ==>
       extra = [] /\
       frame_result_rel (run_blocks n C fn st)
                        (run_blocks m C' fn' st))
Proof
  map_every qid_spec_tac [`st`, `fn'`, `fn`, `nm`] >>
  completeInduct_on `n` >> rpt strip_tac >>
  drule sue_stage_lookup_supply >> disch_then assume_tac >>
  `?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
          sue_expand_function_supply t fn = (fn',t')` by
    (first_x_assum (qspec_then `nm` mp_tac) >> simp[]) >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def, EVERY_MEM] >>
     metis_tac[]) >>
  `?m extra. gas_events_blocks m C' fn st = gas_events_blocks n C fn st ++ extra /\
     (terminates (run_blocks n C fn st) ==> extra = [] /\
       frame_result_rel (run_blocks n C fn st) (run_blocks m C' fn st))` by
    (irule gas_events_blocks_same_caller >> conj_tac
     >- (qx_gen_tac `name` >>
         first_x_assum (qspec_then `name` mp_tac) >>
         Cases_on `lookup_function name C.ctx_functions` >>
         Cases_on `lookup_function name C'.ctx_functions` >> simp[]) >>
     rpt strip_tac >> first_x_assum drule >> metis_tac[]) >>
  `gas_events_blocks m C' fn' st = gas_events_blocks m C' fn st` by
    (irule sue_function_supply_gas_events >>
     fs[fn_entry_state_def, fn_reachable_def] >>
     metis_tac[strict_dom_vars_defined_entry]) >>
  qexistsl_tac [`m`, `extra`] >> simp[] >> strip_tac >>
  `frame_result_rel (run_blocks n C fn st) (run_blocks m C' fn st)` by fs[] >>
  `terminates (run_blocks m C' fn st)` by metis_tac[frame_result_rel_terminates] >>
  `frame_result_rel (run_blocks m C' fn st) (run_blocks m C' fn' st)` by
    (irule sue_run_result_frame >> simp[] >>
     qexists `set (fn_ir_vars fn)` >>
     irule sue_run_blocks_supply_entry >> metis_tac[]) >>
  metis_tac[frame_result_rel_trans]
QED
