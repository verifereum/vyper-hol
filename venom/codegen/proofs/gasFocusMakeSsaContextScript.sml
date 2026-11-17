(* Recursive context closure for MakeSSA finite GAS observations.
   The same-context antecedent is discharged by the concrete finite proof
   at the stage join; it is not an assumption of the producer. *)
Theory gasFocusMakeSsaContext
Ancestors
  gasEventsContext o1ContractMakeSsaSrc o1PassLift o1PassContract
  makeSsaDefs venomWf list option

Theorem make_ssa_context_events_from_same_context:
  (!s fn fn' s' st fuel C.
    make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    make_ssa_current_fn s fn = (fn',s') /\ fn_entry_state fn st ==>
    ?extra.
      gas_events_blocks fuel C fn' st = gas_events_blocks fuel C fn st ++ extra /\
      (terminates (run_blocks fuel C fn st) ==>
        extra = [] /\ frame_result_rel (run_blocks fuel C fn st)
          (run_blocks fuel C fn' st))) ==>
  !rpolicy view C C' fuel nm fn fn' st.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
    lookup_function nm C.ctx_functions = SOME fn /\
    lookup_function nm C'.ctx_functions = SOME fn' /\ fn_entry_state fn st ==>
    ?m extra.
      gas_events_blocks m C' fn' st = gas_events_blocks fuel C fn st ++ extra /\
      (terminates (run_blocks fuel C fn st) ==>
        extra = [] /\ frame_result_rel (run_blocks fuel C fn st)
          (run_blocks m C' fn' st))
Proof
  disch_then (mk_asm "same") >>
  rpt gen_tac >> qid_spec_tac `st` >> qid_spec_tac `fn'` >>
  qid_spec_tac `fn` >> qid_spec_tac `nm` >>
  completeInduct_on `fuel` >> rpt gen_tac >> strip_tac >>
  `!name. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function name C.ctx_functions)
    (lookup_function name C'.ctx_functions)` by
    (drule_all make_ssa_src_stage_frame_sim >>
     disch_then (qspec_then `ARB` assume_tac) >>
     drule list_rel_lookup_function >> (impl_tac >- simp[]) >>
     strip_tac >> gen_tac >> first_x_assum (qspec_then `name` mp_tac) >>
     Cases_on `lookup_function name C.ctx_functions` >>
     Cases_on `lookup_function name C'.ctx_functions` >> simp[OPTREL_def]) >>
  `?m extra.
    gas_events_blocks m C' fn st = gas_events_blocks fuel C fn st ++ extra /\
    (terminates (run_blocks fuel C fn st) ==>
      extra = [] /\ frame_result_rel (run_blocks fuel C fn st)
        (run_blocks m C' fn st))` by
    (irule gas_events_blocks_same_caller >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all make_ssa_src_stage_lookup >> strip_tac >> gvs[] >>
  `fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
    first_block_no_phi fn` by fs[o1_fn_shape_def] >>
  asm "same" drule_all >>
  disch_then (qspecl_then [`m`, `C'`] strip_assume_tac) >>
  qexistsl_tac [`m`, `extra ++ extra'`] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  strip_tac >>
  `extra = [] /\ frame_result_rel (run_blocks fuel C fn st)
    (run_blocks m C' fn st)` by metis_tac[] >>
  `terminates (run_blocks m C' fn st)` by
    metis_tac[frame_result_rel_terminates] >>
  gvs[] >> metis_tac[frame_result_rel_trans]
QED
