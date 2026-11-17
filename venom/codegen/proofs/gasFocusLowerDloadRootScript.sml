(* Bounded source suppliers and correlated LowerDload entry coverage. *)
Theory gasFocusLowerDloadRoot
Ancestors
  o1SafeUpto lowerDloadConfiguredOrigins lowerDloadSafetyRootCoverage
  lowerDloadSafetyEntry lowerDloadSafetyWriteCoverage lowerDloadSafetyLocations
  lowerDloadSafetyRelation o1PassContract unitMemInv contextCodegenRel
  ptrDiscipline lowerDloadDefs venomInst finite_map list
  fmpAnalysisProps o1ContractLowerDload lowerDloadSafetyKernel

Theorem ld_focus_stage_suppliers:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs ==>
  ?P Sigma name fn lbl.
    EVERY (fn_ptr_ok P) C.ctx_functions /\
    (!f. MEM f C.ctx_functions ==>
      ir_supply_covers_fn (Sigma f.fn_name) f /\
      lookup_function f.fn_name C'.ctx_functions =
        SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
    C'.ctx_entry = C.ctx_entry /\ C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    lookup_function name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn)) /\
    fn_entry_label (FST (lower_dload_function_supply (Sigma fn.fn_name) fn)) = SOME lbl
Proof
  strip_tac >>
  drule o1_ctx_shape_distinct_names >> strip_tac >>
  drule_all lower_dload_stage_covered_supplies >> strip_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def,
        ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
  `?name fn lbl. C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl` by
    (fs[o1_safe_upto_def, mem_inv_raw_reachable] >> metis_tac[]) >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_name] >>
  `fn_entry_label (FST (lower_dload_function_supply (Sigma fn.fn_name) fn)) =
    fn_entry_label fn` by
    (Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >>
     drule lower_dload_function_supply_labels >> simp[]) >>
  qexistsl_tac [`P`,`Sigma`,`name`,`fn`,`lbl`] >>
  fs[ctx_pass_stage_def] >> metis_tac[]
QED

Theorem ld_focus_root_correlated:
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = FST (lower_dload_function_supply u fn) /\
  enters_block fn'
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst fn' ti t ==>
  ?inst f X.
    f.lf_fn = fn /\ f.lf_supply = u /\ f.lf_Q = [] /\
    ld_sync lo P C vs [] [] FEMPTY entry_taint fn inst t t FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f] /\
    ld_envelope u fn t t.vs_inst_idx X 0 /\
    ld_prefix C' fn' X 0 0 t t /\ ti = EL 0 X /\
    t.vs_inst_idx = 0 /\ t.vs_gas_readings = vs.vs_gas_readings
Proof
  strip_tac >>
  Cases_on `lower_dload_function_supply u fn` >> gvs[] >>
  `enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t` by
    (irule lower_dload_function_supply_enters_block_origin >> metis_tac[]) >>
  `t = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `t.vs_inst_idx = 0` by simp[] >>
  `?inst. active_inst fn inst t` by
    (irule ld_active_zero_origin >> metis_tac[]) >>
  drule_all ld_sync_entry_static >>
  disch_then (qspecl_then [`u`,`lo`] strip_assume_tac) >>
  `?X. ld_envelope u fn t 0 X 0` by
    (irule ld_envelope_entry >> metis_tac[]) >>
  `active_inst (FST (lower_dload_function_supply u fn)) ti t` by fs[] >>
  `0 < LENGTH X /\ ti = EL 0 X` by
    metis_tac[ld_envelope_active_head] >>
  qexistsl_tac [`inst`,`f`,`X`] >> gvs[ld_prefix_zero]
QED
