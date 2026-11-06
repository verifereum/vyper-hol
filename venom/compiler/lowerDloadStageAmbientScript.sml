(* Frozen-contract ambient witnesses, without target execution assumptions. *)
Theory lowerDloadStageAmbient
Ancestors
  lowerDloadConfiguredOrigins lowerDloadSafetyRootCoverage
  lowerDloadReturnReconstruction o1PassContract unitMemInv
  contextRawReachable contextCodegenRel ptrDiscipline list
  venomInst o1ContractLowerDload fmpAnalysisProps
Libs
  lowerDloadReturnPackageLib

Theorem ld_stage_ambient:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
  ?lo P Sigma.
    EVERY (fn_ptr_ok P) C.ctx_functions /\
    (!fn. MEM fn C.ctx_functions ==>
      ^ld_covered_ambient lo C C' vs Sigma names fn
        (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
    C'.ctx_entry = C.ctx_entry /\
    (?name fn lbl. C'.ctx_entry = SOME name /\
      lookup_function name C'.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl)
Proof
  strip_tac >>
  drule o1_ctx_shape_distinct_names >> strip_tac >>
  drule_all lower_dload_stage_covered_supplies >> strip_tac >>
  fs[o1_src_inv_def] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
     simp[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  qexistsl [`lo`,`P`,`Sigma`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> simp[] >> metis_tac[]) >>
  conj_tac >- fs[ctx_pass_stage_def] >>
  `?name fn lbl. C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl` by
    (qpat_x_assum `mem_inv raw_mem_ok C vs` mp_tac >>
     simp[mem_inv_def, codegen_reachability_package_def] >> metis_tac[]) >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_name] >>
  qexistsl [`name`,`FST (lower_dload_function_supply (Sigma fn.fn_name) fn)`,`lbl`] >>
  `fn_entry_label (FST (lower_dload_function_supply (Sigma fn.fn_name) fn)) =
    fn_entry_label fn` by
    (Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >>
     drule lower_dload_function_supply_labels >> simp[]) >>
  fs[ctx_pass_stage_def] >> metis_tac[]
QED

Theorem ld_stage_root_coverage:
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  mem_inv raw_mem_ok C vs /\ C'.ctx_entry = C.ctx_entry /\
  C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn'
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst fn' ti t ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  strip_tac >>
  `?nm fn lb. C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lb` by
    (qpat_x_assum `mem_inv raw_mem_ok C vs` mp_tac >>
     simp[mem_inv_def, codegen_reachability_package_def] >> metis_tac[]) >>
  `nm = name` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_name] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)` by
    metis_tac[optionTheory.SOME_11] >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >>
     drule lower_dload_function_supply_labels >> gvs[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     `o1_fn_shape C fn` by metis_tac[] >>
     drule o1_fn_shape_components >> simp[]) >>
  `lbl = lb` by metis_tac[optionTheory.SOME_11] >>
  irule ld_owned_root_coverage >>
  goal_assum (drule_at Any) >> simp[] >> gvs[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "stage ambient boundary has hypotheses")
  [ld_stage_ambient, ld_stage_root_coverage];
