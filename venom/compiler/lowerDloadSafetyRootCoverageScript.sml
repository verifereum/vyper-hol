(* Actual target roots establish the correlated owned coverage witness. *)
Theory lowerDloadSafetyRootCoverage
Ancestors
  lowerDloadSafetyEntry lowerDloadSafetyOwnedLocations lowerDloadSafetyOwnership
  lowerDloadConfiguredOrigins lowerDloadSafetyOrdinaryCoverage
  lowerDloadSafetyRelation lowerDloadSafetyLocations o1PassContract
  lowerDloadDefs venomInst venomState ptrDiscipline finite_map list
  contextCodegenRel o1ContractLowerDload

Theorem ld_active_zero_origin:
  lower_dload_function_supply u fn = (fn',v) /\
  s.vs_inst_idx = 0 /\ active_inst fn' ti s ==>
  ?inst. active_inst fn inst s
Proof
  strip_tac >>
  `LENGTH fn'.fn_blocks = LENGTH fn.fn_blocks` by
    (drule lower_dload_function_supply_labels >>
     simp[fn_labels_def] >> metis_tac[LENGTH_MAP]) >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def, MEM_EL] >> strip_tac >>
  rename1 `bb = EL j fn'.fn_blocks` >>
  `j < LENGTH fn.fn_blocks` by metis_tac[] >>
  drule_all lower_dload_function_supply_block_at >> strip_tac >>
  gvs[] >>
  qexists_tac `EL (LENGTH pre) fn.fn_blocks` >> simp[] >>
  conj_tac >- (simp[MEM_EL] >> qexists_tac `LENGTH pre` >> simp[]) >>
  Cases_on `(EL (LENGTH pre) fn.fn_blocks).bb_instructions` >>
  gvs[lower_dload_insts_supply_def]
QED

Theorem ld_owned_root_coverage:
  o1_run_state_ok vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn) /\
  enters_block fn'
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst fn' ti t ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
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
  Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >> gvs[] >>
  `enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t` by
    (irule lower_dload_function_supply_enters_block_origin >> metis_tac[]) >>
  `t = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `t.vs_inst_idx = 0` by simp[] >>
  `?inst. active_inst fn inst t` by
    (irule ld_active_zero_origin >> metis_tac[]) >>
  drule_all ld_sync_entry >>
  disch_then (qspecl_then [`Sigma fn.fn_name`,`lo`] strip_assume_tac) >>
  irule ld_owned_pair_zero >>
  conj_tac >- simp[] >>
  qexistsl_tac [`FEMPTY`,`FEMPTY`,`1`,`[]`,`f`,`fn`,`[]`,`inst`,`t`,`[]`,`entry_taint`] >>
  simp[ld_image_def] >> rpt strip_tac >> gvs[]
QED
