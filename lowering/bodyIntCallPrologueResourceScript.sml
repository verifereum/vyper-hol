(* Resource projections at the public internal-prologue stage boundaries. *)
Theory bodyIntCallPrologueResource
Ancestors
  intCallCallee bodyIntCallResourceSpans bodyIntCallWriteAuthorization
  exprLoweringProps compileEnv venomState venomExecSemantics
  context list rich_list finite_map words arithmetic
Libs
  monadsyntax

Theorem internal_scratch_materialization_inv:
  (case ret_type of
     SOME ty => if alloc_ce.ce_returns_count > 0 then
                  do compile_alloc_buffer (type_memory_bytes alloc_ce ty);
                     return () od
                else return ()
   | NONE => return ()) st = ((),st') /\
  mat_inv func ce env st s lo mr /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  fn_inst_ids_distinct func ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      mat_inv func ce env st' t lo mr /\ mat_frame st s t
Proof
  strip_tac >>
  drule_at (Pat `mat_inv _ _ _ _ _ _ _`) (iffLR mat_inv_def) >>
  strip_tac >>
  drule_all internal_scratch_run >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  simp[mat_inv_def] >> rpt conj_tac >> rpt strip_tac
  >- (first_x_assum drule >> strip_tac >> metis_tac[]) 
  >- metis_tac[LESS_EQ_TRANS]
  >> first_x_assum drule >> metis_tac[]
QED

(* Provenance is retained through the scratch allocation as well as the
   parameter materialization.  The memory-parameter map is exposed, so
   consumers can instantiate any staging-region predicate. *)
Theorem internal_prologue_resource_run:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) ==>
  ?t mr.
    run_inst_seq (emitted_insts st0 st1) s0 = OK t /\
    mat_inv func ce2 env st1 t caller.vs_alloca_next mr /\
    mat_frame st0 s0 t /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >> drule internal_prologue_stages >> strip_tac >>
  drule_all internal_prologue_stage_shapes >> strip_tac >>
  rename1 `materialize_internal_params stage_ce caps sc = (ce2,sm)` >>
  `stage_ce.ce_vars = ce.ce_vars` by simp[] >>
  `internal_stack_size stage_ce params = internal_stack_size ce params` by
    (irule internal_stack_size_vars >> simp[]) >>
  qpat_x_assum `stage_ce = _` (mk_asm "stage_ce") >>
  drule_all internal_capture_materialization_entry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 sc) s0 = OK captured` >>
  drule_all internal_prologue_segment_members >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `ALL_DISTINCT (MAP FST caps)` by fs[internal_args_rel_def] >>
  `captured.vs_alloca_next = caller.vs_alloca_next` by
    (qpat_x_assum `captured = s0 with vs_vars := _` SUBST1_TAC >>
     drule setup_callee_frontier >> simp[]) >>
  `captured.vs_alloca_next +
     internal_stack_size stage_ce (MAP (\c. (FST c,FST (SND c))) caps)
       < dimword (:256)` by simp[] >>
  `!i. MEM i (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts) ==>
    MEM i (fn_insts func)` by fs[emitted_insts_def] >>
  drule_all materialize_run_compact >> strip_tac >>
  rename1 `mat_inv func ce2 env sm materialized _ _` >>
  `run_inst_seq (emitted_insts sc sm) captured = OK materialized` by
    fs[emitted_insts_def] >>
  drule_all internal_scratch_materialization_inv >> strip_tac >>
  rename1 `mat_inv func ce2 env st1 landing _ _` >>
  qexistsl_tac [`landing`, `mr`] >> simp[] >>
  conj_tac >- suspend "sequence" >>
  `mat_frame sc captured landing` by
    (irule mat_frame_trans >> goal_assum (drule_at Any) >>
     simp[] >> fs[not_fresh_at_def]) >>
  irule mat_frame_trans >> goal_assum (drule_at Any) >>
  simp[] >> fs[not_fresh_at_def]
QED

Resume internal_prologue_resource_run[sequence]:
  `emitted_insts st0 st1 =
    emitted_insts st0 sc ++ emitted_insts sc sm ++ emitted_insts sm st1` by
    (qpat_x_assum `isPREFIX st0.cs_current_insts sc.cs_current_insts` mp_tac >>
     qpat_x_assum `isPREFIX sc.cs_current_insts sm.cs_current_insts` mp_tac >>
     qpat_x_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[IS_PREFIX_APPEND] >> rpt strip_tac >>
     `sc.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 sc` by
       simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     `sm.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sm` by
       (qpat_assum `sm.cs_current_insts = sc.cs_current_insts ++ l'` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
     `st1.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm st1` by
       (qpat_assum `st1.cs_current_insts = sm.cs_current_insts ++ l` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
     metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  qpat_x_assum `emitted_insts st0 st1 = _` SUBST1_TAC >>
  qpat_x_assum `run_inst_seq (emitted_insts st0 sc) s0 = OK captured` mp_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sc sm) captured = OK materialized` mp_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sm st1) materialized = OK landing` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  metis_tac[exprLoweringPropsTheory.run_inst_seq_append, listTheory.APPEND_ASSOC]
QED

Finalise internal_prologue_resource_run

(* Attach resources to a landing already chosen by the semantic prologue
   theorem.  Determinism here is of the fixed instruction sequence, not
   uniqueness of arbitrary normal gas paths. *)
Theorem internal_prologue_landing_resources:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK t ==>
  ?mr. mat_inv func ce2 env st1 t caller.vs_alloca_next mr /\
    mat_frame st0 s0 t /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >> drule_all internal_prologue_resource_run >>
  strip_tac >> gvs[] >> qexists_tac `mr` >> simp[]
QED

Theorem internal_prologue_protected_landing:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK t /\
  (!a k. P a k ==> a + k <= caller.vs_alloca_next) /\
  (!a k. P a k ==>
    mem_bytes_at a k s0.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) ==>
  mat_frame st0 s0 t /\
  (!a k. P a k ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region ce2 [env] t n p k ==>
    caller.vs_alloca_next <= p \/
    ?b z. staged b z /\ b <= p /\ p + k <= b + z)
Proof
  strip_tac >> drule_all internal_prologue_landing_resources >> strip_tac >>
  simp[] >> conj_tac
  >- (drule setup_callee_frontier >> strip_tac >>
      qpat_x_assum `mat_frame st0 s0 t` mp_tac >>
      simp[mat_frame_def] >> metis_tac[]) >>
  fs[mat_inv_def] >>
  qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
  qpat_x_assum `!i off sz. _ ==> ?b z. staged _ _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >- simp[] >>
  disj2_tac >> gvs[] >> metis_tac[]
QED
