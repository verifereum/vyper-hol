(* Replay boundary for body-aware counted aggregate children. *)
Theory exprSimAggregateBodyCounted
Ancestors
  exprSimAggregateChildren exprSimAggregateLoops exprSimSource
  gasSummary fragGasMode fragGasPath vyperInterpreter vyperState exprSimHypsDefs
  exprSimHyps exprSimUnwrap exprSimUnwrapProps exprSimMemoryRead
  exprLoweringProps loweringPosts compileEnv
Libs
  monadsyntax

Theorem aggregate_body_marked_replay:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res mid r ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (res,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem aggregate_body_marked_read_replay:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])
Proof
  strip_tac >> drule aggregate_body_marked_replay >> strip_tac >>
  simp[bind_def]
QED

(* Metadata required by the recursive counted typed-copy interface. *)
Theorem aggregate_body_copy_metadata:
  expr_body_pre ce cx env e es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields)
Proof
  strip_tac >> gvs[expr_body_pre_def, expr_sim_inv_def] >>
  first_assum ACCEPT_TAC
QED

Theorem unwrap_value_body_rebased_path:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  drule vv_post_rebase >>
  disch_then assume_tac >>
  `vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' (Value v) vv r` by metis_tac[vv_post_read_result] >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (mp_tac unwrap_value_path >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`su`, `op`] mp_tac) >>
      impl_tac
      >- (simp[] >> conj_tac
          >- (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
          rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
      strip_tac >> qexists_tac `u` >>
      gvs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
      qexists_tac `r` >> simp[gas_marked_path_def, gas_path_rules] >>
      drule expr_post_of_vv_post_stack >> simp[]) >>
  `p.ptr_location = LocMemory` by metis_tac[] >>
  Cases_on `is_word_type t`
  >- (mp_tac (GEN_ALL unwrap_memory_marked_read) >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`su`, `op`] mp_tac) >>
      impl_tac
      >- (simp[] >> gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
          metis_tac[]) >>
      strip_tac >>
      gvs[gas_marked_exec_def, read_result_def, return_def] >>
      qexists_tac `u` >> simp[] >>
      metis_tac[gas_marked_path_def, gas_path_normal]) >>
  gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `r` >> simp[gas_marked_path_def, gas_path_rules] >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]
QED
