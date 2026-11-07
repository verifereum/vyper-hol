(* Counted source boundary for body-aware aggregate child stores. *)
Theory exprSimAggregateBodyCountedChildren
Ancestors
  exprSimAggregateChildren exprSimSource gasSummary vyperState exprSimHypsDefs
  exprSimUnwrap aggregateCountedStraightExec exprSimAbiGasBridge
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringPosts venomInst list rich_list exprSimHash exprLowering fragExec venomState fragGasPath fragGasMode
Libs
  monadsyntax

(* A marked execution replays at the explicit observations selected by its
   target path.  It need not replay at the original state's observations. *)
Theorem aggregate_body_marked_read_source:
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  gvs[] >> simp[bind_def]
QED

Theorem aggregate_body_pre_gas_obs:
  expr_body_pre ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre ce cx env e es
Proof
  simp[expr_body_pre_def, expr_sim_inv_gas_obs]
QED

Theorem aggregate_unwrap_memory_straight[local]:
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  unwrap_value ce vv sm = (op,su) ==>
  cs_extends sm su /\ sm.cs_blocks = su.cs_blocks /\
  frag_ops_free sm su /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sm su)
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >> strip_tac
  >- (gvs[comp_return_def] >>
      simp[cs_extends_refl, frag_ops_free_def, frag_code_def,
           emitted_blocks_def, emitted_insts_def]) >>
  gvs[compile_ptr_load_def] >>
  Cases_on `is_word_type t` >> gvs[comp_return_def] >>
  simp[cs_extends_refl, frag_ops_free_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def,
      emit_def, mk_inst_def, cs_extends_def, frag_ops_free_def,
      frag_code_def, emitted_blocks_def, emitted_insts_def, is_terminator_def,
      DROP_LENGTH_APPEND]
QED

Theorem aggregate_expr_post_returndata[local]:
  expr_post ctx func ce cx e es sa sb s0 es' v op
    (s with vs_returndata := rd) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  Cases_on `op` >>
  simp[expr_post_def, hash_returndata_state_rel, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, eval_operand_def, lookup_var_def,
       local_region_def, local_backed_def, locals_kept_def]
QED

Theorem aggregate_body_unwrap_marked:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "equal" >>
  `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  drule_all aggregate_unwrap_memory_straight >> strip_tac >>
  drule_all unwrap_value_body_rebased_sim >>
  disch_then (qspec_then `\r. F` assume_tac) >>
  ho_match_mp_tac frag_exec_same_block_gas_path >>
  qexists_tac `sm` >> goal_assum (drule_at Any) >>
  simp[aggregate_expr_post_returndata]
QED

Resume aggregate_body_unwrap_marked[equal]:
  drule vv_post_rebase >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> (impl_tac
  >- (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[])) >>
  strip_tac >> gvs[gas_marked_exec_def] >>
  qpat_x_assum `!tail. read_result _ _ _ = _`
    (qspec_then `es'.gas_obs` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  drule gas_marked_path_exec >> strip_tac >>
  drule gas_path_normal >> strip_tac >>
  qexists_tac `u` >> simp[]
QED

Finalise aggregate_body_unwrap_marked
