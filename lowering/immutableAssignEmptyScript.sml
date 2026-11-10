(* Empty length-word immutable assignments do not evaluate an RHS fragment. *)
Theory immutableAssignEmpty
Ancestors
  immutableAssignCode immutableAssignMetadata immutableDeployAssignRestore
  immutableDeployAssignWord immutableDeployAssignBytes immutableDeployAssignAdmissible
  memoryLocalRhsProps stmtSimDeclMem valueEncodingProps vyperTyping vyperTypeValues
  exprSimHypsDefs vyperTypeInvariants vyperTypeEnv
  venomState finite_map exprSimSource vyperInterpreter vyperState
  bodyImmutableAugAssignStore bodyImmutableAugAssignExec immutableDeployAssignSourceFrame
  alist immutableDeployOperandTransfer immutableCopyExecution venomMemProps
  placeTypedCopyPath exprLoweringProps compileEnv loweringStateRelDefs stmtSimProps valueEncoding
  stmtLoweringMono stmtLowering context emitHelper venomInst
  immutableDeployAssignFacts stmtSimDefs gasOutcome gasSummary loweringPosts

Theorem immutable_assign_empty_representation:
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  mem_word_at off mem = 0w ==>
  val_in_memory tv (default_value tv) off mem /\
  immutable_value_admissible tv (default_value tv) /\
  immutable_value_bytes_rel tv (default_value tv)
    (mem_bytes_at off (type_memory_size tv) mem) /\
  32 <= type_memory_size tv
Proof
  strip_tac >> drule_all memory_length_word_layout >> strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `immutable_value_admissible tv (default_value tv)` by
    metis_tac[default_immutable_admissible] >>
  simp[] >> irule immutable_memory_bytes >> simp[]
QED

Theorem immutable_assign_empty_read:
  expr_body_pre ce cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  !tail. (do r <- eval_expr cx e; read_result cx r od)
    (es with gas_obs := tail) =
    (INL (default_value tv), es with gas_obs := tail)
Proof
  strip_tac >> gen_tac >> irule memory_rhs_empty_read_destination >>
  simp[] >> qexistsl_tac [`env`, `ty`] >>
  gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def]
QED

Theorem immutable_assign_empty_source:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ty /\
  expr_body_pre ce cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?ee. write_place cx (ImmutablePlace src id []) (default_value tv) es =
         (INL (),ee) /\
    !tail. eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)
       (es with gas_obs := tail) = (INL (),ee with gas_obs := tail)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  drule_all immutable_assign_source_lookup >> strip_tac >>
  drule_all immutable_augassign_write_source >>
  disch_then (qspec_then `default_value tv` assume_tac) >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),ee)` >>
  qexists_tac `ee` >> simp[] >> gen_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := tail)` by simp[] >>
  `!r ee1. eval_expr cx e (es with gas_obs := tail) = (INL r,ee1) ==>
    eval_target_place cx (TopLevelNameTarget (src,id)) ee1 =
    (INL (ImmutablePlace src id []),ee1)` by
    (rpt strip_tac >> irule immutable_assign_rhs_target >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all immutable_assign_empty_read >>
  disch_then (qspec_then `tail` mp_tac) >>
  simp[Once evaluate_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := tail)` >>
  rename1 `_ = (rr,ee1)` >> Cases_on `rr` >>
  simp[bind_def] >>
  `eval_target_place cx (TopLevelNameTarget (src,id)) ee1 =
    (INL (ImmutablePlace src id []),ee1)` by metis_tac[] >>
  gvs[] >> strip_tac >> simp[] >>
  drule immutable_write_place_gas_obs >> simp[]
QED

Theorem immutable_assign_empty_store_restore:
  stmt_state_rel ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace ce.ce_module id []) (default_value tv) es = (INL (),ee) /\
  q.vs_memory = (mstore off 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
  stmt_state_rel ctx func ce cx ee q
Proof
  strip_tac >>
  `mem_word_at off q.vs_memory = 0w` by simp[mstore_mem_word_at_same] >>
  drule_all immutable_assign_empty_representation >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by simp[LENGTH_mstore_eq] >>
  `!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule immutable_store_stmt_state_rel >>
  metis_tac[]
QED

Theorem immutable_assign_empty_path:
  compile_store_at_loc imm (Lit (n2w off)) (Lit 0w) (SOME LocCode) sa = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  off < dimword (:256) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0
        (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    same_blocks sa sb /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    q.vs_memory = (mstore off 0w s).vs_memory /\
    ~block_is_terminated sb
Proof
  strip_tac >>
  `compile_imm_store_word imm (Lit (n2w off)) (Lit 0w) sa = ((),sb)` by
    fs[compile_store_at_loc_def] >>
  `?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    q.vs_memory = (mstore off 0w s).vs_memory` by
    (drule immutable_store_word_old_execution >>
     disch_then (qspecl_then [`0w`, `s`, `n2w off`] mp_tac) >>
     simp[eval_operand_def, wordsTheory.w2n_n2w] >> metis_tac[]) >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
   ~block_is_terminated sb` by
    (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     Cases_on `imm` >>
     simp[compile_imm_store_word_def, emit_void_def, emit_op_def,
          fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
     simp[same_blocks_def, emitted_insts_def, listTheory.DROP_APPEND,
          mk_inst_def, is_terminator_def, block_is_terminated_def] >>
     Cases_on `sa.cs_current_insts` >>
     simp[listTheory.LAST_CONS_cond, listTheory.LAST_APPEND_CONS,
          arithmeticTheory.SUB_PLUS, mk_inst_def, is_terminator_def]) >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `q` >> simp[]
QED

Theorem immutable_assign_header_alloca_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ 32 <= type_memory_size tv /\
  ee.scopes = es.scopes /\ q.vs_memory = (mstore off 0w s).vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
  alloca_frame ce es sa s ce ee q
Proof
  strip_tac >> drule_all immutable_assign_declared_region >> strip_tac >>
  irule alloca_frame_of_mem_frame >>
  simp[] >> reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >>
  `regions_disjoint off (type_memory_size tv) off' sz` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem immutable_assign_empty_stmt_frag:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_body_pre ce cx env e es /\ has_length_word (expr_type e) /\
  is_empty_value_expr e /\ type_widens_to env.type_defs (expr_type e) ity /\
  evaluate_type (get_tenv cx) ity = SOME tv ==>
  stmt_frag ctx func cx lctx RetQ ce
    (stmt_env ce lctx ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  drule_all immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >> gvs[] >>
  `has_length_word ity` by metis_tac[type_widens_to_has_length_word] >>
  drule_all immutable_assign_empty_source >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all immutable_assign_empty_code >> strip_tac >> gvs[] >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s0 = SOME 0w` by
    (fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def]) >>
  `off < dimword (:256)` by metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS,
    arithmeticTheory.LE_ADD] >>
  drule_all immutable_assign_empty_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `q.vs_prev_bb = s0.vs_prev_bb /\ q.vs_current_bb = s0.vs_current_bb /\
   q.vs_inst_idx = s0.vs_inst_idx /\ q.vs_halted = s0.vs_halted /\
   q.vs_allocas = s0.vs_allocas` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = _`
       mp_tac >> simp[venom_state_component_equality]) >>
  `stmt_state_rel ctx func ce cx ee q` by
    (irule immutable_assign_empty_store_restore >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`env`, `es`, `id`, `off`, `s0`, `sa`, `tv`, `ity`] >>
     simp[venom_state_component_equality] >>
     qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = _`
       mp_tac >> simp[venom_state_component_equality]) >>
  `ee.scopes = es.scopes` by
    metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `32 <= type_memory_size tv` by
    (qspec_then `get_tenv cx` mp_tac memory_length_word_layout >>
     disch_then (qspecl_then [`ity`, `tv`, `off`, `(mstore off 0w s0).vs_memory`] mp_tac) >>
     simp[mstore_mem_word_at_same]) >>
  `alloca_frame ce es sa s0 ce ee q` by
    (irule immutable_assign_header_alloca_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `ee`, `OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  disj1_tac >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx, same_blocks_def] >>
  gvs[same_blocks_def, lookup_var_def] >>
  irule alloca_frame_same_state >> goal_assum (drule_at Any) >> simp[]
QED
