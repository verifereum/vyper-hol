(* Ordinary immutable assignment: source continuation and statement boundary. *)
Theory immutableAssignCompose
Ancestors
  immutableAssignReadiness immutableAssignMetadata immutableAssignStore
  immutableDeployAssignRestore immutableDeployAssignSourceFrame
  bodyImmutableAugAssignStore bodyImmutableAugAssignExec
  exprSimSource exprSimHypsDefs exprSimMemorySource vyperInterpreter vyperState
  vyperTypeInvariants vyperTypeEnv stmtSimProps venomState vyperPlaceFrames
  loweringPosts stmtSimDefs compileEnv immutableDeployAssignFacts exprLoweringProps
  immutableDeployAssignAdmissible venomMemProps exprSimProps context stmtLowering
  emitHelper venomInst valueEncodingProps
Libs monadsyntax

Theorem immutable_assign_read_source:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ity = SOME itv ==>
  ?fin. write_place cx (ImmutablePlace src id []) v ee = (INL (),fin) /\
    expr_sim_inv ce cx env ee /\
    !tail. (do p <- eval_target_place cx (TopLevelNameTarget (src,id));
               w <- read_result cx tv; write_place cx p w od)
      (ee with gas_obs := tail) = (INL (),fin with gas_obs := tail)
Proof
  strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  drule_all immutable_assign_source_lookup >> strip_tac >>
  drule_all immutable_augassign_write_source >>
  disch_then (qspec_then `v` assume_tac) >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),fin)` >>
  qexists_tac `fin` >> simp[] >> gen_tac >>
  `env_consistent env cx ee` by fs[expr_sim_inv_def] >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  drule_all immutable_augassign_prefix_obs >>
  disch_then (qspec_then `tail` strip_assume_tac) >>
  drule read_result_gas_obs >>
  disch_then (qspec_then `tail` assume_tac) >>
  drule immutable_write_place_gas_obs >>
  disch_then (qspec_then `tail` assume_tac) >>
  gvs[bind_def]
QED

(* The declared immutable region is disjoint from every live allocation,
   including allocations made by normalization before this suffix. *)
Theorem immutable_assign_suffix_alloca_frame:
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce su /\
  ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  fin.scopes = ee.scopes /\
  (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s) /\
  (!a k. regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  alloca_frame ce ee su s ce fin q
Proof
  strip_tac >> drule_all immutable_assign_declared_region >> strip_tac >>
  irule alloca_frame_of_mem_frame >> simp[] >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  first_x_assum irule >> fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem immutable_assign_suffix_stmt_post:
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  immutable_value_admissible itv v /\ val_in_memory itv v off q.vs_memory /\
  immutable_value_bytes_rel itv v (mem_bytes_at off (type_memory_size itv) q.vs_memory) /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!a k. regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
  ~block_is_terminated sb ==>
  stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin
    (q with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx fin q` by
    (irule immutable_store_stmt_state_rel >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `fin.scopes = ee.scopes` by
    metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `alloca_frame ce ee su s ce fin q` by
    (irule immutable_assign_suffix_alloca_frame >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality] >>
  strip_tac >> gvs[lookup_var_def] >>
  irule alloca_frame_same_state >> goal_assum (drule_at Any) >> simp[]
QED

Theorem immutable_assign_word_stmt_post:
  compile_assign_value ce (Lit (n2w off)) LocCode op T loc ity sty da bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ is_word_type ity /\
  value_has_type itv v /\ off < dimword (:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (typed_val_to_w256 itv v) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q
Proof
  strip_tac >>
  `eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `type_memory_size itv = 32` by metis_tac[word_tv_memory_size] >>
  `same_blocks su sb` by
    (`compile_imm_store_word (SOME region) (Lit (n2w off)) op su = ((),sb)` by
      fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def, emit_op_def, emit_void_def,
          fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[same_blocks_def]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  irule immutable_assign_suffix_stmt_post >>
  simp[LENGTH_mstore_eq, lookup_var_def] >>
  conj_tac >- fs[same_blocks_def] >>
  qexistsl_tac [`env`,`id`,`itv`,`ity`,`off`,`v`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
      fs[regions_disjoint_def] >> decide_tac) >>
  metis_tac[evaluated_immutable_admissible]
QED
