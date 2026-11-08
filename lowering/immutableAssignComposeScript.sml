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
  emitHelper venomInst valueEncodingProps immutableDeployStoreLength
  immutableDeployOperandTransfer immutableAssignNormalizeFrame stmtSimDeclCompose
  exprOperandVar placeStoreAllocPath exprSimBufferStore loweringHalt stmtLoweringMono fragExec fragGasMode
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

Theorem immutable_assign_direct_stmt_post:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty da bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  (ity = sty \/ (is_bytestring_type ity /\ is_bytestring_type sty)) /\
  copy_size = (if is_bytestring_type ity then type_memory_bytes ce sty else bytes) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  32*n <= type_memory_size itv /\
  value_has_type itv v /\ value_has_type stv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k /\
  k <= 32*n /\ a+k < dimword (:256) /\ off+32*n < dimword (:256) /\
  (a+k <= off \/ off+32*n <= a) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!x. region = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (n2w a) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule immutable_assign_direct_store >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ity = _`)) >>
  disch_then (drule_at (Pat `ce.ce_imm_alloca = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ity = _`)) >>
  disch_then (qspecl_then [`n`,`k`,`ctx`,`copy_size`,`off`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `compile_imm_store_words (SOME region) op (Lit (n2w off)) n 0 su = ((),sb)` by
    (qpat_x_assum `n = _` (fn th => rewrite_tac[th]) >>
     irule immutable_store_suffix_words >>
     fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     gvs[comp_return_def]) >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    metis_tac[immutable_store_words_memory_length] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  irule immutable_assign_suffix_stmt_post >> simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  qexistsl_tac [`env`,`id`,`itv`,`ity`,`off`,`v`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[regions_disjoint_def] >>
      disj2_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `off + type_memory_size itv` >>
      simp[arithmeticTheory.LESS_EQ_MONO_ADD_EQ, arithmeticTheory.ADD_COMM]) >>
  metis_tac[evaluated_immutable_admissible]
QED

Theorem immutable_assign_normalized_stmt_post:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty da L su = ((),sb) /\
  ity <> sty /\ ~is_bytestring_type ity /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
  local_ptrs_reserved ce su /\ (!x. op = Var x ==> not_fresh_at su x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty ity /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  value_has_type stv v /\ value_has_type itv v /\ val_wf stv v /\ val_wf itv v /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas su.cs_next_id = SOME (b,sz) ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region /\
  (!x. region = Var x ==> not_fresh_at su x) /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  L = type_memory_size itv /\ L = 32*n /\ 0 < L /\ off+L < dimword (:256) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~(is_bytestring_type ity /\ is_bytestring_type sty)` by simp[] >>
  drule_all immutable_assign_normalized_compile >> strip_tac >>
  `cs_extends su mid /\ ci_mono su mid` by
    metis_tac[compile_alloc_buffer_extends, ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `cs_extends mid sm /\ ci_mono mid sm` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode buf.buf_operand F loc ity ity da L sm = ((),sb)` by
    (simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     qpat_x_assum `(if _ then _ else _) sm = _` mp_tac >> simp[]) >>
  `cs_extends sm sb` by metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code su sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `compile_alloc_buffer (type_memory_size itv) su = (buf,mid)` by metis_tac[] >>
  drule immutable_assign_normalize_prefix >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspec_then `get_tenv cx` mp_tac) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  `ci_mono su sm` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> fs[ci_mono_def]) >>
  `!x. region = Var x ==> not_fresh_at sm x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (drule compile_alloc_buffer_parts >> strip_tac >> simp[] >>
     irule compiler_ci_mono_not_fresh >> qexists_tac `mid` >> simp[]) >>
  `regions_disjoint off L (w2n pw) L` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ s` kall_tac >>
     drule_all immutable_assign_declared_region >> strip_tac >>
     first_x_assum (qspecl_then [`su.cs_next_id`,`w2n pw`,`type_memory_size itv`] mp_tac) >>
     simp[regions_disjoint_def]) >>
  `n = (if L <= 32 then 1 else (L+31) DIV 32)` by
    (Cases_on `L <= 32` >- (fs[] >> decide_tac) >>
     qpat_assum `L = 32*n` (fn th => rewrite_tac[th]) >>
     simp[arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_DIV_ADD_DIV]) >>
  qpat_assum `compile_assign_value _ _ _ buf.buf_operand _ _ ity ity _ _ _ = _`
    (mp_then Any mp_tac immutable_assign_direct_stmt_post) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ r`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ r.vs_memory`)) >>
  disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP env.bare_globals _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ity = _`)) >>
  disch_then (drule_at (Pat `ce.ce_imm_alloca = _`)) >>
  disch_then (qspecl_then [`n`,`lctx`,`L`,`L`] mp_tac) >>
  (impl_tac >- (qpat_x_assum `n = if _ then _ else _` kall_tac >>
    simp[] >> conj_tac >- metis_tac[val_footprint_le] >>
    fs[regions_disjoint_def])) >> strip_tac >>
  qexists_tac `q` >> conj_tac
  >- (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
      qexists_tac `r` >> simp[]) >>
  irule stmt_post_entry_frame >>
  qexistsl_tac [`ee`,`r`,`sm`] >>
  qpat_x_assum `n = if _ then _ else _` kall_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule compiler_ci_mono_not_fresh >>
      qexists_tac `su` >> simp[]) >>
  fs[ci_mono_def]
QED
