Theory bodyFullAssignImmutableEmpty
Ancestors
  vfmBuffer[qualified,ignore_grammar]
  ctorDeployDeadSection immSectionDead valueEncodingDefs valueEncodingProps
  valueEncodingProofs abiEncoderMemory cv_std byte words divides arithmetic list
  ptrDiscipline context emitHelper fragExec
  venomState venomInst venomExecSemantics loweringStateRelDefs
  string ASCIInumbers rich_list pred_set
  bodyFullMemoryFrames bodyPtrBytestringBuiltinsWindowGhost vyperPlaceFrames
  stmtSimAugAssignPlaceMemory vyperPlaceWriteSoundness
  immutableAssignEmpty immutableDeployAssignRestore immutableDeployAssignMemoryFrame
  exprSimProps alist compileEnv exprLoweringProps
  bodySim bodyInvCodeProps bodyStorageMetadata immutableRelation
  ctorDeployDeadSectionFrame compileVyper venomMemProps stateRelProj
  bodyPtrDefs stmtSimDefs vyperState vyperTyping vyperTypeEnv vyperTypeValues
  exprSimHypsDefs vyperContext finite_map


Theorem num_of_bytes_mono[local]:
  !xs ys. LIST_REL (\x y. w2n x <= w2n y) xs ys ==>
    num_of_bytes xs <= num_of_bytes ys
Proof
  Induct >> Cases_on `ys` >> simp[num_of_bytes_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem mem_word_at_bytewise_mono[local]:
  LIST_REL (\x y. w2n x <= w2n y) (mem_bytes_at a 32 sec') (mem_bytes_at a 32 sec) ==>
  w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)
Proof
  strip_tac >>
  drule LIST_REL_REVERSE >>
  disch_then (assume_tac o MATCH_MP num_of_bytes_mono) >>
  `!m. num_of_bytes (REVERSE (mem_bytes_at a 32 m)) < dimword (:256)` by
    (gen_tac >> mp_tac (Q.SPEC `REVERSE (mem_bytes_at a 32 m)` vfmBufferTheory.num_of_bytes_lt) >>
     simp[dimword_def]) >>
  `!m. mem_word_at a m = word_of_bytes_be (mem_bytes_at a 32 m)` by
    simp[mem_word_at_def, mem_bytes_at_def, word_of_bytes_be_def] >>
  asm_rewrite_tac[] >>
  simp[word_of_bytes_be_eq_num_of_bytes, dividesTheory.compute_divides,
       be_bytes_thm, TAKE_APPEND1, TAKE_LENGTH_ID_rwt, w2n_n2w_compute]
QED

(* Decreasing length words can only make more bytes dead. *)
Theorem mem_dead_bytes_lengths_decrease[local]:
  (!sec off tv i. mem_dead_bytes sec off tv i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes sec' off tv i) /\
  (!sec off tvs i. mem_dead_bytes_list sec off tvs i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes_list sec' off tvs i) /\
  (!sec off fields i. mem_dead_bytes_fields sec off fields i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes_fields sec' off fields i)
Proof
  ho_match_mp_tac mem_dead_bytes_ind >>
  simp[mem_dead_bytes_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `off` assume_tac) >> decide_tac)
  >- (first_x_assum (qspec_then `off` assume_tac) >> decide_tac)
  >- (qexists_tac `k` >> simp[] >> metis_tac[])
  >- (qexists_tac `k` >> simp[] >>
      qpat_assum `!a. w2n (mem_word_at a sec') <= _`
        (qspec_then `off` assume_tac) >>
      Cases_on `k < w2n (mem_word_at off sec')`
      >- (`k < w2n (mem_word_at off sec)` by decide_tac >>
          fs[] >> metis_tac[]) >>
      Cases_on `k < w2n (mem_word_at off sec)` >> fs[] >>
      drule (cj 1 mem_dead_bytes_range) >>
      simp[ADD1, LEFT_ADD_DISTRIB] >> decide_tac)
  >> metis_tac[]
QED

Theorem imm_section_dead_lengths_decrease:
  (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) /\
  imm_section_dead tops sec i ==>
  imm_section_dead tops sec' i
Proof
  simp[imm_section_dead_def] >>
  metis_tac[cj 1 mem_dead_bytes_lengths_decrease]
QED

Theorem imm_section_dead_mstore_zero:
  imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) i ==>
  imm_section_dead tops (mem_bytes_at 0 lo (mstore p 0w s).vs_memory) i
Proof
  strip_tac >> irule imm_section_dead_lengths_decrease >>
  goal_assum (drule_at Any) >> gen_tac >>
  irule mem_word_at_bytewise_mono >>
  simp[LIST_REL_EL_EQN] >> qx_gen_tac `j` >> strip_tac >>
  `!m. EL j (mem_bytes_at a 32 (mem_bytes_at 0 lo m)) =
      if a+j < lo then EL (a+j) (mem_bytes_at 0 lo m) else 0w` by
    metis_tac[EL_mem_bytes_at, LENGTH_mem_bytes_at] >>
  Cases_on `a+j < lo` >> asm_rewrite_tac[] >> simp[] >>
  `!m. EL (a+j) (mem_bytes_at 0 lo m) = EL 0 (mem_bytes_at (a+j) 1 m)` by
    simp[EL_mem_bytes_at] >>
  asm_rewrite_tac[] >>
  Cases_on `p <= a+j /\ a+j < p+32`
  >- (`a+j-p + 1 <= 32` by decide_tac >>
      drule abi_encoder_zero_subwindow >>
      disch_then (qspecl_then [`s`, `p`] mp_tac) >>
      `p+(a+j-p) = a+j` by decide_tac >>
      `REPLICATE 1 (0w:byte) = [0w]` by EVAL_TAC >>
      asm_rewrite_tac[] >> simp[w2n_n2w]) >>
  `a+j+1 <= p \/ p+32 <= a+j` by decide_tac >>
  simp[mstore_mem_bytes_at_disjoint]
QED

Theorem immutable_empty_store_ghost:
  ghost_inv_at D lo d ce cx es G tn s /\
  dead_lo_ok H D lo ce cx /\ ce.ce_is_ctor /\
  body_inv tops ctx ce cx /\
  expr_sim_inv ce cx env es /\ stmt_state_rel H ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  ee.scopes = es.scopes /\ off+32 <= lo /\
  q.vs_memory = (mstore off 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_mem SUBSET tn.t_mem ==>
  ghost_inv_at D lo d ce cx ee Gf tf q
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> Cases_on `len = 0` >- simp[mem_bytes_at_def] >>
     `0 < len` by decide_tac >>
     `lo <= b` by (drule_all body_full_local_region_lower_bound >> simp[]) >>
     `off+32 <= b` by decide_tac >>
     simp[] >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
     ptr_covers Gf tf x q sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  `q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _;
       vs_immutables := _; vs_prev_bb := _; vs_current_bb := _;
       vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- suspend "locals"
  >- suspend "return"
  >- fs[stor_taint_ok_at_def, dead_lo_ok_def]
  >- (rpt strip_tac >> irule imm_section_dead_mstore_zero >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- metis_tac[local_ptrs_reserved_def]
  >> gvs[allocas_from_def] >> metis_tac[]
QED

Resume immutable_empty_store_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz` by metis_tac[] >>
  `?w0. lookup_var p s = SOME w0` by fs[ptr_covers_def] >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  `mem_bytes_at (w2n w) sz q.vs_memory =
   mem_bytes_at (w2n w) sz s.vs_memory` by metis_tac[] >>
  `!i. w2n w <= i /\ i < w2n w+sz /\ i IN tf.t_mem ==>
       i IN tn.t_mem` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  irule robust_val_in_memory_window_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`sz`,`s.vs_memory`,`q.vs_memory`] >>
  gvs[] >> metis_tac[]
QED

Resume immutable_empty_store_ghost[return]:
  Cases_on `d` >> fs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  fs[return_buf_ptr_def] >> metis_tac[]
QED

Finalise immutable_empty_store_ghost

Theorem immutable_nested_write_as_root:
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,iv) /\
  evaluate_subscripts itv iv path = INL old /\
  write_place cx (ImmutablePlace src id path) v es = (wr,ee) /\
  stmt_res_ok lctx wr ==>
  wr = INL () /\
  ?new. assign_subscripts itv iv path (Replace v) = INL new /\
        write_place cx (ImmutablePlace src id []) new es = (INL (),ee)
Proof
  strip_tac >>
  `get_immutables cx src es = (INL (get_source_immutables src imms),es)` by
    simp[get_immutables_def, get_address_immutables_def,
         lift_option_type_def, bind_def, vyperStateTheory.return_def] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `assign_subscripts itv iv path (Replace v)` >>
  simp[assign_subscripts_def, lift_sum_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def]
  >- (strip_tac >> drule_all set_immutable_success_from_get >> simp[]) >>
  strip_tac >> drule_all aug_place_replace_read_error >>
  strip_tac >> gvs[stmt_res_ok_def]
QED

Theorem immutable_root_span:
  body_inv tops ctx ce cx /\ struct_args_unique tops /\
  ce.ce_is_ctor /\ dead_lo_ok H D lo ce cx /\
  FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (NONE,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  off + type_memory_size tv <= lo
Proof
  strip_tac >>
  drule body_inv_immutable_section_layout >>
  rewrite_tac[immutable_section_layout_def] >> strip_tac >>
  first_x_assum drule >>
  disch_then (qx_choosel_then [`pre`,`post`,`vis`,`ty'`,`slot`] strip_assume_tac) >>
  `MEM (VariableDecl vis Immutable id ty' slot) tops` by simp[] >>
  qpat_assum `body_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `ty' = ty` by
    (drule_all build_maps_variable >> strip_tac >>
     qpat_assum `!i. ce.ce_module_var_type _ = _`
       (qspec_then `id` mp_tac) >>
     gvs[optionTheory.SOME_11]) >>
  qpat_x_assum `ty' = ty` SUBST_ALL_TAC >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv` by metis_tac[imm_frame_size] >>
  `cx_tops cx = tops` by metis_tac[body_inv_main_code] >>
  `lo = imm_len tops` by fs[dead_lo_ok_def] >>
  qpat_assum `lo = imm_len _` SUBST1_TAC >>
  rewrite_tac[imm_len_def] >>
  qpat_assum `off = _` SUBST1_TAC >>
  qpat_assum `type_mem_bytes _ _ = _` (SUBST1_TAC o SYM) >>
  qpat_assum `tops = _` SUBST1_TAC >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`off` |-> `0`] (SPEC_ALL immutable_declaration_interval_bound)))
QED

Theorem immutable_empty_path_store_restore:
  stmt_state_rel H ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME root_ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) root_ty = SOME itv /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv iv path (Replace (default_value ptv)) = INL new /\
  write_place cx (ImmutablePlace ce.ce_module id []) new es = (INL (),ee) /\
  has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  q.vs_memory = (mstore (off+k) 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
  stmt_state_rel H ctx func ce cx ee q
Proof
  strip_tac >>
  `val_in_memory itv iv off s.vs_memory` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s`
       (mp_tac o MATCH_MP state_rel_immutables_rel o MATCH_MP stmt_state_rel_state_rel) >>
     simp[immutables_rel_def] >> metis_tac[]) >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
  drule_all imms_well_typed_get_source_immutables >> strip_tac >>
  `mem_word_at (off+k) q.vs_memory = 0w` by simp[mstore_mem_word_at_same] >>
  drule_all immutable_assign_empty_representation >> strip_tac >>
  `value_has_type ptv (default_value ptv)` by
    metis_tac[default_value_well_typed,evaluate_type_well_formed_type_value] >>
  drule_all mem_path_offset_sound >> strip_tac >>
  `!b n. off <= b /\ b+n <= off+type_memory_size itv /\
      (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
      mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  drule_all immutable_value_bytes_rel_replace_path >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by simp[LENGTH_mstore_eq] >>
  `!a n. regions_disjoint a n off (type_memory_size itv) ==>
      mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule immutable_store_stmt_state_rel >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`env`,`es`,`id`,`off`,`s`,`sa`,`ce.ce_module`,`itv`,`root_ty`,`new`] >>
  simp[]
QED
