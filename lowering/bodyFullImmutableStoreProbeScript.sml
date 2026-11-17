(* Constructor immutable stores, tested independently of bodyFullAssign. *)
Theory bodyFullImmutableStoreProbe
Ancestors
  bodyPtrDefs stmtSimDefs wordLoadStorePtr immutableDeployAssignRestore
  immutableDeployAssignAdmissible immutableDeployAssignFacts stmtSimDeclStore
  immutableDeployAssignBytes
  ctorDeployDeadSectionFrame ctorDeployDeadSection immSectionDead
  compileVyper compileEnv exprLoweringProps exprSimHypsDefs loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs
  venomState venomMemProps venomExecSemantics venomInstProofs venomInst
  codegenRel contextCodegenRel ptrDiscipline ptrSafeRun
  fragExec fragExecPtr emitHelper memLocDefs
  vyperState vyperPlaceFrames vyperContext vyperValue
  vyperTypeSystem vyperTyping vyperAST list finite_map pred_set arithmetic words

Theorem immutable_uint256_dead_frame_by_layout:
  (!ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
      type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size tv) /\
  tops = pre ++ VariableDecl vis Immutable name (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + 32) ==>
       EL j sec2 = EL j sec1) /\
  imm_section_dead tops sec1 i ==>
  imm_section_dead tops sec2 i
Proof
  strip_tac >>
  qpat_x_assum `imm_section_dead _ _ _`
    (mp_tac o REWRITE_RULE [imm_section_dead_def]) >>
  disch_then (qx_choosel_then [`pre2`, `vis2`, `name2`, `ty`, `slot2`, `post2`, `tv`]
    strip_assume_tac) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv` by metis_tac[] >>
  Q.SUBGOAL_THEN `pre = pre2 \/ off + 32 <=
      compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2 \/
    compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2 +
      type_memory_size tv <= off` assume_tac
  >-
    (`pre ++ VariableDecl vis Immutable name (BaseT (UintT 256)) slot :: post =
      pre2 ++ VariableDecl vis2 Immutable name2 ty slot2 :: post2` by metis_tac[] >>
     drule imm_frame_occurrence_separation >>
     disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
     simp[] >> gvs[type_mem_bytes_def]) >>
  Cases_on `pre = pre2`
  >- (gvs[] >> gvs[evaluate_type_def, mem_dead_bytes_def]) >> fs[] >>
  `mem_dead_bytes sec2
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2) tv =
   mem_dead_bytes sec1
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2) tv` by
    (irule mem_dead_bytes_frame >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> gvs[] >> decide_tac) >>
  simp[imm_section_dead_def] >>
  qexistsl_tac [`pre2`, `vis2`, `name2`, `ty`, `slot2`, `post2`, `tv`] >> gvs[]
QED

(* The extra dead-byte premise is discharged from the declaration layout
   for a word store; unlike ghost_inv_at_mstore_clean this permits off < lo. *)
Theorem immutable_istore_ghost:
  ghost_inv_at D lo d ce cx es G tn s /\
  local_ptrs_rel func ce es.scopes s /\ es'.scopes = es.scopes /\
  (!im. D.d_imm im = UNIV) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
     b + sz <= off \/ off + 32 <= b) /\
  (!i. i < lo /\ i IN tn.t_mem /\ ~(off <= i /\ i < off + 32) ==>
     imm_section_dead (cx_tops cx)
       (mem_bytes_at 0 lo (mstore off w s).vs_memory) i) ==>
  ghost_inv_at D lo d ce cx es' G
    (tn with <|t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + 32};
               t_imm := key_update tn.t_imm off {}|>)
    (istore off w s)
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> conj_tac
  >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def, lookup_var_def,
          istore_def, mstore_def]) >>
  gvs[op_taint_def, stor_taint_ok_at_def, allocas_from_def, istore_def,
      mstore_def, SUBSET_UNIV] >> metis_tac[]
QED

Resume immutable_istore_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- gvs[ptr_covers_def, op_taint_def, lookup_var_def, istore_def, mstore_def] >>
  qx_gen_tac `ptrword` >> qx_gen_tac `mem` >> strip_tac >>
  `lookup_var p s = SOME ptrword` by fs[lookup_var_def, istore_def, mstore_def] >>
  `local_region ce es.scopes s name (w2n ptrword) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n ptrword + sz <= off \/ off + 32 <= w2n ptrword` by metis_tac[] >>
  `lookup_scopes name es.scopes = SOME entry` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory entry.type entry.value (w2n ptrword) m` by metis_tac[] >>
  drule mstore_local_robust >>
  disch_then (qspecl_then [`name`, `entry`, `p`, `sz`, `off`, `ptrword`, `w`,
    `tn.t_mem`, `tn.t_mem DIFF {i | off <= i /\ i < off + 32}`] mp_tac) >>
  simp[] >> disch_then (qspec_then `mem` mp_tac) >> fs[istore_def]
QED
Finalise immutable_istore_ghost

Theorem immutable_uint256_istore_ghost_by_layout:
  ghost_inv_at D lo d ce cx es G tn s /\
  local_ptrs_rel func ce es.scopes s /\ es'.scopes = es.scopes /\
  (!im. D.d_imm im = UNIV) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
     b + sz <= off \/ off + 32 <= b) /\
  (!ty tv. evaluate_type (type_env (cx_tops cx)) ty = SOME tv ==>
      type_mem_bytes (get_struct_fields (make_struct_fields_map (cx_tops cx))) ty =
      type_memory_size tv) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable name (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre ==>
  ghost_inv_at D lo d ce cx es' G
    (tn with <|t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + 32};
               t_imm := key_update tn.t_imm off {}|>)
    (istore off w s)
Proof
  strip_tac >> irule immutable_istore_ghost >>
  asm_rewrite_tac[] >> conj_tac
  >- suspend "dead" >>
  qexistsl_tac [`es`, `func`] >> gvs[] >> metis_tac[]
QED

Resume immutable_uint256_istore_ghost_by_layout[dead]:
  rpt strip_tac >>
  `imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) i` by
    fs[ghost_inv_at_def] >>
  `!j. j < LENGTH (mem_bytes_at 0 lo s.vs_memory) /\
        ~(off <= j /\ j < off + 32) ==>
       EL j (mem_bytes_at 0 lo (mstore off w s).vs_memory) =
       EL j (mem_bytes_at 0 lo s.vs_memory)` by
    (rpt strip_tac >>
     `mem_bytes_at j 1 (mstore off w s).vs_memory = mem_bytes_at j 1 s.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> fs[EL_mem_bytes_at]) >>
  `LENGTH (mem_bytes_at 0 lo (mstore off w s).vs_memory) =
   LENGTH (mem_bytes_at 0 lo s.vs_memory)` by simp[] >>
  mp_tac (Q.INST [`tops` |-> `cx_tops cx`,
    `sec1` |-> `mem_bytes_at 0 lo s.vs_memory`,
    `sec2` |-> `mem_bytes_at 0 lo (mstore off w s).vs_memory`]
    (SPEC_ALL immutable_uint256_dead_frame_by_layout)) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED
Finalise immutable_uint256_istore_ghost_by_layout

Theorem immutable_word_older_taint:
  tn'.t_mem SUBSET tn.t_mem /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) ==>
  !aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
               off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn0.t_mem
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem immutable_uint256_store_boundary_by_layout:
  stmt_state_rel H ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  value_has_type (BaseTV (UintT 256)) v /\
  ghost_inv_at D lo d ce cx ee G tn s /\ (!im. D.d_imm im = UNIV) /\
  (!ty tv. evaluate_type (type_env (cx_tops cx)) ty = SOME tv ==>
      type_mem_bytes (get_struct_fields (make_struct_fields_map (cx_tops cx))) ty =
      type_memory_size tv) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable id (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre /\
  alloca_frame ce es sa s0 ce ee s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) ==>
  stmt_state_rel H ctx func ce cx fin
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  ghost_inv_at D lo d ce cx fin G
    (tn with <|t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + 32};
               t_imm := key_update tn.t_imm off {}|>)
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  alloca_frame ce es sa s0 ce fin
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\
     i IN (tn.t_mem DIFF {j | off <= j /\ j < off + 32}) ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME (BaseTV (UintT 256))` by
    simp[evaluate_type_def] >>
  `fin.scopes = ee.scopes` by metis_tac[write_immutable_place_scopes] >>
  `local_ptrs_rel func ce ee.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all immutable_assign_declared_region >>
  simp[NoAsms, type_memory_size_def] >> strip_tac >>
  rpt conj_tac
  >- suspend "state"
  >- (irule immutable_uint256_istore_ghost_by_layout >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[regions_disjoint_def])
  >- suspend "frame" >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

Resume immutable_uint256_store_boundary_by_layout[state]:
  qpat_x_assum `cx_tops cx = _` kall_tac >>
  qpat_x_assum `off = _` kall_tac >>
  `val_in_memory (BaseTV (UintT 256)) v off
     (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s).vs_memory` by
    (simp[istore_def] >> metis_tac[typed_word_store, is_word_type_def]) >>
  `immutable_value_admissible (BaseTV (UintT 256)) v` by
    metis_tac[evaluated_immutable_admissible] >>
  `immutable_value_bytes_rel (BaseTV (UintT 256)) v
     (mem_bytes_at off 32
       (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s).vs_memory)` by
    (irule (SRULE [type_memory_size_def]
       (Q.SPEC `BaseTV (UintT 256)` immutable_memory_bytes)) >>
     simp[well_formed_type_value_def] >> metis_tac[]) >>
  `!a k. regions_disjoint a k off 32 ==>
     mem_bytes_at a k
       (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s).vs_memory =
     mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> simp[istore_def] >>
     irule mstore_mem_bytes_at_disjoint >> gvs[regions_disjoint_def] >> decide_tac) >>
  `((istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) with
      <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
        vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    simp[istore_def, mstore_def, venom_state_component_equality] >>
  `LENGTH s.vs_memory <=
     LENGTH (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s).vs_memory` by
    simp[istore_def, venomMemPropsTheory.LENGTH_mstore_eq] >>
  `!x. lookup_var x (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) =
       lookup_var x s` by simp[lookup_var_def, istore_def, mstore_def] >>
  irule immutable_store_stmt_state_rel >> asm_rewrite_tac[] >>
  qexistsl_tac [`env`, `ee`, `id`, `off`, `s`, `su`,
    `ce.ce_module`, `BaseTV (UintT 256)`, `BaseT (UintT 256)`, `v`] >>
  simp[type_memory_size_def] >> fs[istore_def]
QED

Resume immutable_uint256_store_boundary_by_layout[frame]:
  qpat_x_assum `cx_tops cx = _` kall_tac >>
  qpat_x_assum `off = _` kall_tac >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[alloca_frame_def] >> strip_tac >>
  qx_gen_tac `aid` >> qx_gen_tac `a` >> qx_gen_tac `sz` >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> conj_tac
  >- (`FLOOKUP s.vs_allocas aid = SOME (a,sz)` by metis_tac[] >>
      `regions_disjoint off 32 a sz` by metis_tac[] >>
      simp[istore_def] >> fs[regions_disjoint_def] >>
      simp[mstore_mem_bytes_at_disjoint]) >>
  rpt strip_tac >>
  `local_region ce ee.scopes s n b sz'` by
    (qpat_assum `fin.scopes = ee.scopes` (fn th =>
      gvs[th, local_region_def, istore_def, mstore_def, lookup_var_def])) >>
  qpat_x_assum `!n b sz'. local_region ce ee.scopes s n b sz' ==>
    a + sz <= b \/ b + sz' <= a` drule >> simp[ADD_COMM]
QED
Finalise immutable_uint256_store_boundary_by_layout

Theorem immutable_istore_execution:
  eval_operand addr s = SOME a /\ eval_operand op s = SOME w /\
  op_taint tn op = {} ==>
  run_inst_seq [mk_inst iid ISTORE [addr;op] []] s = OK (istore (w2n a) w s) /\
  step_prov PG G (mk_inst iid ISTORE [addr;op] []) (istore (w2n a) w s) = G /\
  step_taint (mk_inst iid ISTORE [addr;op] []) s (istore (w2n a) w s) tn =
    tn with <|t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
              t_imm := key_update tn.t_imm (w2n a) {}|>
Proof
  strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def] >>
  simp[taint_component_equality, mem_taint_def, new_site_bytes_def,
       istore_def, mstore_def, write_memory_with_expansion_def, FLOOKUP_DEF,
       step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       written_taint_def, range_bytes_def, EXTENSION, DRESTRICT_UNIV] >> metis_tac[]
QED

Theorem immutable_uint256_dead_frame:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + 32) ==>
       EL j sec2 = EL j sec1) /\
  imm_section_dead tops sec1 i ==>
  imm_section_dead tops sec2 i
Proof
  strip_tac >>
  mp_tac (SPEC_ALL immutable_uint256_dead_frame_by_layout) >>
  asm_rewrite_tac[] >> disch_then irule >>
  rpt gen_tac >> strip_tac >> metis_tac[imm_frame_size]
QED

Theorem immutable_uint256_istore_ghost:
  ghost_inv_at D lo d ce cx es G tn s /\
  local_ptrs_rel func ce es.scopes s /\ es'.scopes = es.scopes /\
  (!im. D.d_imm im = UNIV) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
     b + sz <= off \/ off + 32 <= b) /\
  struct_args_unique (cx_tops cx) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable name (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre ==>
  ghost_inv_at D lo d ce cx es' G
    (tn with <|t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + 32};
               t_imm := key_update tn.t_imm off {}|>)
    (istore off w s)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL immutable_uint256_istore_ghost_by_layout) >>
  asm_rewrite_tac[] >> disch_then irule >>
  rpt gen_tac >> strip_tac >> metis_tac[imm_frame_size]
QED

Theorem immutable_uint256_store_boundary:
  stmt_state_rel H ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  value_has_type (BaseTV (UintT 256)) v /\
  ghost_inv_at D lo d ce cx ee G tn s /\ (!im. D.d_imm im = UNIV) /\
  struct_args_unique (cx_tops cx) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable id (BaseT (UintT 256)) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre /\
  alloca_frame ce es sa s0 ce ee s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) ==>
  stmt_state_rel H ctx func ce cx fin
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  ghost_inv_at D lo d ce cx fin G
    (tn with <|t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + 32};
               t_imm := key_update tn.t_imm off {}|>)
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  alloca_frame ce es sa s0 ce fin
    (istore off (typed_val_to_w256 (BaseTV (UintT 256)) v) s) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\
     i IN (tn.t_mem DIFF {j | off <= j /\ j < off + 32}) ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL immutable_uint256_store_boundary_by_layout) >>
  asm_rewrite_tac[] >> disch_then irule >>
  rpt gen_tac >> strip_tac >> metis_tac[imm_frame_size]
QED
