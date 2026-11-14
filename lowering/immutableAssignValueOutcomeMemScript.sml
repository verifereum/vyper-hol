(* The physical RHS dispatches to counted immutable write outcomes. *)
Theory immutableAssignValueOutcomeMem
Ancestors
  immutableAssignCompose immutableAssignMetadata immutableAssignRepresentation
  immutableAssignWordOutcomeMem
  immutableAssignDirectOutcomeMem immutableAssignBytesOutcomeMem
  immutableAssignNormalizedPostMem immutableDeployPhysicalSource
  immutableDeployAssignRanges immutableDeployAssignFacts immutableDeployAssignAdmissible
  immutableBytestringFootprint bytestringCopyExecution
  immutableAssignReadiness exprSimMemDefs
  bodyMemBopRestWordPath exprSimHyps exprSimHypsDefs loweringPosts
  typedMemoryCopy valueCopyBytes valueTypingMemoryProps valueEncodingProps exprSimBufferStore
  annassignRelayoutSource placeMemoryTypeInterfaces vyperTypeArgFits
  exprLoweringProps abiDecodeStaticProps
  stmtSimDefs loweringStateRelDefs compileEnv stmtLowering context
  venomState venomMemProps fragGasMode arithmetic words
Libs monadsyntax

Theorem immutable_assign_value_mem_stmt_post:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (ce.ce_module,id) = SOME ity /\
  expr_body_pre ce cx env e es /\
  assignable_type env.type_defs (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  expr_sim_inv ce cx env ee /\
  expr_post ctx func ce cx e ers si su s0 ee v op s /\
  expr_store_bound cx (expr_type e) v op s /\
  (~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
    !w tv. eval_operand op s = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==>
      type_memory_size tv = 0 \/ w2n (w:bytes32) + type_memory_size tv <= s.vs_alloca_next) /\
  compile_assign_value ce (Lit (n2w off)) LocCode op (is_word_type ity) loc
    ity (lowered_value_type ce e) (type_memory_bytes ce ity) su = ((),sb) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
  local_ptrs_reserved ce su /\ (!x. op = Var x ==> not_fresh_at su x) /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at su x) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  off + type_memory_size itv < dimword (:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q /\
    s.vs_alloca_next <= q.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  drule_all immutable_rhs_physical_widens >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `tu = itv` by metis_tac[optionTheory.SOME_11] >>
  `value_has_type itv v` by metis_tac[] >>
  `stmt_state_rel ctx func ce cx ee s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (ACCEPT_TAC o cj 1 o PURE_REWRITE_RULE [expr_post_def])) >>
  Cases_on `is_word_type ity`
  >- suspend "word" >>
  suspend "aggregate"
QED

Resume immutable_assign_value_mem_stmt_post[word]:
  `lowered_value_type ce e = ity` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `expr_type e = ity` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `eval_operand op s = SOME (typed_val_to_w256 itv v)` by
    fs[expr_post_def, expr_val_rel_def] >>
  mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`,
    `bytes` |-> `type_memory_bytes ce ity`]
    (SPEC_ALL immutable_assign_word_stmt_post_mem)) >>
  impl_tac >- (gvs[] >> decide_tac) >>
  strip_tac >> qexists_tac `q` >> simp[] >>
  drule gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_frontier >> simp[]
QED

Resume immutable_assign_value_mem_stmt_post[aggregate]:
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[return_source_word_widens_eq] >>
  drule_all immutable_rhs_physical_memory >> strip_tac >>
  `0 < type_memory_size stv` by
    (drule_all immutable_assign_rhs_memory_positive >> simp[]) >>
  `type_memory_bytes ce ity = type_memory_size itv` by
    metis_tac[expr_sim_inv_memory_size] >>
  Cases_on `is_bytestring_type ity`
  >- suspend "bytes" >>
  Cases_on `ity = lowered_value_type ce e`
  >- suspend "direct" >>
  suspend "normalized"
QED

Resume immutable_assign_value_mem_stmt_post[direct]:
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutable_rhs_post_physical_classify] >>
  `~is_word_type (post_value_type ce e)` by metis_tac[] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[return_source_word_widens_eq, type_widens_from_bytestring] >>
  `expr_val_at ce cx (post_value_type ce e) si su ee v op s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (ACCEPT_TAC o cj 3 o PURE_REWRITE_RULE [expr_post_def])) >>
  drule_all immutable_assign_source_range >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stv = itv` by metis_tac[optionTheory.SOME_11] >>
  `0 < type_memory_size itv` by metis_tac[] >>
  `type_memory_size itv <> 0` by decide_tac >>
  `val_footprint stv v = type_memory_size itv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `w2n (w:bytes32) + type_memory_size itv <= s.vs_alloca_next` by metis_tac[] >>
  qabbrev_tac `copy_size = type_memory_size itv` >>
  qabbrev_tac `n = if copy_size <= 32 then 1 else (copy_size+31) DIV 32` >>
  `val_footprint stv v <= 32*n /\ 32*n <= type_memory_size itv` by
    (irule immutable_assign_direct_window >> goal_assum (drule_at Any) >>
     simp[Abbr `copy_size`, Abbr `n`] >> metis_tac[]) >>
  `copy_size = type_memory_size itv` by simp[Abbr `copy_size`] >>
  `n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32)` by
    simp[Abbr `n`] >>
  `type_memory_size itv = 32*n` by metis_tac[LESS_EQUAL_ANTISYM] >>
  suspend "direct_call"
QED

Resume immutable_assign_value_mem_stmt_post[direct_call]:
  `tu = itv /\ ptv = stv` by metis_tac[optionTheory.SOME_11] >>
  `val_in_memory itv v (w2n (w:bytes32)) s.vs_memory` by metis_tac[] >>
  `w2n (w:bytes32) + val_footprint stv v < dimword (:256)` by metis_tac[] >>
  `regions_disjoint off (type_memory_size itv) (w2n (w:bytes32)) (type_memory_size itv)` by
    metis_tac[] >>
  `w2n (w:bytes32) + 32*n <= s.vs_alloca_next /\ off + 32*n < dimword (:256)` by
    metis_tac[] >>
  `(w2n (w:bytes32) + 32*n <= off \/ off + 32*n <= w2n (w:bytes32))` by
    metis_tac[regions_disjoint_def] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity
    (lowered_value_type ce e) (type_memory_bytes ce ity) su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [ASSUME ``~is_word_type ity``])) >>
  `copy_size = (if is_bytestring_type ity then
    type_memory_bytes ce (lowered_value_type ce e) else type_memory_bytes ce ity)` by
    (PURE_REWRITE_TAC [ASSUME ``~is_bytestring_type ity``, COND_CLAUSES] >>
     metis_tac[]) >>
  `eval_operand op s = SOME (n2w (w2n (w:bytes32)))` by
    (PURE_REWRITE_TAC [n2w_w2n] >> first_assum ACCEPT_TAC) >>
  suspend "direct_store"
QED

Resume immutable_assign_value_mem_stmt_post[direct_store]:
  markerLib.RESUME_TAC >>
  (mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`,
    `a` |-> `w2n (w:bytes32)`, `bytes` |-> `type_memory_bytes ce ity`,
    `k` |-> `val_footprint stv v`]
    (SPEC_ALL immutable_assign_direct_stmt_post_mem)) >>
  impl_tac >- (rpt conj_tac >> metis_tac[LESS_EQ_REFL]) >>
  strip_tac >> qexists_tac `q` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_frontier >>
  disch_then (qspec_then `q` mp_tac) >> simp_tac bool_ss [])
QED

Resume immutable_assign_value_mem_stmt_post[bytes]:
  `is_bytestring_type (lowered_value_type ce e) /\
   is_bytestring_type (expr_type e)` by metis_tac[typed_copy_bytestring_source] >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[immutable_rhs_post_physical_classify, is_bytestring_word_type] >>
  `expr_val_at ce cx (post_value_type ce e) si su ee v op s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (ACCEPT_TAC o cj 3 o PURE_REWRITE_RULE [expr_post_def])) >>
  drule_all immutable_assign_source_range >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >> simp[]) >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
     value_has_type etv v` by metis_tac[type_widens_to_value_has_type] >>
  `val_store_size stv v = val_store_size etv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  mp_tac (Q.SPECL [`get_tenv cx`,`lowered_value_type ce e`,`stv`,`v`,
    `w2n (w:bytes32)`,`s`] buffer_typed_bytestring_header) >> simp[] >>
  disch_then (qx_choose_then `lenh` strip_assume_tac) >>
  `val_store_size etv v <> 0` by decide_tac >>
  `w2n (w:bytes32) + (32 + 32 * word_size lenh) <= s.vs_alloca_next` by
    (fs[expr_store_bound_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `lenh < dimword (:256)` by
    (mp_tac (Q.SPEC `lenh` word_size_capacity) >> decide_tac) >>
  mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`, `dty` |-> `ity`,
    `tenv` |-> `get_tenv cx`, `stv` |-> `stv`, `dtv` |-> `itv`,
    `a` |-> `w2n (w:bytes32)`] immutable_bytestring_runtime_extent) >> simp[] >>
  disch_then (qx_choose_then `len` strip_assume_tac) >>
  `len < dimword (:256)` by decide_tac >>
  `lenh = len` by fs[n2w_11] >>
  qpat_x_assum `lenh = len` SUBST_ALL_TAC >>
  `w2n (w:bytes32) + 32 * (1 + word_size len) < dimword (:256) /\
   w2n (w:bytes32) + 32 * (1 + word_size len) <= s.vs_alloca_next` by
    (simp_tac std_ss [LEFT_ADD_DISTRIB] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  `len + 63 < dimword (:256)` by
    (irule bytestring_word_count_no_wrap >>
     qpat_assum `w2n (w:bytes32) + 32 * (1 + word_size len) < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [LEFT_ADD_DISTRIB] >>
     metis_tac[LESS_EQ_ADD, ADD_COMM, LESS_EQ_LESS_TRANS]) >>
  suspend "bytes_layout"
QED

Resume immutable_assign_value_mem_stmt_post[bytes_layout]:
  `val_in_memory itv v (w2n (w:bytes32)) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_footprint stv v <> 0` by
    metis_tac[ADD_EQ_0, DECIDE ``32 <> 0``] >>
  `regions_disjoint off (type_memory_size itv) (w2n (w:bytes32)) (val_footprint itv v)` by
    metis_tac[] >>
  drule_all immutable_assign_declared_region >> strip_tac >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  suspend "bytes_call"
QED

Resume immutable_assign_value_mem_stmt_post[bytes_call]:
  `!j. j < 1 + word_size len ==>
    w2n ((w:bytes32)+n2w (32*j)) + 32 <= s.vs_alloca_next /\
    w2n ((n2w off:bytes32)+n2w (32*j)) + 32 <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `w2n (w:bytes32) + 32*j + 32 <= s.vs_alloca_next /\
      off + 32*j + 32 <= s.vs_alloca_next` by
       metis_tac[DECIDE ``!a b d cap j n. j < 1+n /\
         a+32*(1+n) <= cap /\ 32*(n+1) <= d /\ b+d <= cap ==>
         a+32*j+32 <= cap /\ b+32*j+32 <= cap``] >>
     `w2n (w:bytes32) + 32*j < dimword (:256) /\ off + 32*j < dimword (:256)` by
       metis_tac[DECIDE ``!a cap d. a+32 <= cap /\ cap < d ==> a < d``] >>
     simp[w2n_add_n2w_lt, word_add_n2w] >> metis_tac[ADD_ASSOC]) >>
  `32 * (1 + word_size len) <= type_memory_size itv` by
    metis_tac[ADD_COMM] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity
    (lowered_value_type ce e) (type_memory_size itv) su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [ASSUME ``~is_word_type ity``,
        ASSUME ``type_memory_bytes ce ity = type_memory_size itv``])) >>
  mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`, `a` |-> `(w:bytes32)`]
    (SPEC_ALL immutable_assign_bytes_mem_stmt_post)) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Resume immutable_assign_value_mem_stmt_post[normalized]:
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutable_rhs_post_physical_classify] >>
  `expr_val_at ce cx (lowered_value_type ce e) si su ee v op s /\
   expr_val_rel cx (lowered_value_type ce e) v op s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (fn th =>
       let val pr = PURE_REWRITE_RULE [expr_post_def] th in
         mp_tac (cj 2 pr) >> mp_tac (cj 3 pr)
       end) >> asm_simp_tac bool_ss []) >>
  `type_memory_size stv = 0 <=> type_memory_size itv = 0` by
    metis_tac[type_widens_to_zero_memory_size] >>
  `0 < type_memory_size itv` by decide_tac >>
  `immutable_value_admissible itv v` by
    metis_tac[evaluated_immutable_admissible] >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size itv MOD 32 = 0` by simp[type_memory_size_slots] >>
  `type_memory_size itv < dimword (:256)` by decide_tac >>
  drule_all immutable_assign_copy_metadata >> strip_tac >>
  drule_all immutable_assign_declared_region >> strip_tac >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity
    (lowered_value_type ce e) (type_memory_size itv) su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [ASSUME ``~is_word_type ity``,
        ASSUME ``type_memory_bytes ce ity = type_memory_size itv``])) >>
  mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`, `dty` |-> `ity`,
    `dtv` |-> `itv`, `src` |-> `op`, `p` |-> `(w:bytes32)`, `sm` |-> `su`,
    `sa` |-> `si`, `es` |-> `ee`, `sl` |-> `loc`]
    (SPEC_ALL immutable_assign_normalized_mem_stmt_post)) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> metis_tac[]) >> simp[]
QED

Finalise immutable_assign_value_mem_stmt_post
