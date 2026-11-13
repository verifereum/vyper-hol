Theory bodyIfExpBytesAdapter
Ancestors
  bodyIfExpDestination bodyIfExpBytesCopy exprSimIfExp exprSimWordArgs loweringStateRelDefs
  exprSimHash exprSimAggregateSource exprLoweringProps fragExec compileEnv
  exprOperandVar freshWrites exprSimMemDefs loweringPosts venomState
  bodyMemAssignAttrStorage exprSimPrecompiles valueCopy exprSimProps
  exprSimAlloc bodyIfExpArmMemory valueEncodingTyping

Theorem ifexp_adapter_source_operand[local]:
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s ==>
  ?a. eval_operand (vv_operand vv) s = SOME a
Proof
  Cases_on `vv` >> simp[loweringPostsTheory.vv_post_def,
    loweringPostsTheory.vv_holds_def, loweringPostsTheory.expr_val_rel_def,
    contextTheory.vv_operand_def] >> metis_tac[]
QED

Theorem ifexp_copy_frame[local]:
  wb_frame ce es ee origin s0 s /\ stmt_state_rel ctx func ce cx ee s /\
  local_ptrs_reserved ce origin /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  FLOOKUP s.vs_allocas aid = SOME (dst,cap) /\ origin.cs_next_id <= aid /\
  len <= cap /\
  (!name b k. local_region ce ee.scopes s name b k ==>
     regions_disjoint dst cap b k) ==>
  wb_frame ce es ee origin s0 (mcopy dst src len s)
Proof
  strip_tac >> irule wb_frame_allocating_tail >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s`,`ee.scopes`,`origin`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
      first_x_assum drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- simp[venomStateTheory.lookup_var_def,
          venomExecSemanticsTheory.mcopy_def,
          venomStateTheory.write_memory_with_expansion_def] >>
  rpt strip_tac >>
  `regions_disjoint b sz dst cap` by
    (irule state_allocations_disjoint >> goal_assum (drule_at Any) >>
     qexists_tac `aid` >> simp[] >> goal_assum (drule_at Any)) >>
  irule mem_bytes_at_mcopy_disjoint >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ifexp_bytestring_adapter_path_mem:
  expr_type e = t /\ is_bytestring_type t /\
  ~is_word_type t /\ ~same_memory_layout ce arm_ty t /\
  compile_ifexp_arm ce t arm_ty vv sa = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
  type_memory_bytes ce t = type_memory_size tvt /\ type_memory_size tvt < 2 ** 64 /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es origin sb s0 ee v op u /\
    vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_bytestring] >>
  drule_all ifexp_bytestring_adapter_parts >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_unwrap_value,
              ci_mono_compile_store_bytestring, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce sa` by metis_tac[local_ptrs_reserved_next_var] >>
  drule ifexp_adapter_source_operand >> strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) ifexp_allocate_unwrap_path >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`,`src`,`sn`,`a`] mp_tac) >>
  impl_tac >- (gvs[ci_mono_def] >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  strip_tac >> suspend "copy"
QED

Resume ifexp_bytestring_adapter_path_mem[copy]:
  `expr_val_rel cx t v src u /\ stmt_state_rel ctx func ce cx ee u` by
    (qpat_assum `post_value_type ce e = _` (fn th => fs[expr_post_def, th]) >>
     metis_tac[]) >>
  drule_all ifexp_copy_source_bounds >> strip_tac >>
  `!z. src = Var z ==> not_fresh_at sn z` by
    (drule compiler_unwrap_value_var >>
     Cases_on `vv` >> fs[contextTheory.vv_operand_def] >>
     metis_tac[not_fresh_at_mono, ci_mono_def]) >>
  `!z. src = Var z \/ buf.buf_operand = Var z ==> not_fresh_at sn z` by
    (gvs[] >> rpt strip_tac >- metis_tac[] >>
     irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `w2n w + (32 + 32 * word_size len) <= u.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def] >> disch_then (qspec_then `tvt` mp_tac) >>
     gvs[] >> decide_tac) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `~u.vs_halted` by
    (qpat_assum `gas_path_mem _ _ r _ _` (mp_tac o MATCH_MP
       fragGasPathMemTheory.gas_path_mem_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  `w2n d + (32 + 32 * word_size len) <= u.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
     first_x_assum drule >> gvs[] >> decide_tac) >>
  drule_at (Pat `compile_store_bytestring _ _ _ = _`) ifexp_bytes_copy_path_mem >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand _ = _`)) >>
  disch_then (qspecl_then [`len`,`ctx`] mp_tac) >>
  impl_tac >- (gvs[wordsTheory.dimword_def,
    valueEncodingPropsTheory.mem_word_at_eq_mload] >> first_assum ACCEPT_TAC) >>
  strip_tac >> suspend "endpoint"
QED

Resume ifexp_bytestring_adapter_path_mem[endpoint]:
  `local_ptrs_rel func ce es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
  `origin.cs_next_var <= sm.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `expr_post ctx func ce cx e es origin sn s0 ee v src u` by
    (irule expr_post_rebased_compose_mem_src >> goal_assum (drule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `wb_frame ce es ee origin s0 u` by metis_tac[expr_post_frame] >>
  `wb_frame ce es ee origin s0 (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) u)` by
    (irule ifexp_copy_frame >> goal_assum (drule_at Any) >>
     simp[] >> reverse conj_tac
     >- (qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce t))]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]) >>
  `not_local_ptr ce ee.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `sa.cs_next_id < sm.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, comp_bind_def,
       comp_return_def, fresh_id_def,
       fresh_var_def, emit_def, comp_ignore_bind_def] >>
     strip_tac >> gvs[]) >>
  suspend "canonical"

QED

Resume ifexp_bytestring_adapter_path_mem[canonical]:
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` by simp[] >>
  drule_at (Pat `wb_frame _ _ _ _ _ _`) ifexp_copy_endpoint >>
  disch_then (drule_at (Pat `post_value_type _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (mp_tac o SRULE[venomInstTheory.mk_inst_def]) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `not_local_ptr _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sb`,`op`,`t`] mp_tac) >>
  impl_tac
  >- (simp[] >>
      `val_wf tvt v` by metis_tac[value_has_type_val_wf] >>
      `sa.cs_next_id < sb.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
      `w2n d + type_memory_bytes ce t <= u.vs_alloca_next` by
        (fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.alloca_next_valid_def] >>
         first_x_assum drule >> simp[]) >>
      simp[] >> conj_tac >- (qspec_then `v` mp_tac (Q.SPEC `tvt` val_footprint_le_store_size) >> simp[]) >>
      conj_tac
      >- gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
         venomExecSemanticsTheory.mcopy_def, venomStateTheory.write_memory_with_expansion_def] >>
      rpt strip_tac >>
      `local_region ce ee.scopes u n b k` by
        (fs[local_region_def, venomStateTheory.eval_operand_def,
            venomStateTheory.lookup_var_def, venomExecSemanticsTheory.mcopy_def,
            venomStateTheory.write_memory_with_expansion_def]) >>
      first_x_assum drule >> simp[regions_disjoint_def]) >>
  strip_tac >> suspend "transport"
QED

Resume ifexp_bytestring_adapter_path_mem[transport]:
  qmatch_asmsub_abbrev_tac `expr_post ctx func ce cx e es origin sb s0 ee v op m` >>
  `q with <|vs_vars := m.vs_vars; vs_inst_idx := m.vs_inst_idx|> = m` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
       mp_tac >>
     simp[Abbr `m`, venomExecSemanticsTheory.mcopy_def,
          venomStateTheory.write_memory_with_expansion_def,
          venomStateTheory.venom_state_component_equality] >>
     rpt strip_tac >> gvs[]) >>
  `local_ptrs_reserved ce sn /\ origin.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def] >> irule local_ptrs_reserved_next_var >>
     qexists_tac `origin` >> simp[] >> decide_tac) >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_copy_post_transport >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`q`,`sn`] mp_tac) >>
  impl_tac
  >- simp[Abbr `m`, venomStateTheory.lookup_var_def,
          venomExecSemanticsTheory.mcopy_def, venomStateTheory.write_memory_with_expansion_def] >>
  strip_tac >> qexists_tac `q` >> simp[] >>
  conj_tac >- metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  gvs[]
QED

Finalise ifexp_bytestring_adapter_path_mem
