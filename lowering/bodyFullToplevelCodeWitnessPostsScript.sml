(* Operational consequences of the fixed TopLevelName immutable-copy witness. *)
Theory bodyFullToplevelCodeWitnessPosts
Ancestors
  bodyFullToplevelCodeNormalize exprPtrUnwrapTypedSize exprPtrCodeCopyEndpoint
  exprPtrUnwrapCodeEdges
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapAllocationFrame immutableCopyWordsPtr
  exprPtrUnwrapAllocation bufferAllocationExecution exprSimCopy exprSimStorageCopy
  exprLoweringProps exprLowering compileEnv loweringStateRelDefs allocationPtr
  allocaHistory venomMemDefs venomState venomInst bodyPtrDefs ptrDiscipline
  words arithmetic finite_map pred_set list

Theorem toplevel_code_runtime_witness_layout:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  nb = type_memory_bytes cenv t /\ n = (nb+31) DIV 32 /\
  type_memory_bytes cenv t = type_memory_size rt /\
  compile_alloc_buffer nb sb = (buf,mid) /\
  compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand buf.buf_operand n 0 mid = ((),sc) /\
  buf.buf_operand = Var root ==>
  nb = 32*n /\ op = Var root
Proof
  strip_tac >>
  `nb = 32*n` by
    metis_tac[unwrap_typed_buffer_bytes, unwrap_typed_buffer_count] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qpat_x_assum `nb = 32*n` kall_tac >> gvs[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >>
  pure_asm_rewrite_tac[ensure_code_copy_route, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem toplevel_code_runtime_witness_old:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  Gm = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  copy_runtime_frame mid a sc z /\
  (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
    op_taint tf (Var x) = op_taint tm (Var x)) ==>
  !x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)
Proof
  strip_tac >>
  `sb.cs_next_var <= mid.cs_next_var` by
    (mp_tac (Q.SPECL [`nb`,`sb`] ci_mono_compile_alloc_buffer) >>
     simp[ci_mono_def]) >>
  gen_tac >> disch_tac >> irule unwrap_code_old_variable_frames >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl [`PG`,`k`,`sc`] >> simp[] >> metis_tac[]
QED

Theorem toplevel_code_runtime_witness_allocation:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword(:256) /\
  buf.buf_operand = Var root /\
  u = update_var root (n2w (buffer_allocation_base s sb.cs_next_id))
    (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := SUC s.vs_inst_idx /\
  (d:bytes32) = n2w (buffer_allocation_base s sb.cs_next_id) /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  alloca_inv a /\ a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  mid.cs_current_bb = sb.cs_current_bb /\ a.vs_current_bb = mid.cs_current_bb /\
  w2n d+nb <= a.vs_alloca_next /\
  a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
  a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
  a.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `alloca_inv u` by metis_tac[history_base_alloca_inv] >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `mid.cs_current_bb = sb.cs_current_bb` by metis_tac[unwrap_alloc_current_block] >>
  `w2n d+nb <= (buffer_allocation_fields s sb.cs_next_id nb).vs_alloca_next` by
    (qpat_x_assum `d = _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
     >- simp[buffer_allocation_base_def, buffer_allocation_fields_def,
             arithmeticTheory.MOD_LESS_EQ] >>
     rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME site` >>
     PairCases_on `site` >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
     drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
     fs[alloca_next_valid_def, buffer_allocation_base_def, buffer_allocation_fields_def] >>
     first_x_assum drule >>
     `site0 MOD dimword(:256) <= site0` by simp[arithmeticTheory.MOD_LESS_EQ] >>
     decide_tac) >>
  conj_tac
  >- (qpat_x_assum `a = _` SUBST1_TAC >>
      qpat_x_assum `alloca_inv u` mp_tac >>
      simp[NoAsms, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  conj_tac >- simp[arithmeticTheory.ADD1] >>
  qpat_x_assum `alloca_inv u` kall_tac >>
  gvs[update_var_def, buffer_allocation_fields_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[]
QED

Theorem toplevel_code_runtime_witness_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  nb = type_memory_bytes cenv t /\ n = (nb+31) DIV 32 /\
  type_memory_bytes cenv t = type_memory_size rt /\ nb < dimword(:256) /\
  compile_alloc_buffer nb sb = (buf,mid) /\
  compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand buf.buf_operand n 0 mid = ((),sc) /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  buf.buf_operand = Var root /\
  u = update_var root (n2w (buffer_allocation_base s sb.cs_next_id))
    (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := SUC s.vs_inst_idx /\
  Gm = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sb.cs_next_id) /\
  copy_runtime_frame mid a sc z /\ z.vs_current_bb = sc.cs_current_bb /\
  lookup_var root a = SOME d /\
  tf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
  (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
    op_taint tf (Var x) = op_taint tm (Var x)) ==>
  nb = 32*n /\ op = Var root /\ eval_operand op z = SOME d /\
  w2n d+nb <= z.vs_alloca_next /\
  (!j. w2n d <= j /\ j < w2n d+nb ==> j NOTIN tf.t_mem) /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_current_bb = sc.cs_current_bb
Proof
  strip_tac >>
  drule_all toplevel_code_runtime_witness_layout >> strip_tac >>
  drule_all toplevel_code_runtime_witness_allocation >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sc)` by
    metis_tac[immutable_copy_nonterminators] >>
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     drule_all toplevel_code_runtime_witness_old >> simp[NoAsms]) >>
  `not_fresh_at mid root` by
    (drule allocated_copy_operands_old >> simp[] >>
     disch_then (qspec_then `Lit 0w` mp_tac) >> simp[]) >>
  `eval_operand op z = SOME d` by
    (fs[copy_runtime_frame_def, eval_operand_def] >> metis_tac[]) >>
  `z.vs_alloca_next = a.vs_alloca_next` by
    fs[copy_runtime_frame_def, copy_static_def, venom_state_component_equality] >>
  drule_all toplevel_code_runtime_history >> strip_tac >>
  qpat_x_assum `tf.t_mem = _` mp_tac >>
  qpat_x_assum `nb = type_memory_bytes _ _` kall_tac >>
  qpat_x_assum `n = _` kall_tac >>
  simp[] >> rpt strip_tac >> gvs[]
QED
