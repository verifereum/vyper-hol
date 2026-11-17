(* Fixed endpoint semantic and ghost boundaries for Convert widening. *)
Theory bodyFullConvertCopyPosts
Ancestors
  stateRelProj
  exprSimConvertBytes bodyFullAllocaFresh typedCopyPtr robustCopyTransportPtr fragExecPtr
  bodyPtrDefs exprSimDefs exprSimMemDefs exprSimProps loweringPosts loweringStateRelDefs
  venomInst exprLoweringProps ptrDiscipline venomExecSemantics venomState finite_map pred_set

Theorem convert_widen_copy_endpoint_post:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\ local_ptrs_reserved cenv sm /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME a /\
  ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  val_wf rt v /\ val_in_memory rt v (w2n a) s.vs_memory /\
  val_footprint rt v <= k /\
  run_inst_seq (emitted_insts sm sb) s = OK u /\
  q = u with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  expr_post H ctx func cenv cx e ee sm sb s ee v op q
Proof
  strip_tac >> drule_all convert_widen_copy_run >> strip_tac >>
  `t = u` by gvs[] >> gvs[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       stmt_state_rel_inst_idx, lookup_var_def, local_region_def,
       locals_kept_def, eval_operand_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The allocation frame and the copy update are supplied, not re-executed.
   The representation premise concerns occupied bytes, not padded capacity. *)
Theorem convert_widen_copy_endpoint_ghosts:
  ghost_inv_at D lo d0 cenv cx ee G tn s /\
  stmt_state_rel H ctx func cenv cx ee s /\
  stmt_state_rel H ctx func cenv cx ee z /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
  z with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo z /\ s.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
       (s.vs_alloca_next <= i /\ i < w2n dw+cap)) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  sa0.cs_next_var <= sm.cs_next_var /\
  lo <= s.vs_alloca_next /\
  (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa0.cs_next_id ==>
       b+n <= s.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n) /\
  (!name b n. local_region cenv es0.scopes s0 name b n ==>
       b+n <= s.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n) /\
  (!name b n. local_region cenv ee.scopes z name b n ==>
       regions_disjoint (w2n dw) cap b n) /\
  lo <= w2n dw /\ k <= cap /\ cap < dimword(:256) /\
  lookup_var dst z = SOME dw /\ lookup_var src z = SOME a /\
  ptr_covers Ga tna dst z cap /\
  q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := idx /\
  Gf = step_prov PG Ga (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] [])
         (mcopy (w2n dw) (w2n a) k z) /\
  tnf = step_taint (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] []) z
         (mcopy (w2n dw) (w2n a) k z) tna /\
  w2n dw+cap <= z.vs_alloca_next /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME rt /\
  val_wf rt v /\ val_footprint rt v <= k /\ val_store_size rt v <= cap /\
  type_memory_bytes cenv ty <= cap /\ type_memory_size rt <= cap /\
  w2n a+k <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v (w2n a) m) ==>
  ghost_inv_at D lo d0 cenv cx ee Gf tnf q /\
  ptr_val_ok cx ty v (Var dst) Gf tnf q /\
  (!e. lowered_value_type cenv e = ty ==> ptr_buf_ok cenv e (Var dst) Gf q) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gf tnf /\
  vv_store_bound cx ty ty ee (Value v) (StackValue ty (Var dst)) q
Proof
  strip_tac >>
  `ghost_inv_at D lo d0 cenv cx ee Ga tna z` by
    (drule_all alloc_buffer_ghost_inv_at >> simp[]) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Ga tna` by
    (irule alloc_buffer_ghost_kept_at >> goal_assum (drule_at Any) >>
     qexistsl_tac [`G`, `w2n dw+cap`, `tn`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
         metis_tac[]) >>
     conj_tac >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `z.vs_memory = s.vs_memory` by
    (qpat_x_assum `z with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
                            vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `k < dimword(:256)` by decide_tac >>
  `w2n (n2w k : 256 word) = k` by simp[wordsTheory.w2n_n2w] >>
  `Gf = Ga /\ tnf.t_var = tna.t_var /\ tnf.t_stor = tna.t_stor /\
   tnf.t_trans = tna.t_trans /\
   tnf.t_mem = (tna.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw+k}) UNION
     {w2n dw+i | i < k /\ w2n a+i IN tna.t_mem}` by
    (qpat_x_assum `tna.t_stor = tn.t_stor` kall_tac >>
     qpat_x_assum `tna.t_trans = tn.t_trans` kall_tac >>
     qpat_x_assum `!i. i IN tna.t_mem <=> _` kall_tac >>
     qabbrev_tac `cw = (n2w k :256 word)` >>
     `w2n cw = k` by simp[Abbr `cw`] >>
     `n2w k = cw` by simp[Abbr `cw`] >>
     asm_rewrite_tac[] >>
     qpat_assum `w2n cw = k` (fn th => once_rewrite_tac[GSYM th]) >>
     conj_tac >- (irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     conj_tac >- (irule (cj 2 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     conj_tac >- (irule (cj 3 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     conj_tac >- (irule (cj 4 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     irule (cj 5 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  `tnf.t_imm = tna.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  `!x. lookup_var x q = lookup_var x z /\
       op_taint tnf (Var x) = op_taint tna (Var x)` by
    simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, op_taint_def] >>
  `!i. ~(w2n dw <= i /\ i < w2n dw+k) ==>
        (i IN tnf.t_mem <=> i IN tna.t_mem)` by
    (simp[] >> rpt strip_tac >> eq_tac >> simp[] >> decide_tac) >>
  conj_tac >- suspend "inv" >>
  conj_tac >- suspend "value" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "kept" >>
  suspend "bounds"
QED

Resume convert_widen_copy_endpoint_ghosts[inv]:
  `!p sz. ptr_covers Ga tna p z sz ==> ptr_covers Gf tnf p q sz` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  `!i n. i+n <= w2n dw \/ w2n dw+k <= i ==>
     mem_bytes_at i n q.vs_memory = mem_bytes_at i n z.vs_memory` by
    (qpat_x_assum `z.vs_memory = s.vs_memory` kall_tac >>
     rpt strip_tac >> simp[] >>
     irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >> simp[]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ Ga tna z` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "inv_locals" >>
  conj_tac
  >- (Cases_on `d0` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (gvs[stor_taint_ok_at_def, mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~(w2n dw <= i /\ i < w2n dw+k)` by decide_tac >>
      `i IN tna.t_mem` by metis_tac[] >>
      `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo z.vs_memory` by simp[] >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  gvs[allocas_from_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]
QED
Resume convert_widen_copy_endpoint_ghosts[inv_locals]:
  rpt gen_tac >> strip_tac >>
  `ptr_covers Ga tna p z sz` by metis_tac[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `lookup_var p z = SOME w` by metis_tac[] >>
  `local_ptrs_rel func cenv ee.scopes z` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `local_region cenv ee.scopes z name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  `regions_disjoint (w2n dw) cap (w2n w) sz` by metis_tac[] >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`z.vs_memory`, `q.vs_memory`, `tna.t_mem`, `tnf.t_mem`,
    `{i | w2n dw <= i /\ i < w2n dw+k}`] >>
  qpat_x_assum `z.vs_memory = s.vs_memory` kall_tac >>
  qpat_x_assum `q = _` kall_tac >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> fs[regions_disjoint_def] >> decide_tac
QED
Resume convert_widen_copy_endpoint_ghosts[value]:
  `!m. mem_agree_outside tna.t_mem z.vs_memory m ==>
       val_in_memory rt v (w2n a) m` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `z.vs_memory`, `tn.t_mem`, `tna.t_mem`,
       `{i | s.vs_alloca_next <= i}`] >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  `!j. j < k ==> (w2n dw+j IN tnf.t_mem <=> w2n a+j IN tna.t_mem)` by
    (qpat_x_assum `tnf.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp[] >> rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `!m. mem_agree_outside tnf.t_mem q.vs_memory m ==>
       val_in_memory rt v (w2n dw) m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`z.vs_memory`, `q.vs_memory`, `k`, `w2n a`,
                  `tna.t_mem`, `tnf.t_mem`] >>
     simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED
Resume convert_widen_copy_endpoint_ghosts[buffer]:
  rpt strip_tac >> simp[ptr_buf_ok_def, eval_operand_def] >>
  gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED
Resume convert_widen_copy_endpoint_ghosts[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ Ga tna` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n dw) cap off sz` by metis_tac[] >>
      `~(w2n dw <= i /\ i < w2n dw+k)` by
        (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint (w2n dw) cap b sz` by metis_tac[] >>
  `~(w2n dw <= i /\ i < w2n dw+k)` by
    (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]
QED
Resume convert_widen_copy_endpoint_ghosts[bounds]:
  simp[vv_store_bound_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def, eval_operand_def] >>
  conj_tac >> rpt strip_tac >>
  gvs[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >> decide_tac
QED
Finalise convert_widen_copy_endpoint_ghosts
