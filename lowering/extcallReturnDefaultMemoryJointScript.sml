(* Same-run copy boundaries for memory defaults. *)
Theory extcallReturnDefaultMemoryJoint
Ancestors
  extcallReturnDefaultWordJoint extcallReturnDefaultLengthJoint
  bodyFullUnwrapRun bodyFullUnwrapSlotPost fragGasCopyLoop allocaFootprint
  exprSimBufferStore fragExecPtr fragGasSeqPtr typedCopyPtr robustCopyTransportPtr
  compileEnv venomMemDefs fragExec exprLoweringProps codegenRel ptrDiscipline context emitHelperProps venomState venomInst venomExecSemantics
  finite_map list pred_set

Theorem return_default_mcopy_joint:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME aw /\ lookup_var dst s = SOME dw /\
  eval_operand count_op s = SOME nw /\ op_taint tn count_op = {} /\
  ptr_covers G tn src s (w2n nw) /\ ptr_covers G tn dst s (w2n nw) /\
  allocas_from lo s /\
  (w2n nw = 0 \/ w2n aw + w2n nw <= s.vs_alloca_next) /\
  (w2n nw = 0 \/ w2n dw + w2n nw <= s.vs_alloca_next) ==>
  ?u tm.
    u = (mcopy (w2n dw) (w2n aw) (w2n nw) s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
    tm = tn with t_mem :=
      (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + w2n nw}) UNION
      {w2n dw+i | i < w2n nw /\ w2n aw+i IN tn.t_mem} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G,tm)) /\
    (!op. eval_operand op u = eval_operand op s) /\
    (!off len. off+len <= w2n dw \/ w2n dw+w2n nw <= off ==>
       mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+w2n nw) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!tv v. val_wf tv v /\ val_footprint tv v <= w2n nw /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n aw) mem) ==>
       !mem. mem_agree_outside tm.t_mem u.vs_memory mem ==> val_in_memory tv v (w2n dw) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []]` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s =
     OK (mcopy (w2n dw) (w2n aw) (w2n nw) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
       (mcopy (w2n dw) (w2n aw) (w2n nw) s) = G /\
   step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
       (mcopy (w2n dw) (w2n aw) (w2n nw) s) tn =
       tn with t_mem :=
         (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + w2n nw}) UNION
         {w2n dw+i | i < w2n nw /\ w2n aw+i IN tn.t_mem}` by
    (simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, eval_operand_def, imm_taint_def,
       mcopy_def, write_memory_with_expansion_def, FLOOKUP_DEF,
       pred_setTheory.EXTENSION, taint_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`mcopy (w2n dw) (w2n aw) (w2n nw) s with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `tn with t_mem := (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + w2n nw}) UNION
       {w2n dw+i | i < w2n nw /\ w2n aw+i IN tn.t_mem}`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- (Cases >> simp[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >- (rpt strip_tac >> irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  conj_tac >- (rpt strip_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  suspend "value"
QED
Resume return_default_mcopy_joint[path]:
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`[mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []]`, `sa`] >>
  simp[run_inst_seq_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  simp[is_terminator_def] >>
  conj_tac >- (drule emit_mcopy_mem_ok >>
    disch_then (qspecl_then [`s`, `dw`, `aw`, `nw`] mp_tac) >> simp[eval_operand_def]) >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[mk_inst_def] >> simp[] >>
  qexists_tac `0` >> simp[] >>
  gvs[inst_seq_ptr_def] >> irule ptr_inst_ok_mcopy_operand >> simp[]
QED
Resume return_default_mcopy_joint[value]:
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mcopy (w2n dw) (w2n aw) (w2n nw) s).vs_memory`,
    `w2n nw`, `w2n aw`, `tn.t_mem`,
    `(tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + w2n nw}) UNION
       {w2n dw+i | i < w2n nw /\ w2n aw+i IN tn.t_mem}`] >>
  simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same] >> rpt strip_tac >> eq_tac >> simp[] >> decide_tac
QED
Finalise return_default_mcopy_joint

Theorem return_default_static_copy_joint:
  compile_copy_memory (Var dst) (Var src) k sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  k < dimword (:256) /\ lookup_var src s = SOME aw /\ lookup_var dst s = SOME dw /\
  (k <> 0 ==> ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
    w2n aw+k <= s.vs_alloca_next /\ w2n dw+k <= s.vs_alloca_next) /\
  allocas_from lo s ==>
  ?u tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G,tm)) /\
    (!op. eval_operand op u = eval_operand op s) /\
    (!off len. off+len <= w2n dw \/ w2n dw+k <= off ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+k) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!tv v. val_wf tv v /\ val_footprint tv v <= k /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n aw) mem) ==>
       !mem. mem_agree_outside tm.t_mem u.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (u with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (tm with t_mem := tn.t_mem) = tn
Proof
  strip_tac >> Cases_on `k = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`s`, `tn`] >> simp[] >>
      conj_tac >- simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
      reverse conj_tac >- gvs[venom_state_component_equality] >>
      rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n aw`, `tn.t_mem`, `tn.t_mem`] >>
      simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `emit_void MCOPY [Var dst;Var src;Lit (n2w k)] sa = ((),sb)` by
    (Cases_on `k` >> gvs[compile_copy_memory_def]) >>
  `w2n (n2w k : bytes32) = k` by simp[wordsTheory.w2n_n2w] >>
  drule return_default_mcopy_joint >>
  disch_then (qspecl_then [`tn`, `s`, `n2w k`, `lo`, `func`, `explicit`, `dw`, `ctx`, `aw`, `PG`, `G`] mp_tac) >>
  simp[eval_operand_def, op_taint_def] >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  qexistsl_tac [`mcopy (w2n dw) (w2n aw) k s with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `tn with t_mem := (tn.t_mem DIFF {i | w2n dw <= i /\ i < k+w2n dw}) UNION
      {i+w2n dw | i < k /\ i+w2n aw IN tn.t_mem}`] >> gvs[] >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  gvs[mcopy_def, write_memory_with_expansion_def, venom_state_component_equality] >> metis_tac[]
QED
