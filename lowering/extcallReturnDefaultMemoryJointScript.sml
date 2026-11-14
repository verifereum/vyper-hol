(* Same-run copy boundaries for memory defaults. *)
Theory extcallReturnDefaultMemoryJoint
Ancestors
  extcallReturnDefaultWordJoint extcallReturnDefaultLengthJoint
  extcallReturnDefaultMemoryFrame assignTuplePtrLocalCompat
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

Theorem return_default_memory_store_joint:
  compile_store_memory ce src (Var dst) rt sty a = ((),b) /\
  ~is_word_type rt /\ ~is_word_type sty /\
  (rt = sty \/ is_bytestring_type rt /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) rt = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type tv v /\ value_has_type stv v /\
  val_wf tv v /\ val_wf stv v /\
  type_memory_bytes ce rt = type_memory_size tv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size tv + 64 < dimword (:256) /\
  type_memory_size stv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at a x) /\ not_fresh_at a dst /\
  eval_operand src s = SOME sw /\ lookup_var dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  ptr_mem_ok cx sty v src G tn s /\
  (type_memory_size stv <> 0 ==>
    ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv) /\
        w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size tv <> 0 ==>
    ptr_covers G tn dst s (type_memory_size tv) /\
    w2n dw + type_memory_size tv <= s.vs_alloca_next) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  fn_has_code a b func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tm)) /\
    (!mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    lookup_var dst u = SOME dw /\
    (!x. not_fresh_at a x ==>
      lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!off len. off+len <= w2n dw \/ w2n dw+type_memory_size tv <= off ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. i < w2n dw \/ w2n dw+type_memory_size tv <= i ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by
    (gvs[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  Cases_on `is_bytestring_type rt`
  >- suspend "bytes" >>
  gvs[] >>
  `compile_copy_memory (Var dst) src (type_memory_size stv) a = ((),b)` by
    gvs[compile_store_memory_def] >>
  Cases_on `type_memory_size stv = 0`
  >- suspend "zero" >>
  gvs[eval_operand_def] >> rename1 `lookup_var source s = SOME sw` >>
  suspend "static"
QED
Resume return_default_memory_store_joint[zero]:
  gvs[compile_copy_memory_def, comp_return_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
  conj_tac >- simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  reverse conj_tac >- gvs[venom_state_component_equality] >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n sw`, `tn.t_mem`, `tn.t_mem`] >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  drule exprSimPropsTheory.val_footprint_le >> simp[]
QED
Resume return_default_memory_store_joint[static]:
  `emit_void MCOPY [Var dst;Var source;Lit (n2w (type_memory_size stv))] a = ((),b)` by
    (Cases_on `type_memory_size stv` >> gvs[compile_copy_memory_def]) >>
  `w2n (n2w (type_memory_size stv) : bytes32) = type_memory_size stv` by
    (simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  drule return_default_mcopy_joint >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `LENGTH s.vs_memory <= LENGTH (mcopy (w2n dw) (w2n sw) (type_memory_size stv) s).vs_memory` by
    (simp[mcopy_def, write_memory_with_expansion_def, LET_THM, LENGTH_TAKE, LENGTH_DROP] >>
     Cases_on `w2n dw + type_memory_size stv > LENGTH s.vs_memory` >> simp[LENGTH_TAKE] >> decide_tac) >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  qexistsl_tac [`mcopy (w2n dw) (w2n sw) (type_memory_size stv) s with vs_inst_idx := LENGTH b.cs_current_insts`,
    `G`, `tn with t_mem := (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw+type_memory_size stv}) UNION
      {w2n dw+i | i < type_memory_size stv /\ w2n sw+i IN tn.t_mem}`] >> simp[] >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  gvs[mcopy_def, write_memory_with_expansion_def, lookup_var_def,
      venom_state_component_equality] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume return_default_memory_store_joint[bytes]:
  `is_bytestring_type sty` by metis_tac[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv v (w2n sw) mem` by
    metis_tac[bytestring_robust_representation_compat_ptr] >>
  `?len. mload (w2n sw) s = n2w len /\
    len+31 < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_size stv /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_size tv /\
    val_footprint tv v <= 32 + 32 * ((len+31) DIV 32) /\
    (!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem)` by
    metis_tac[bytestring_compatible_resources_ptr] >>
  pop_assum strip_assume_tac >>
  `0 < type_memory_size stv /\ 0 < type_memory_size tv` by decide_tac >>
  gvs[eval_operand_def] >> rename1 `lookup_var source s = SOME sw` >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def, compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >>
  gvs[] >>
  `cs_extends a cs'` by
    (drule buffer_copy_len_shape >> simp[same_blocks_def, cs_extends_def] >>
     strip_tac) >>
  `cs_extends cs' b` by
    (drule emit_void_extends >> simp[same_blocks_def, cs_extends_def] >> strip_tac) >>
  `fn_has_code a cs' func /\ fn_has_code cs' b func` by
    metis_tac[fn_has_code_split] >>
  `ptr_covers G tn source s 32` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> first_assum (irule_at Any) >> decide_tac) >>
  `w2n sw + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all return_default_bytestring_length_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `lookup_var source u = SOME sw /\ lookup_var dst u = SOME dw` by metis_tac[] >>
  `ptr_covers Gf tm source u (32+32*((len+31) DIV 32)) /\
   ptr_covers Gf tm dst u (32+32*((len+31) DIV 32))` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >>
     conj_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `allocas_from lo u` by (gvs[allocas_from_def] >> metis_tac[]) >>
  `32+32*((len+31) DIV 32) < dimword (:256)` by decide_tac >>
  `((mload (w2n sw) s + 31w && ~31w) + 32w) =
     n2w (32+32*((len+31) DIV 32))` by
    (qspec_then `len` mp_tac buffer_round_size >>
     gvs[vfmConstantsTheory.word_size_def]) >>
  `w2n (n2w (32+32*((len+31) DIV 32)) : bytes32) = 32+32*((len+31) DIV 32)` by
    simp[wordsTheory.w2n_n2w] >>
  drule return_default_mcopy_joint >>
  disch_then (qspecl_then [`tm`, `u`, `n2w (32+32*((len+31) DIV 32))`,
    `lo`, `func`, `explicit`, `dw`, `ctx`, `sw`, `PG`, `Gf`] mp_tac) >>
  (impl_tac >- (gvs[] >> decide_tac)) >> strip_tac >>
  qexistsl_tac [`u'`, `Gf`, `tm'`] >>
  conj_tac >- (gen_tac >>
    qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
      (qspec_then `D` assume_tac) >>
    drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
    disch_then (qspecl_then [`u`, `Gf`, `tm`, `[]`, `OK u'`, `Gf`, `tm'`] mp_tac) >>
    simp[]) >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  conj_tac >- metis_tac[eval_operand_def] >>
  conj_tac >- (gvs[op_taint_def, eval_operand_def, lookup_var_def,
    mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `off + len' <= w2n dw \/
      w2n dw + w2n (n2w (32+32*((len+31) DIV 32)) : bytes32) <= off` by
      (simp[] >> decide_tac) >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `~(w2n dw <= i /\
      i < w2n dw + w2n (n2w (32+32*((len+31) DIV 32)) : bytes32))` by
      (simp[] >> decide_tac) >> metis_tac[]) >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  conj_tac >-
    (gvs[mcopy_def, write_memory_with_expansion_def, LET_THM, LENGTH_TAKE, LENGTH_DROP] >>
     Cases_on `w2n dw + (32+32*((len+31) DIV 32)) > LENGTH s.vs_memory` >>
     simp[LENGTH_TAKE] >> decide_tac) >>
  gvs[mcopy_def, write_memory_with_expansion_def, venom_state_component_equality]
QED
Finalise return_default_memory_store_joint
