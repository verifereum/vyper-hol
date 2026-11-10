(* A staging ALLOCA is separate from the allocation-preserving copy.
   The continuation retains the original allocation frontier and byte frame. *)
Theory bodyIntCallFamStmtMutationStaging
Ancestors
  bodyIntCallFamStmtMutationFlatCopy
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimAlloc
  exprLoweringProps placeMemoryCopyEffect exprSimCopy exprSimProps
  valueEncodingProps compileEnv venomInst venomState fragGasMode
  bodyIntCallCopySharpDynamic freshWrites

Theorem intcall_staging_copy_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es sa s es sm a /\
  compile_copy_memory dst src n sm = ((),sb) /\
  eval_operand dst a = SOME dw /\ eval_operand src a = SOME sw /\
  n < dimword (:256) /\ fn_has_code sm sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sa.cs_next_id /\
  FLOOKUP a.vs_allocas inst.inst_id = SOME (w2n dw,n) /\
  fp.jc_lo <= w2n dw /\ sa.cs_next_var <= sm.cs_next_var /\
  (!name b k. local_region ce es.scopes a name b k ==>
     regions_disjoint (w2n dw) n b k) /\
  (!name b k. local_region ce es.scopes s name b k ==>
     regions_disjoint (w2n dw) n b k) ==>
  ?t. typed_copy_effect fp.jc_ctx fp.jc_func sm sb a t (w2n dw) n /\
      intcall_expr_cont fp ce env es sa s es sb t /\
      mem_bytes_at (w2n dw) n t.vs_memory =
        mem_bytes_at (w2n sw) n a.vs_memory
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sm a /\ ~a.vs_halted /\
   a.vs_current_bb = sm.cs_current_bb /\
   a.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  drule_all intcall_flat_copy_effect >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  `sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_copy_memory, ci_mono_def, pairTheory.SND] >>
  `copy_static t = copy_static a` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality, exprSimStorageCopyTheory.copy_static_def]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl [`w2n dw`,`inst`,`a`,`sm`,`n`] >>
     fs[intcall_expr_res_def, typed_copy_effect_def, regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists `t` >> simp[] >>
  irule intcall_owned_store_cont >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`inst.inst_id`,`w2n dw`,`w2n dw`,`n`,`a`,`sm`,`n`] >>
  fs[intcall_expr_res_def, stmt_state_rel_def,
     regions_disjoint_def, arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem intcall_staging_initialize:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ n < dimword (:256) /\
  eval_operand src s = SOME sw /\ (!lbl. src <> Label lbl) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  type_memory_size tv <= n /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sb t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    fp.jc_lo <= w2n w /\ w2n w+n < dimword (:256) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >> drule_all intcall_alloc_landing >> strip_tac >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> fs[intcall_expr_cont_def, eval_operand_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, pairTheory.SND] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `fp.jc_lo <= w2n w` by
    (fs[intcall_expr_cont_def,intcall_expr_res_def,
        intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  `!name b k. local_region ce es.scopes s name b k ==>
     regions_disjoint (w2n w) n b k` by
    (rpt strip_tac >>
     `local_region ce es.scopes u name b k` by
       (irule local_region_frame_fwd >>
        qexistsl [`s`,`sa`] >> fs[intcall_expr_res_def,intcall_expr_cont_def] >>
        metis_tac[]) >>
     metis_tac[]) >>
  `?t. typed_copy_effect fp.jc_ctx fp.jc_func sm sb u t (w2n w) n /\
       intcall_expr_cont fp ce env es sa s es sb t /\
       mem_bytes_at (w2n w) n t.vs_memory = mem_bytes_at (w2n sw) n u.vs_memory` by
    (irule intcall_staging_copy_landing >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl [`buf.buf_operand`,`src`] >> simp[]) >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  suspend "result"
QED

Resume intcall_staging_initialize[result]:
  `sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_copy_memory, ci_mono_def, pairTheory.SND] >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s (0+0) (OK t)` by
    (irule gas_marked_path_then >> qexists `u` >>
     fs[typed_copy_effect_def]) >>
  fs[] >> qexistsl [`t`,`w`] >> simp[] >>
  conj_tac >-
    (drule_all (typed_copy_effect_operand_preserved |>
       Q.INST [`oper` |-> `Var p`] |> SRULE []) >> simp[]) >>
  conj_tac >-
    (irule valueEncodingPropsTheory.val_in_memory_relocate >>
     simp[] >> qexistsl [`s.vs_memory`,`n`,`w2n sw`] >> fs[]) >>
  fs[typed_copy_effect_def] >>
  metis_tac[not_fresh_at_mono]
QED

Finalise intcall_staging_initialize
