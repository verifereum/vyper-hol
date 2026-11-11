(* Bytes stores separate the semantic source capacity from the compiler's
   physical source annotation.  Only the destination is a write region. *)
Theory bodyIntCallFamStmtMutationBytesInit
Ancestors
  bodyIntCallFamStmtReturnBytesEffect bodyIntCallJointAggCore
  exprSimCopy exprSimStorageCopy
  bodyIntCallJointContract exprLoweringProps placeMemoryCopyEffect compileEnv
  venomState venomInst

Theorem intcall_bytes_initializer_store:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_store_memory ce src dst dty physical sa = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type a /\
  evaluate_type tenv a = SOME av /\ evaluate_type tenv dty = SOME dv /\
  value_has_type av v /\ value_has_type dv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_size av + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  fp.jc_lo <= b /\ b <= w2n dw /\ w2n dw + type_memory_size dv <= b+k /\
  (!name p n. local_region ce es.scopes s name p n ==>
     regions_disjoint b k p n) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dv v (w2n dw) t.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sa sb s t (w2n dw) (type_memory_size dv) /\
    intcall_expr_res fp ce env es sb t
Proof
  strip_tac >> drule_all bytestring_store_effect >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND] >>
  `typed_copy_effect fp.jc_ctx fp.jc_func sa sb s t b k` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `copy_static t = copy_static s` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality,copy_static_def]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl [`b`,`inst`,`s`,`sa`,`k`] >>
     fs[intcall_expr_res_def,typed_copy_effect_def,regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `intcall_expr_res fp ce env es sb t` by
    (irule intcall_joint_res_copy >> simp[] >>
     qexistsl [`w2n dw`,`type_memory_size dv`,`s`,`sa`] >> simp[] >>
     fs[intcall_frame_ok_def,regions_disjoint_def] >> rpt strip_tac >>
     qpat_x_assum `!a k. fp.jc_prot a k ==> a+k <= fp.jc_lo` drule >>
     decide_tac) >>
  qexists `t` >> simp[]
QED
