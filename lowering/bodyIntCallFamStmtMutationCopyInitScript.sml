(* Materialized initializer store: value semantics and expression resources
   at the same counted endpoint, before activation of the source binding. *)
Theory bodyIntCallFamStmtMutationCopyInit
Ancestors
  bodyIntCallFamStmtMutationStaging bodyIntCallJointAggCore
  bodyIntCallJointContract exprLoweringProps placeMemoryCopyEffect compileEnv

Theorem intcall_initializer_store_landing:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s /\
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  expr_val_at ce fp.jc_cx sty si sa es v src s /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sa.cs_next_var <= sb.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u
        (w2n dw) (type_memory_size dtv) /\
      val_in_memory dtv v (w2n dw) u.vs_memory /\
      intcall_expr_res fp ce env es sb u
Proof
  strip_tac >> drule_all intcall_child_store_effect >> strip_tac >>
  `!a n. fp.jc_prot a n ==>
     regions_disjoint a n (w2n dw) (type_memory_size dtv)` by
    (fs[intcall_frame_ok_def, regions_disjoint_def] >> rpt strip_tac >>
     disj1_tac >>
     qpat_x_assum `!a k. fp.jc_prot a k ==> a+k <= fp.jc_lo` drule >>
     decide_tac) >>
  `intcall_expr_res fp ce env es sb u` by
    (drule_all intcall_joint_res_copy >> simp[]) >>
  qexists `u` >> simp[]
QED
