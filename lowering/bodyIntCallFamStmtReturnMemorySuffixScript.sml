(* Counted memory return suffixes, at the joint invariant boundary. *)
Theory bodyIntCallFamStmtReturnMemorySuffix
Ancestors
  bodyIntCallFamStmtReturnMemoryPath bodyIntCallFamStmtReturnBytesEffect
  bodyIntCallJointStmtBoundary bodyIntCallCopySharpRank
  bodyIntCallJointContract placeMemoryCopyEffect compileEnv loweringStateRelDefs loweringPosts
  venomState venomExecSemantics

Theorem intcall_compound_store_return_exit:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  type_widens_to (get_tenv fp.jc_cx) sty fp.jc_ret_ty /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type fp.jc_ret_tv v /\ val_wf fp.jc_ret_tv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  compile_store_memory ce src dst fp.jc_ret_ty sty sa = ((),sm) /\
  ~is_word_type fp.jc_ret_ty /\ ~is_bytestring_type fp.jc_ret_ty /\
  (sty = fp.jc_ret_ty ==> type_memory_size fp.jc_ret_tv + 64 < dimword (:256)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME bw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  emit_inst RET [fp.jc_rpc] [] sm = ((),sb) /\
  fn_has_code sm sb fp.jc_func ==>
  ?t. gas_path fp.jc_ctx fp.jc_func s 0
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
    intcall_stmt_exit fp (INR (ReturnException v)) es
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all intcall_copy_metadata >> strip_tac >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
   cap = type_memory_size fp.jc_ret_tv` by
    (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `w2n bw + cap < dimword (:256)` by
    (irule intcall_return_buffer_bound >> metis_tac[]) >>
  `?t. val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sa sm s t (w2n bw) cap` by
    (Cases_on `sty = fp.jc_ret_ty`
     >- (gvs[] >>
         SUBGOAL_THEN ``fp.jc_ret_ty = fp.jc_ret_ty \/
           is_bytestring_type fp.jc_ret_ty /\ is_bytestring_type fp.jc_ret_ty`` assume_tac
         >- simp[] >>
         `(if is_word_type fp.jc_ret_ty then sw = typed_val_to_w256 fp.jc_ret_tv v
           else val_in_memory fp.jc_ret_tv v (w2n sw) s.vs_memory)` by simp[] >>
         `type_memory_bytes ce fp.jc_ret_ty = type_memory_size fp.jc_ret_tv` by metis_tac[] >>
         drule_all bodyIntCallFamStmtReturnStoreEffectTheory.compatible_store_effect >>
         disch_then (qspec_then `fp.jc_ctx` mp_tac) >> simp[]) >>
     `compile_store_memory_typed ce dst fp.jc_ret_ty src sty sa = ((),sm)` by
       gvs[contextTheory.compile_store_memory_def] >>
     simp[] >> irule compile_store_memory_typed_forward_sharp >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`stv`, `sw`, `get_tenv fp.jc_cx`] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `t` >> irule intcall_copy_return_exit >> simp[] >>
  goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >> gvs[]
QED

Theorem intcall_bytestring_store_return_exit:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  compile_store_memory ce src dst fp.jc_ret_ty physical sa = ((),sm) /\
  is_bytestring_type fp.jc_ret_ty /\ is_bytestring_type a /\
  evaluate_type (get_tenv fp.jc_cx) a = SOME av /\
  value_has_type av v /\ value_has_type fp.jc_ret_tv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_size av + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME bw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  emit_inst RET [fp.jc_rpc] [] sm = ((),sb) /\
  fn_has_code sm sb fp.jc_func ==>
  ?t. gas_path fp.jc_ctx fp.jc_func s 0
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
    intcall_stmt_exit fp (INR (ReturnException v)) es
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
   cap = type_memory_size fp.jc_ret_tv` by
    (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  drule_all bytestring_store_effect >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  qexists_tac `t` >> irule intcall_copy_return_exit >> simp[] >>
  goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >> gvs[]
QED
