(* Dynamic capture embedding and continuation boundary. *)
Theory exprSimSliceDynamicAdapter
Ancestors
  exprSimSliceCaptureControl exprSimSliceCapture exprSimSliceOrdinaryFrame
  exprSimSliceMemory fragExec rich_list list

Theorem slice_dynamic_capture_embedding:
  compile_bytestring_src src sm = ((len,data),sc) /\
  fn_has_code sm sc func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sm sc) (DROP t.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule slice_bytestring_src_control >> strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem slice_source_dynamic_capture_entry:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  lower_value compile_expr cenv (BaseT bt) src sa = (src_op,sm) /\
  compile_bytestring_src src_op sm = ((len_op,data),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sc func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?cap bs (p:bytes32) u.
    ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
     (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sc) t = OK u /\
    w2n p + 32 < dimword (:256) /\
    w2n p + 32 + LENGTH bs < dimword (:256) /\
    evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
    32 + LENGTH bs <= val_footprint (BaseTV bt) v /\
    let u' = u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sc) in
      u'.vs_inst_idx = LENGTH sc.cs_current_insts /\
      u'.vs_current_bb = sc.cs_current_bb /\
      stmt_state_rel ctx func cenv cx ee u' /\
      eval_operand len_op u' = SOME (n2w (LENGTH bs)) /\
      eval_operand data u' = SOME (n2w (w2n p + 32)) /\
      eval_operand src_op u' = SOME p /\
      expr_val_at cenv cx (BaseT bt) sa sc ee v src_op u' /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u'.vs_memory = bs /\
      (!e sd ee' v' op' r.
        expr_post ctx func cenv cx e ee sc sd u' ee' v' op' r ==>
        mem_bytes_at (w2n p + 32) (LENGTH bs) r.vs_memory = bs) /\
      (!env' sd se e1 e2 ee1 ee2 v1 v2 op1 op2 r1 r2.
        expr_sim_inv cenv cx env' ee1 /\
        local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd.cs_next_id /\
        MAP FDOM ee.scopes = MAP FDOM ee1.scopes /\
        (!z. src_op = Var z ==> not_fresh_at sc z) /\
        (!l. src_op <> Label l) /\
        expr_post ctx func cenv cx e1 ee sc sd u' ee1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 ee1 sd se r1 ee2 v2 op2 r2 ==>
        mem_bytes_at (w2n p + 32) (LENGTH bs) r2.vs_memory = bs) /\
      (!tops source Q R.
        gas_outcome F tops (ctx,func) source (ee,u') Q R ==>
        gas_outcome F tops (ctx,func) source (ee,t) Q R)
Proof
  strip_tac >> drule_all slice_dynamic_capture_embedding >> strip_tac >>
  drule_all slice_source_dynamic_capture_reserved >> strip_tac >>
  `~is_word_type (BaseT bt)` by
    (fs[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `w2n p + val_footprint (BaseTV bt) v < dimword (:256)` by
    (irule exprSimTypedAllocTheory.expr_val_at_bound >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `w2n p + 32 + LENGTH bs < dimword (:256)` by decide_tac >>
  drule_all slice_capture_index_frame >> simp[Excl "LENGTH_MAP"] >> strip_tac >>
  gvs[instIdxIndepTheory.eval_op_inst_idx, Excl "LENGTH_MAP"] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >-
    (rpt strip_tac >>
     irule (cj 2 slice_dynamic_payload_two_operands) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[compileEnvTheory.is_word_type_def,
          instIdxIndepTheory.eval_op_inst_idx] >>
     qpat_assum `expr_val_at _ _ _ _ _ _ _ _ (_ with vs_inst_idx := _)`
       (irule_at Any) >>
     gvs[compileEnvTheory.is_word_type_def] >> metis_tac[])) >>
  rpt strip_tac >> irule slice_bytestring_capture_outcome_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`data`, `len_op`, `sc`, `sm`, `src_op`, `u`] >>
  simp[]
QED
