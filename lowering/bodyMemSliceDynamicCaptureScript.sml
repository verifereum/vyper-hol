(* Counted memory boundary for ordinary dynamic slice source capture. *)
Theory bodyMemSliceDynamicCapture
Ancestors
  exprSimSliceDynamicAdapter builtinBytesMemory bodyMemBiMethodIdSuffix
  exprSimMemDefs fragExecMem fragGasSeqMem exprSimSliceMemory exprSimSliceCaptureControl

Theorem slice_dynamic_capture_path_mem[local]:
  compile_bytestring_src src sm = ((len,data),sc) /\
  eval_operand src t = SOME p /\ w2n p + 32 <= t.vs_alloca_next /\
  (!z. src = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  alloca_inv t /\ alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sc) t = OK u ==>
  gas_path_mem ctx func t 0 (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
  alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ~u.vs_halted /\ u.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  drule_all compile_bytestring_src_mem_ok >> strip_tac >>
  drule_all slice_bytestring_src_run >> strip_tac >> gvs[] >>
  drule slice_bytestring_src_control >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sc) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sc)) = 0` by
    (drule slice_bytestring_src_shape >> strip_tac >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule_all method_id_run_path_mem >>
  simp[fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
  qpat_x_assum `t' = t with vs_vars := _` SUBST1_TAC >> simp[]
QED

Theorem slice_source_dynamic_capture_entry_mem:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  lower_value compile_expr cenv (BaseT bt) src sa = (src_op,sm) /\
  compile_bytestring_src src_op sm = ((len_op,data),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sc func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_store_bound cx (BaseT bt) v src_op t /\
  fn_inst_ids_distinct func /\ alloca_history func t ==>
  ?cap bs (p:bytes32) u.
    ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
     (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sc) t = OK u /\
    w2n p + 32 + LENGTH bs < dimword (:256) /\
    let u' = u with vs_inst_idx := LENGTH sc.cs_current_insts in
      gas_path_mem ctx func t 0 (OK u') /\ alloca_history func u' /\ ~u'.vs_halted /\
      w2n p + 32 + LENGTH bs <= u'.vs_alloca_next /\
      t.vs_alloca_next = u'.vs_alloca_next /\
      u'.vs_current_bb = sc.cs_current_bb /\
      stmt_state_rel ctx func cenv cx ee u' /\
      eval_operand len_op u' = SOME (n2w (LENGTH bs)) /\
      eval_operand data u' = SOME (n2w (w2n p + 32)) /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u'.vs_memory = bs /\
      (!env' sd se e1 e2 ee1 ee2 v1 v2 op1 op2 r1 r2.
        expr_sim_inv cenv cx env' ee1 /\
        local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd.cs_next_id /\
        MAP FDOM ee.scopes = MAP FDOM ee1.scopes /\
        (!z. src_op = Var z ==> not_fresh_at sc z) /\
        (!l. src_op <> Label l) /\
        expr_post ctx func cenv cx e1 ee sc sd u' ee1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 ee1 sd se r1 ee2 v2 op2 r2 ==>
        mem_bytes_at (w2n p + 32) (LENGTH bs) r2.vs_memory = bs)
Proof
  strip_tac >>
  `~is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def] >>
     Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def,
       compileEnvTheory.is_word_type_def]) >>
  drule_all slice_source_dynamic_capture_entry >> strip_tac >>
  `!z. src_op = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!l. src_op <> Label l` by
    (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `?w. eval_operand src_op t = SOME w` by
    (fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def]) >>
  drule_all slice_bytestring_src_run >> strip_tac >> gs[] >>
  `eval_operand src_op t' = SOME w` by
    (Cases_on `src_op` >> gvs[venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `w = p` by gvs[instIdxIndepTheory.eval_op_inst_idx] >> gs[] >>
  `w2n p + 32 + LENGTH bs <= t.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def] >> strip_tac >>
     `val_footprint (BaseTV bt) v <= val_store_size (BaseTV bt) v` by
       simp[exprSimPropsTheory.val_footprint_le_store_size] >>
     gs[] >> decide_tac) >>
  `alloca_inv t` by fs[loweringPostsTheory.expr_post_def,
    exprLoweringPropsTheory.stmt_state_rel_def] >>
  `w2n p + 32 <= t.vs_alloca_next` by decide_tac >>
  drule_all slice_dynamic_capture_path_mem >> strip_tac >>
  qexists_tac `p` >> gs[] >> first_assum MATCH_ACCEPT_TAC
QED
