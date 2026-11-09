(* Slot semantics and joint resources at one counted mapping endpoint. *)
Theory bodyIntCallFamAggSubscriptMappingSlot
Ancestors
  bodyIntCallFamAggSubscriptMappingRun bodyIntCallJointContract
  exprSimMapKey exprLoweringProps placeMemoryPrimitiveForward
  compileEnv context venomState

Theorem intcall_mapping_slot_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      eval_operand op u = SOME (hashmap_slot w0 w1) /\
      (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  drule_all compile_mapping_subscript_frame >> strip_tac >>
  drule_all intcall_mapping_scratch_run_cont >> strip_tac >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb) /\
   (?x. op = Var x /\ not_fresh_at sb x)` by
    metis_tac[mapping_suffix_shape] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    fs[listTheory.EVERY_CONJ] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all straight_line_zero_gas_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def]
QED
