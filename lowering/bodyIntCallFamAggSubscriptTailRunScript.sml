(* Resource composition for supplied scratch tail stages. *)
Theory bodyIntCallFamAggSubscriptTailRun
Ancestors
  bodyIntCallFamAggSubscriptReadRun bodyIntCallFamAggSubscriptStoreRun
  bodyIntCallJointContract exprSimLiteralBuffer emitHelperProps exprLoweringProps
  context compileEnv venomState venomInst

Theorem intcall_scratch_tail_run_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 es sn s /\
  emit_op ADD [buf; Lit 32w] sn = (dst,sp) /\
  emit_void MSTORE [dst; key] sp = ((),sq) /\
  emit_op SHA3 [buf; Lit 64w] sq = (op,sb) /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
  fn_has_code sq sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n addr,64) /\
  sa.cs_next_id <= inst.inst_id /\ w2n addr + 64 < dimword (:256) /\
  sa.cs_next_var <= sn.cs_next_var /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. buf = Var x ==> not_fresh_at sn x) /\
  eval_operand buf s = SOME addr /\ eval_operand key s = SOME w /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     regions_disjoint (w2n addr) 64 lb len) /\
  run_inst_seq (emitted_insts sn sp) s = OK added /\
  run_inst_seq (emitted_insts sp sq)
    (added with vs_inst_idx := LENGTH sp.cs_current_insts) = OK stored /\
  run_inst_seq (emitted_insts sq sb)
    (stored with vs_inst_idx := LENGTH sq.cs_current_insts) = OK t ==>
  intcall_expr_cont fp ce env es sa s0 es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all intcall_add_run_cont >> strip_tac >>
  `eval_operand key (added with vs_inst_idx := LENGTH sp.cs_current_insts) = SOME w /\
   eval_operand buf added = SOME addr /\
   FLOOKUP (added with vs_inst_idx := LENGTH sp.cs_current_insts).vs_allocas
     inst.inst_id = SOME (w2n addr,64)` by
    (Cases_on `key` >> Cases_on `buf` >>
     fs[eval_operand_def, lookup_var_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `sa.cs_next_var <= sp.cs_next_var` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `w2n (addr + 32w) = w2n addr + 32` by simp[wordsTheory.w2n_add_2] >>
  `eval_operand dst (added with vs_inst_idx := LENGTH sp.cs_current_insts) =
     SOME (addr + 32w) /\ w2n addr <= w2n (addr + 32w) /\
   w2n (addr + 32w) + 32 <= w2n addr + 64` by
    simp[eval_operand_def, lookup_var_def] >>
  drule_all intcall_scratch_store_run_cont >> strip_tac >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  `eval_operand buf (stored with vs_inst_idx := LENGTH sq.cs_current_insts) = SOME addr` by
    (Cases_on `buf` >>
     fs[venom_state_component_equality, mstore_def, eval_operand_def, lookup_var_def] >> gvs[]) >>
  `sa.cs_next_var <= sq.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `eval_operand (Lit 64w) (stored with vs_inst_idx := LENGTH sq.cs_current_insts) = SOME 64w`
    by simp[eval_operand_def] >>
  drule_all intcall_sha3_run_cont >> simp[]
QED
