(* Fresh scratch stores at a supplied raw execution endpoint. *)
Theory bodyIntCallFamAggSubscriptStoreRun
Ancestors
  bodyIntCallFamAggSubscriptScratchTail bodyIntCallJointContract
  exprSimLiteralBuffer context compileEnv venomState venomInst

Theorem intcall_scratch_store_run_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 es si s /\
  emit_void MSTORE [ptr_op; value] si = ((),sb) /\
  eval_operand ptr_op s = SOME addr /\ eval_operand value s = SOME w /\
  fn_has_code si sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  sa.cs_next_id <= inst.inst_id /\
  b <= w2n addr /\ w2n addr + 32 <= b + sz /\
  sa.cs_next_var <= si.cs_next_var /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     regions_disjoint b sz lb len) /\
  run_inst_seq (emitted_insts si sb) s = OK t ==>
  intcall_expr_cont fp ce env es sa s0 es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_scratch_store_cont >> strip_tac >>
  drule_all literal_emit_mstore_run >> strip_tac >> gvs[]
QED
