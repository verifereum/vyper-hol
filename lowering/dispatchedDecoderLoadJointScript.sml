(* Actual calldata load: shared concrete endpoint and zero-event joint trace. *)
Theory dispatchedDecoderLoadJoint
Ancestors calldataWordStepsPtr dispatchedDecoderTrace abiDecoderContract
  abiEncoder fragExec instIdxIndep bodyPtrDefs calldataClampPtr
  calldataOverwritePtr loweringStateRelDefs venomMemDefs

Theorem calldata_load_accepted_joint:
  emit_op CALLDATALOAD [src] sa = (v,sb) /\
  eval_operand src s = SOME sw /\ fresh_vars_wrt sa s /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_inv s ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    eval_operand v t = SOME (abi_decode_load CALLDATALOAD sw s) /\
    op_taint u v = {} /\ op_prov H v = NONE /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a w. eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u))
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule evaluated_operand_not_fresh >>
     goal_assum $ drule_at (Pat `eval_operand`) >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK loaded` >>
  drule_all calldata_load_overwrite_trace_uniform >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `loaded = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ _ = OK loaded` mp_tac >> simp[]) >>
  `fresh_vars_wrt sb t` by fs[fresh_vars_wrt_def] >>
  `!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z` by
    (rpt strip_tac >>
     qpat_x_assum `!a z. eval_operand a s = SOME z ==> eval_operand a loaded = SOME z`
       drule >> simp[eval_op_inst_idx]) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED
