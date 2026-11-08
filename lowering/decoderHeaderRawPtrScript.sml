(* Header ghosts on raw ordinary states; only safety cursors are normalized. *)
Theory decoderHeaderRawPtr
Ancestors abiDecoderComposition decoderArrayInitPtr calldataDynOwned abiDecoderArrayHeader abiDecoderBulk
  abiDecoderContract abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  decoderArraySetupPtr bodyPtrDefs ptrDiscipline ptrSafeRun venomState venomExecSemantics
  fragExec venomInst words list arithmetic finite_map pred_set instIdxIndep moduleLoweringProps

Theorem calldata_array_header_raw_endpoint_ptr:
  abi_decode_array_header (Var root) src CALLDATALOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s capacity /\ 32 <= capacity /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u.
    ptr_covers H u root t capacity /\ op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD a s) /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    u.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn
        (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     rename1 `emit_void MSTORE [Var root;cnt] mid = ((),sb)` >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     imp_res_tac emitted_insts_emit_op >> drule emitted_insts_emit_void >>
     simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `lookup_var root (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME (n2w d) /\
   ptr_covers G tn root (s with vs_inst_idx := LENGTH sa.cs_current_insts) capacity /\
   eval_operand src (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a /\
   ~(s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_halted` by
    gvs[eval_op_inst_idx, ptr_covers_def, lookup_var_def] >>
  drule_all (Q.INST [`s` |-> `s with vs_inst_idx := LENGTH sa.cs_current_insts`,
    `t` |-> `t with vs_inst_idx := LENGTH sa.cs_current_insts`]
    (SPEC_ALL calldata_array_header_endpoint_ptr_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  `eval_operand (Var root) s = SOME (n2w d) /\
   abi_decoder_operand_live sa.cs_next_var (Var root)` by
    simp[eval_operand_def, calldata_operand_live_not_fresh] >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  qexistsl_tac [`H`,`u`] >>
  gvs[cj 4 control_moves_keep_vars, allocas_from_def] >> metis_tac[]
QED

Theorem calldata_bulk_payload_run_pc:
  abi_decode_bulk_payload dst src cnt mem_sz CALLDATALOAD sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  !k. run_inst_seq (emitted_insts sa sb) (s with vs_inst_idx := k) =
    OK (t with vs_inst_idx := k)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, comp_bind_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] sa = (sz,c1)` >>
     rename1 `emit_op ADD [src; Lit 32w] c1 = (sd,c2)` >>
     rename1 `emit_op ADD [dst; Lit 32w] c2 = (dd,c3)` >>
     rename1 `emit_void _ [dd;sd;sz] c3 = ((),sb)` >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
       emitted_insts c2 c3 ++ emitted_insts c3 sb` by
       (imp_res_tac inst_extends_trans >> metis_tac[emitted_insts_append, inst_extends_def]) >>
     imp_res_tac emitted_insts_emit_op >> drule emitted_insts_emit_void >>
     simp[mk_inst_def, is_terminator_def, abi_decode_copy_opcode_def]) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED
