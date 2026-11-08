(* Arithmetic endpoints with raw ordinary states and compiler-normalized safety PCs. *)
Theory decoderRawEndpointPtr
Ancestors decoderNavigationPtr decoderArraySetupPtr bodyPtrDefs ptrDiscipline
  ptrSafeRun compileEnv emitHelper emitHelperProps exprLoweringProps venomInst
  venomState venomExecSemantics instIdxIndep moduleLoweringProps words list
  finite_map arithmetic

Theorem emit_scalar_binop_raw_endpoint_ptr:
  (opc = ADD \/ opc = MUL) /\
  emit_op opc [left;right] sa = (out,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    eval_operand out t = SOME (if opc = ADD then a + b else a * b) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_labels = s.vs_labels /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand out t = SOME (if opc = ADD then a + b else a * b) /\
   t.vs_labels = s.vs_labels /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq (emitted_insts sa sb)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     fs[is_terminator_def, exec_result_map_def]) >>
  `eval_operand left (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a /\
   eval_operand right (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME b` by
    (Cases_on `left` >> Cases_on `right` >> gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `run_inst_seq _ s = _` kall_tac >>
  drule_all emit_scalar_binop_endpoint_ptr_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >>
  fs[cj 4 control_moves_keep_vars, allocas_from_def] >> metis_tac[]
QED

Theorem emit_ptr_offset_raw_endpoint_ptr:
  emit_op ADD [Var root;offset] sa = (out,sb) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ op_prov G offset = NONE /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q.
    out = Var q /\ lookup_var q t = SOME (n2w (w2n a + off)) /\
    ptr_covers H u q t n /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_labels = s.vs_labels /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t.vs_labels = s.vs_labels /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def]) >>
  `run_inst_seq (emitted_insts sa sb)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `lookup_var root (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a /\
   ptr_covers G tn root (s with vs_inst_idx := LENGTH sa.cs_current_insts) capacity /\
   eval_operand offset (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME (n2w off)` by
    (Cases_on `offset` >> gvs[ptr_covers_def, eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `run_inst_seq _ s = _` kall_tac >>
  drule_all (Q.INST [`off` |-> `off`, `n` |-> `n`, `total` |-> `capacity`]
    (SPEC_ALL emit_ptr_offset_endpoint_ptr_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`] >>
  gvs[cj 4 control_moves_keep_vars, allocas_from_def, ptr_covers_def, lookup_var_def] >>
  metis_tac[]
QED
