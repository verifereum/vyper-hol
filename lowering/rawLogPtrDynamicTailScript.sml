(* Counted dynamic RawLog suffix with a full ghost endpoint. *)
Theory rawLogPtrDynamicTail
Ancestors
  rawLogPtrDynamic rawLogPtrInst bodyPtrHashBuiltinsGhostFrame bodyPtrDefs
  fragGasSeqPtr fragExec stmtReasonLitFragMemory emitHelper context compileEnv
  exprLoweringProps venomState venomInst venomExecSemantics ptrDiscipline
  words finite_map list rich_list

Theorem raw_log_dynamic_tail_ptr:
  !D ctx fn PG G tn s x sa len_op sl ptr_op sp u sb b root cap n ops vals
    d cenv cx es logs.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x; Lit 32w] sl = (ptr_op,sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] sp = (u,sb) /\
  not_fresh_at sa x /\ eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (root,cap) /\ root <= b /\ b+32+n <= root+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\
  op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ LENGTH ops < dimword (:256) /\
  eval_operands ops s = SOME vals /\
  EVERY (\op. !z. op = Var z ==> not_fresh_at sa z) ops /\
  EVERY (\op. op_taint tn op = {}) ops /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  ~s.vs_halted /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_inv d cenv cx (es with logs := logs) G' tn'
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv es sa G tn s G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
    t.vs_memory = s.vs_memory /\
    t.vs_logs = s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
         data := TAKE n (DROP (b+32) s.vs_memory ++ REPLICATE n 0w)|>]
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_log_dynamic_inst_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  conj_tac >- suspend "path" >>
  conj_tac
  >- (`ghost_inv d cenv cx es G' tn' mid` by
        (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
         simp[]) >>
      qpat_x_assum `t = mid with vs_logs := _` SUBST1_TAC >>
      simp[log_ghost_frame]) >>
  simp[ghost_kept_def]
QED

Resume raw_log_dynamic_tail_ptr[path]:
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >> simp[NoAsms] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     pure_rewrite_tac[DROP_LENGTH_APPEND] >>
     simp[NoAsms, mk_inst_def, is_terminator_def]) >>
  drule_all fn_has_code_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Finalise raw_log_dynamic_tail_ptr
