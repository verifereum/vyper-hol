(* Concrete pointer checks for RawLog's fixed-data continuation. *)
Theory bodyFullRawLogFixedTailPath
Ancestors
  bodyFullRawLogFixedBoundary rawLogPtrInst bodyPtrDefs ptrDiscipline
  ptrSafeRun venomState venomInst venomExecSemantics words list
  rawLogCoreFrame fragGasSeqPtr wordLoadStorePtr exprPtrUnwrapCopyEdges
  instMemFrontier emitHelper compileEnv fragExecMem fragExec
  venomMemDefs valueEncodingProps rich_list finite_map arithmetic

Theorem raw_log_fixed_log_inst_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\
  eval_operands topics s = SOME vals /\
  (?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + 32 <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\
  (!i. w2n off <= i /\ i < w2n off + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok_at D tn s /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s = OK t ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s
Proof
  strip_tac >>
  `access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_access_ok >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `access_ok lo G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (gvs[access_ok_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_EQ_0]) >>
  `taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_taint_ok >> simp[eval_operand_def, op_taint_def, dimword_def] >> metis_tac[]) >>
  gvs[ptr_inst_ok_def, stor_taint_ok_at_def, mk_inst_def, step_inst_non_invoke]
QED

Theorem raw_log_fixed_store_step:
  emit_void MSTORE [Var p;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) [] s1 = ((),sb) /\
  eval_operand (Var p) s = SOME w /\ eval_operand data_op s = SOME word /\
  ptr_covers G tn p s 32 /\ op_taint tn data_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst id MSTORE [Var p;data_op] [];
      t = mstore (w2n w) word s;
      tf = step_taint i s t tn
  in
    step_inst_base i s = OK t /\ ptr_inst_ok D lo 0 ctx func G tn i s /\
    step_prov PG G i t = G /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {j | w2n w <= j /\ j < w2n w + 32} /\
    ptr_covers G tf p t 32 /\
    EVERY (\op. op_taint tf op = {}) ops = EVERY (\op. op_taint tn op = {}) ops /\
    (!j. w2n w <= j /\ j < w2n w+32 ==> j NOTIN tf.t_mem) /\
    allocas_from lo t /\ stor_taint_ok_at D tn s = stor_taint_ok_at D tf t
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `lookup_var p s = SOME w` by gvs[eval_operand_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`id`] strip_assume_tac) >>
  simp[] >> conj_tac
  >- simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  ` (step_taint (mk_inst id MSTORE [Var p;data_op] []) s
      (mstore (w2n w) word s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, imm_taint_def] >>
  gvs[ptr_covers_def, mstore_def, lookup_var_def, allocas_from_def,
       stor_taint_ok_at_def, op_taint_def] >> metis_tac[]
QED
