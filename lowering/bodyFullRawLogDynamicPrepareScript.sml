(* RawLog's dynamic header and payload-address preparation. *)
Theory bodyFullRawLogDynamicPrepare
Ancestors
  bodyFullRawLogDynamicData fragGasSeqPtr
  exprSimHash bodyPtrDefs exprLowering compileEnv venomState
  ptrDiscipline valueEncodingDefs finite_map words list arithmetic
  emitHelper fragExec exprLoweringProps loweringStateRelDefs bodyFullGhostFrame
  ASCIInumbers venomExecSemantics venomInstProofs venomInst
Libs
  wordsLib

Theorem raw_log_dynamic_prepare_joint:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops) /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ ghost_inv_at D lo d cenv cx ee G tn s /\
  eval_operand data_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (?x. data_op = Var x /\
    ptr_covers G tn x s (32+32*word_size (LENGTH bs))) /\
  b+32+LENGTH bs <= s.vs_alloca_next /\
  (!i. b<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  eval_operands ops s = SOME topics /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  ?t G1 tn1.
    run_inst_seq (emitted_insts sm s2) s = OK t /\
    run_inst_seq_mem_ok (emitted_insts sm s2) s /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm s2) s G1 tn1 /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b+32)) /\
    eval_operands ops t = SOME topics /\
    EVERY (\op. op_taint tn1 op = {}) (ptr_op::len_op::ops) /\
    (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\
      ptr_covers G1 tn1 x t (LENGTH bs)) /\
    (!i. b+32<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn1.t_mem) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    ghost_inv_at D lo d cenv cx ee G1 tn1 t /\
    ghost_kept_at lo cenv ee sm G tn s G1 tn1
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `!x. data_op = Var x ==> not_fresh_at sm x` by fs[] >>
  drule_all hash_data_prefix_run >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  rename1 `ptr_covers G tn src s _` >>
  fs[emitted_insts_def, APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `STRING #"%" (toString nv)` >>
  qabbrev_tac `l = STRING #"%" (toString nv)` >>
  qabbrev_tac `p = STRING #"%" (toString (nv+1))` >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND] >>
  `!x. not_fresh_at sm x ==> x <> l /\ x <> p` by
    (simp[not_fresh_at_def, Abbr `l`, Abbr `p`, Abbr `nv`] >>
     metis_tac[DECIDE ``n <= n+1``]) >>
  `src <> l /\ src <> p` by metis_tac[] >>
  `l <> p` by
    simp[Abbr `l`, Abbr `p`, ASCIInumbersTheory.toString_inj] >>
  qabbrev_tac `u = update_var l (n2w (LENGTH bs)) s` >>
  qabbrev_tac `v = update_var p (n2w (b+32)) u` >>
  `step_inst_base (mk_inst sm.cs_next_id MLOAD [Var src] [l]) s = OK u` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, Abbr `u`, mload_def,
       GSYM mem_word_at_def]) >>
  `step_inst_base (mk_inst (sm.cs_next_id+1) ADD [Var src;Lit 32w] [p]) u = OK v` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `v`, Abbr `u`,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       word_add_n2w] >> fs[eval_operand_def, lookup_var_def, word_add_n2w]) >>
  `t = v` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     simp[run_inst_seq_def]) >>
  FAIL_TAC "ghosts"
QED
