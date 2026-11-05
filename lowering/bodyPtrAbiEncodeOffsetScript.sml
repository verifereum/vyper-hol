(* An emitted ADD is retained even for byte offset zero. *)
Theory bodyPtrAbiEncodeOffset
Ancestors
  typedCopyPtr exprLoweringProps emitHelperProps context compileEnv emitHelper
  fragGasSeqPtr fragGasPathPtr fragExecPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map words

Theorem abi_encode_add_coverage[local]:
  !root s a G tn total off n PG id p.
  lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
  off < total /\ off+n <= total /\ w2n a+off < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [p])
      (update_var p (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [p]) s
      (update_var p (a+n2w off) s) tn)
    p (update_var p (a+n2w off) s) n
Proof
  rpt gen_tac >> strip_tac >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, w2n_add_2, w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem abi_encode_offset_sequence_checks:
  !op st st' root s a G tn total off n ctx D fn PG.
  emit_op ADD [Var root; Lit (n2w off)] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
  w2n a+off < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?p t Gf tnf.
    op = Var p /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    lookup_var p t = SOME (n2w (w2n a+off)) /\
    ptr_covers Gf tnf p t n /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `t = update_var p (a+n2w off) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) s t tn` >>
  `ptr_covers Gf tnf p t n` by
    (simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`] >>
     irule abi_encode_add_coverage >> simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def] >>
     gvs[ptr_covers_def, op_taint_def]) >>
  `step_inst_base (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) s = OK t` by
    simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, Abbr `t`] >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, Abbr `Gf`, Abbr `tnf`,
       Abbr `t`, copy_len_binop_ghost_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, GSYM word_add_n2w, WORD_ADD_COMM] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`] >>
  rpt strip_tac >>
  `q <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
  simp[GSYM update_var_def, copy_len_binop_ghost_frame]
QED

Theorem abi_encode_offset_fresh_vars:
  emit_op ADD [Var root; Lit (n2w off)] st = (op,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  lookup_var root s = SOME a /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def] >>
  irule fresh_vars_wrt_update_var >> simp[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem abi_encode_offset_checked_ptr_path:
  !op st st' root s a G tn total off n ctx D fn PG bb.
  emit_op ADD [Var root; Lit (n2w off)] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
  w2n a+off < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t Gf tnf.
    op = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+1)) /\
    lookup_var p t = SOME (n2w (w2n a+off)) /\
    ptr_covers Gf tnf p t n /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_offset_sequence_checks >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[]
QED
