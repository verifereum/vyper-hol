(* Empty windows still emit ADD; modular endpoints need no access coverage. *)
Theory bodyPtrAbiEncodeEndpoint
Ancestors
  bodyPtrAbiEncodeOffset typedCopyPtr exprLoweringProps emitHelperProps context
  compileEnv emitHelper fragGasSeqPtr fragGasPathPtr fragExecPtr bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map words

Theorem abi_encode_endpoint_sequence_checks:
  !op st st' root s a G tn off ctx D fn PG.
  emit_op ADD [Var root; Lit (n2w off)] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\ ~ctx_has_dalloca ctx ==>
  ?p t Gf tnf.
    op = Var p /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    lookup_var p t = SOME (a+n2w off) /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
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
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst st.cs_next_id ADD [Var root; Lit (n2w off)] [p]) s = OK t` by
    simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, Abbr `t`] >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, Abbr `Gf`, Abbr `tnf`,
       Abbr `t`, copy_len_binop_ghost_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`] >>
  rpt strip_tac >>
  `q <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
  simp[GSYM update_var_def, copy_len_binop_ghost_frame]
QED

Theorem abi_encode_endpoint_checked_ptr_path:
  !op st st' root s a G tn off ctx D fn PG bb limit_st.
  emit_op ADD [Var root; Lit (n2w off)] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\ ~ctx_has_dalloca ctx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t Gf tnf.
    op = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+1)) /\
    lookup_var p t = SOME (a+n2w off) /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_endpoint_sequence_checks >>
  disch_then (qspecl_then [`G`, `D`, `fn`, `PG`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st t` by
    (drule_all abi_encode_offset_fresh_vars >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[]
QED

(* Endpoint computations: no allocated memory or nonwrapping address is needed. *)
Theorem abi_encode_empty_endpoint_run:
  !root s a id total p. lookup_var root s = SOME a ==>
  run_inst_seq [mk_inst id ADD [Var root; Lit (n2w total)] [p]] s =
    OK (update_var p (a+n2w total) s)
Proof
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def]
QED

Theorem abi_encode_zero_extent_run:
  lookup_var root s = SOME a ==>
  run_inst_seq [mk_inst id ADD [Var root; Lit 0w] [p]] s =
    OK (update_var p a s)
Proof
  strip_tac >> drule abi_encode_empty_endpoint_run >>
  disch_then (qspecl_then [`id`, `0`, `p`] mp_tac) >> simp[WORD_ADD_0]
QED
