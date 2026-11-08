(* Canonical member navigation from facts at the parent's entry state. *)
Theory canonicalMemberTraversalPtr
Ancestors sourcePrimitiveMemberPtr abiDecoderMemberSetup abiDecoderMemberCode
  abiDecoderDynamicLoopSetup decoderMemberPrefixPtr abiDecoderContract
  abiDecoderReentry compileEnv ghostPcTransportPtr ptrDiscipline bodyPtrDefs
  venomState venomExecSemantics exprLoweringProps fragExec words arithmetic
  finite_map list abiEncoder emitHelperProps entrySinkExtraction

Theorem straight_sequence_inst_idx[local]:
  !is s t. EVERY (\i. ~is_terminator i.inst_opcode) is /\
    run_inst_seq is s = OK t ==> t.vs_inst_idx = s.vs_inst_idx
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  drule_all step_inst_base_preserves_inst_idx >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Theorem calldata_member_setup_source_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  eval_operand src s = SOME (n2w srcpos) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (srcpos + ao) : bytes32) s = n2w off /\
    srcpos + off < dimword (:256)) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\ fresh_vars_wrt mid s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt mid r /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME (n2w (srcpos + if dyn then off else ao)) /\
    ptr_covers H u q r C /\ op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`, `limit_st` |-> `st'`]
      abi_decode_member_setup_reentry)) >> strip_tac >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`] abi_decode_member_setup_shape)) >> strip_tac >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[w2n_n2w, LESS_MOD] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa mid) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa mid)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `t.vs_inst_idx = s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb` by
    metis_tac[straight_sequence_inst_idx, run_inst_seq_preserves_entry_control] >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `H`, `u`, `q`] >>
  gvs[w2n_n2w, LESS_MOD, lookup_var_def, fresh_vars_wrt_def,
    abi_decoder_address_frame_def] >>
  conj_tac >- simp[venom_state_component_equality] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >> simp[]
QED
