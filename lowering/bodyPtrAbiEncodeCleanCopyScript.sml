(* Dynamic-length MCOPY has the same exact write/taint frame as fixed copies. *)
Theory bodyPtrAbiEncodeCleanCopy
Ancestors
  bodyPtrAbiEncodeCursorFrame bodyPtrDefs bodyPtrAbiEncodeCleanStore typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  words list arithmetic pred_set finite_map codegenRel

Theorem abi_encode_clean_copy_sequence:
  emit_void MCOPY [Var dst;Var src;len] st = ((),en) /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  eval_operand len s = SOME (n2w sz) /\ sz < dimword(:256) /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {} /\ op_taint tn len = {} /\
  ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz /\
  (!i. w2n a <= i /\ i < w2n a+sz ==> i NOTIN tn.t_mem) /\ ~ctx_has_dalloca ctx ==>
  run_inst_seq (emitted_insts st en) s = OK (mcopy (w2n b) (w2n a) sz s) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st en) s G
    (tn with t_mem := tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+sz})
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id MCOPY [Var dst;Var src;len] []) s` by
    (irule ptr_inst_ok_mcopy_operand >> simp[w2n_n2w] >>
     goal_assum $ drule_at Any >> simp[w2n_n2w]) >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a` by
    simp[eval_operand_def] >>

  `{w2n b+i | i < sz /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >>
     first_x_assum (qspec_then `w2n a+i` mp_tac) >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst st.cs_next_id MCOPY [Var dst;Var src;len] []) s =
     OK (mcopy (w2n b) (w2n a) sz s)` by
    simp[Once step_inst_base_def, mk_inst_def, eval_operand_def, w2n_n2w] >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  simp[taint_component_equality, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, mk_inst_def, set_var_taint_def, DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, imm_taint_def] >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       written_taint_def, range_bytes_def, new_site_bytes_def,
       mcopy_def, write_memory_with_expansion_def, FLOOKUP_DEF, w2n_n2w] >>
  qpat_x_assum `{w2n b+i | i < sz /\ w2n a+i IN tn.t_mem} = {}` mp_tac >>
  simp[EXTENSION, ADD_COMM, SF CONJ_ss] >> metis_tac[]
QED

Theorem abi_encode_clean_copy_checked_path:
  emit_void MCOPY [Var dst;Var src;len] st = ((),en) /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  eval_operand len s = SOME (n2w sz) /\ sz < dimword(:256) /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {} /\ op_taint tn len = {} /\
  ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz /\
  (!i. w2n a <= i /\ i < w2n a+sz ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+sz})
    (OK ((mcopy (w2n b) (w2n a) sz s) with vs_inst_idx := s.vs_inst_idx+1))
Proof
  strip_tac >> drule_all abi_encode_clean_copy_sequence >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED

Theorem abi_encode_read_frame_copy:
  abi_encode_read_frame st s G tn t H un ==>
  abi_encode_read_frame st (mcopy db sb n s) G
    (tn with t_mem := tn.t_mem DIFF removed)
    ((mcopy db sb n t) with vs_inst_idx := k) H
    (un with t_mem := un.t_mem DIFF removed)
Proof
  simp[abi_encode_read_frame_def, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def]
QED

Theorem abi_encode_clean_copy_covers:
  ptr_covers G tn q s n ==>
  ptr_covers G (tn with t_mem := tn.t_mem DIFF removed) q
    ((mcopy db sb sz s) with vs_inst_idx := k) n
Proof
  simp[ptr_covers_def, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def]
QED

Theorem abi_encode_clean_copy_fresh:
  fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st ((mcopy db sb n s) with vs_inst_idx := k)
Proof
  simp[fresh_vars_wrt_def, mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED
