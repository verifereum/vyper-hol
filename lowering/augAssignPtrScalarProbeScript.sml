(* Bounded scalar instruction/sequence interface probe. *)
Theory augAssignPtrScalarProbe
Ancestors augAssignPtrInterfaces bodyPtrDefs typedCopyPtr fragGasSeqPtr
  ptrDiscipline ptrSafeRun venomInst venomState venomExecSemantics
  finite_map pred_set codegenRel contextCodegenRel

Theorem add_sub_clean_metadata:
  (opc = ADD \/ opc = SUB) /\ op_prov G x = NONE /\ op_prov G y = NONE ==>
  op_prov (step_prov PG G (mk_inst id opc [x;y] [z]) u) (Var z) = NONE /\
  op_taint (step_taint (mk_inst id opc [x;y] [z]) s u tn) (Var z) = {} /\
  (!q. q <> z ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [x;y] [z]) u) q = FLOOKUP G q /\
    op_taint (step_taint (mk_inst id opc [x;y] [z]) s u tn) (Var q) =
      op_taint tn (Var q))
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, op_prov_def, op_taint_def,
       out_taint_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand x s` >> simp[]
QED

Theorem add_assert_sequence_ptr:
  ~ctx_has_dalloca ctx /\ op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} ==>
  ?H tm. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []] s H tm
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ADD [x;y] [z]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  Cases_on `step_inst_base (mk_inst id ADD [x;y] [z]) s` >>
  simp[inst_seq_ptr_def] >>
  `op_taint (step_taint (mk_inst id ADD [x;y] [z]) s v tn) (Var z) = {}` by
    metis_tac[add_sub_clean_metadata] >>
  simp[ptr_inst_ok_assert] >>
  Cases_on `step_inst_base (mk_inst aid ASSERT [Var z] [])
    (v with vs_inst_idx := SUC s.vs_inst_idx)` >> simp[]
QED

Theorem add_assert_success_path_ptr:
  ~ctx_has_dalloca ctx /\ op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []] s = OK t ==>
  ?H tm. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
    (OK (t with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  strip_tac >>
  `?H tm. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []] s H tm` by
    (irule add_assert_sequence_ptr >> simp[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `bb`] mp_tac) >>
  gvs[mk_inst_def, is_terminator_def] >> metis_tac[]
QED

Theorem add_assert_abort_path_ptr:
  ~ctx_has_dalloca ctx /\ op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []] s = Abort a t ==>
  ?H tm n j. gas_path_ptr D 0 ctx fn PG G tn s n H tm
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `?H tm. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []] s H tm` by
    (irule add_assert_sequence_ptr >> simp[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_abort_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `a`, `bb`] mp_tac) >>
  gvs[mk_inst_def, is_terminator_def] >> metis_tac[]
QED

Theorem add_sub_ambient_taint:
  (opc = ADD \/ opc = SUB) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, mk_inst_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def]
QED

Theorem add_sub_ptr_inst_ok:
  (opc = ADD \/ opc = SUB) /\ op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [x;y] [z]) s
Proof
  strip_tac >> gvs[]
  >- (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                  combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
