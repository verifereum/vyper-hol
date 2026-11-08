(* Non-call edges used by the shared SHA256 tail. *)
Theory bodyPtrHashBuiltinsShaTailSteps
Ancestors bodyPtrHashBuiltinsShaCall bodyPtrHashBuiltinsKeccakBytesRun
  typedCopyPtr bodyPtrDefs fragGasSeqPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState contextCodegenRel codegenRel
  words finite_map pred_set

Theorem hash_gas_step:
  !id out s.
    step_inst_base (mk_inst id GAS [] [out]) s =
      OK (update_var out (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings))
Proof
  rpt gen_tac >> Cases_on `s.vs_gas_readings` >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_gas_def, update_var_def, venom_state_component_equality]
QED

Theorem hash_gas_inst_ok:
  !D ctx fn G tn id out s.
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id GAS [] [out]) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    allocas_from_def, step_inst_non_invoke, hash_gas_step, mk_inst_def,
    update_var_def]
QED

Theorem hash_gas_ghost:
  !PG G tn id out s.
    step_prov PG G (mk_inst id GAS [] [out])
      (update_var out (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings)) =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id GAS [] [out]) s
      (update_var out (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings)) tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt gen_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    mk_inst_def, set_var_taint_def, out_taint_def, mem_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, written_taint_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION,
    SF CONJ_ss, taint_component_equality]
QED

Theorem hash_assert_inst_ok:
  !D ctx fn G tn id op s.
    ~ctx_has_dalloca ctx /\ op_taint tn op = {} ==>
    ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    allocas_from_def, step_inst_non_invoke, mk_inst_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[] >> Cases_on `eval_operand op s` >> simp[] >>
  rename1 `eval_operand op s = SOME w` >>
  Cases_on `w = 0w` >> simp[]
QED

Theorem hash_assert_ghost:
  !PG G tn id op s.
    step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
    step_taint (mk_inst id ASSERT [op] []) s s tn = tn
Proof
  rpt gen_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    mk_inst_def, set_var_taint_def, out_taint_def, mem_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, written_taint_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
    taint_component_equality, DRESTRICT_UNIV]
QED

Theorem hash_sha256_load_pair:
  !D ctx fn PG G tn s ia im success q out r.
    lookup_var success s = SOME 1w /\
    op_taint tn (Var success) = {} /\
    eval_operand (Var q) s = SOME r /\ ptr_covers G tn q s 32 /\
    (!i. w2n r <= i /\ i < w2n r+32 ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s
      (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst ia ASSERT [Var success] []) s = OK s` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule hash_assert_inst_ok >> simp[]) >>
  simp[hash_assert_ghost] >>
  qabbrev_tac `u = s with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand (Var q) u = SOME r /\ ptr_covers G tn q u 32` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, ptr_covers_def] >>
  `step_inst_base (mk_inst im MLOAD [Var q] [out]) u =
     OK (update_var out (mload (w2n r) u) u)` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  drule_all hash_mload_ghost >> strip_tac >>
  simp[inst_seq_ptr_def]
QED

Theorem hash_sha256_assert_abort_check:
  !D ctx fn PG G tn s ia im success q out.
    lookup_var success s = SOME 0w /\
    op_taint tn (Var success) = {} /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s G tn
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst ia ASSERT [Var success] []) s =
    Abort Revert_abort (revert_state (set_returndata [] s))` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >> irule hash_assert_inst_ok >> simp[]
QED

Theorem hash_sha256_load_path:
  !D ctx fn PG G tn s t bb ia im success q out r.
    lookup_var success s = SOME 1w /\
    op_taint tn (Var success) = {} /\
    eval_operand (Var q) s = SOME r /\ ptr_covers G tn q s 32 /\
    (!i. w2n r <= i /\ i < w2n r+32 ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]]
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s = OK t ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (t with vs_inst_idx := s.vs_inst_idx+2))
Proof
  rpt gen_tac >> strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn
     [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s
     (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule hash_sha256_load_pair >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED

Theorem hash_sha256_assert_abort_path:
  !D ctx fn PG G tn s bb ia im success q out.
    lookup_var success s = SOME 0w /\
    op_taint tn (Var success) = {} /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst ia ASSERT [Var success] []) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
      (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst ia ASSERT [Var success] []) s` by
    (irule hash_assert_inst_ok >> simp[]) >>
  `step_inst_base (mk_inst ia ASSERT [Var success] []) s =
    Abort Revert_abort (revert_state (set_returndata [] s))` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = Abort _ _`) gas_path_ptr_abort >>
  simp[mk_inst_def, is_terminator_def] >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem hash_gas_prefix_check:
  !D ctx fn PG G tn id gas code s G' tn'.
    ~ctx_has_dalloca ctx /\
    inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {gas}))
      (tn with t_var := tn.t_var |+ (gas,{})) code
      (update_var gas (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings)
        with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
    inst_seq_ptr D 0 ctx fn PG G tn (mk_inst id GAS [] [gas]::code) s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once inst_seq_ptr_def, hash_gas_step] >>
  conj_tac >- (irule hash_gas_inst_ok >> simp[]) >>
  gvs[SRULE [] (cj 1 hash_gas_ghost), SRULE [] (cj 2 hash_gas_ghost)]
QED
