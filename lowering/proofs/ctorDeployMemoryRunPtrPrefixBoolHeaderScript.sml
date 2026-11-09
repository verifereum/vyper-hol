(* The repeatedly visited Bool decoder header: closed local certificates. *)
Theory ctorDeployMemoryRunPtrPrefixBoolHeader
Ancestors
  ctorDeployMemoryRunPtrPrefixHeader ctorDeployMemoryRunPtrPrefixBoolShape
  ctorDeployMemoryRunPtrPrefixWordRead ctorDeployMemoryRunPtrPrefixBoolWord
  ctorDeployMemoryRunPtrPrefixSteps instIdxIndep
  abiDecoderExecution abiDecoderContract emitHelperProps ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic
  list rich_list finite_map pred_set codegenRel contextCodegenRel memLocDefs

Theorem prefix_bool_header_state_frames:
  ALL_DISTINCT [ip;src;dst;iv;cv;cmp;done] ==>
  let h = abi_decode_header_state iv cv cmp done i ncount s;
      t = jump_to target h
  in
    t.vs_memory = s.vs_memory /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!v. MEM v [ip;src;dst] ==>
      eval_operand (Var v) t = eval_operand (Var v) s)
Proof
  simp[abi_decode_header_state_def, jump_to_def, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem prefix_bool_header_execution:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  ALL_DISTINCT [ip;src;dst;iv;cv;cmp;done] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  scratch < dimword(:256) /\ mload scratch s = n2w i /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) ==>
  !f. exec_block f ctx
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id (Var ip) (Var src) DLOAD iv cv cmp done body_lbl exit_lbl|> s =
    OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s))
Proof
  rpt strip_tac >> irule abi_decode_header_control >>
  simp[abi_decode_source_opcode_def] >>
  gvs[w2n_n2w]
QED

Theorem prefix_bool_header_closed:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = hdr /\
  ALL_DISTINCT [ip;src;dst;iv;cv;cmp;done] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  mload scratch s = n2w i /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) /\
  FLOOKUP G ip = SOME (scratch,32) /\
  scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= scratch /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var src) = {} /\
  (!k. k < 32 ==> scratch+k NOTIN tn.t_mem) ==>
  let H = abi_decode_header_insts id (Var ip) (Var src) DLOAD iv cv cmp done body_lbl exit_lbl;
      bb = <|bb_label := hdr; bb_instructions := H|>;
      u1 = update_var iv (n2w i) s;
      u2 = update_var cv (n2w ncount) u1;
      u3 = update_var cmp (bool_to_word (i < ncount)) u2;
      h = update_var done (bool_to_word (~(i < ncount))) u3;
      t = jump_to (if i < ncount then body_lbl else exit_lbl) h;
      g1 = DRESTRICT G (COMPL {iv});
      g2 = DRESTRICT g1 (COMPL {cv});
      g3 = DRESTRICT g2 (COMPL {cmp});
      Gh = DRESTRICT g3 (COMPL {done});
      q1 = step_taint (EL 0 H) s u1 tn;
      q2 = step_taint (EL 1 H) (u1 with vs_inst_idx := 1) (u2 with vs_inst_idx := 1) q1;
      q3 = step_taint (EL 2 H) (u2 with vs_inst_idx := 2) (u3 with vs_inst_idx := 2) q2;
      th = step_taint (EL 3 H) (u3 with vs_inst_idx := 3) (h with vs_inst_idx := 3) q3
  in
    lookup_block hdr fn.fn_blocks = SOME bb ==>
    (!f. exec_block f ctx bb s = OK t) /\
    (!f. ptr_safe_blocks D lo f ctx fn PG
       (entry_prov fn t Gh) (entry_taint_vars fn t th) t ==>
       ptr_safe_blocks D lo (SUC f) ctx fn PG G tn s) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    op_taint th (Var iv) = {} /\ op_taint th (Var cv) = {} /\
    op_taint th (Var cmp) = {} /\ op_taint th (Var done) = {} /\
    (!v. MEM v [ip;src;dst] ==>
      eval_operand (Var v) t = eval_operand (Var v) s /\
      FLOOKUP Gh v = FLOOKUP G v /\ op_taint th (Var v) = op_taint tn (Var v))
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `H = abi_decode_header_insts id (Var ip) (Var src) DLOAD iv cv cmp done body_lbl exit_lbl` >>
  qabbrev_tac `bb = <|bb_label := hdr; bb_instructions := H|>` >>
  qabbrev_tac `u1 = update_var iv (n2w i) s` >>
  qabbrev_tac `u2 = update_var cv (n2w ncount) u1` >>
  qabbrev_tac `u3 = update_var cmp (bool_to_word (i < ncount)) u2` >>
  qabbrev_tac `h = update_var done (bool_to_word (~(i < ncount))) u3` >>
  qabbrev_tac `t = jump_to (if i < ncount then body_lbl else exit_lbl) h` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {iv})` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {cv})` >>
  qabbrev_tac `g3 = DRESTRICT g2 (COMPL {cmp})` >>
  qabbrev_tac `Gh = DRESTRICT g3 (COMPL {done})` >>
  qabbrev_tac `q1 = step_taint (EL 0 H) s u1 tn` >>
  qabbrev_tac `q2 = step_taint (EL 1 H) (u1 with vs_inst_idx := 1) (u2 with vs_inst_idx := 1) q1` >>
  qabbrev_tac `q3 = step_taint (EL 2 H) (u2 with vs_inst_idx := 2) (u3 with vs_inst_idx := 2) q2` >>
  qabbrev_tac `th = step_taint (EL 3 H) (u3 with vs_inst_idx := 3) (h with vs_inst_idx := 3) q3` >>
  `scratch < dimword(:256)` by decide_tac >>
  conj_tac
  >- (drule_all prefix_bool_header_execution >>
      simp[Abbr `t`, Abbr `h`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
           Abbr `bb`, Abbr `H`, abi_decode_header_state_def]) >>
  conj_tac >- suspend "safety" >> suspend "frames"
QED

Resume prefix_bool_header_closed[frames]:
  `!v. MEM v [u1;u2;u3;h] ==>
    v.vs_allocas = s.vs_allocas /\ v.vs_fmp = s.vs_fmp` by
    (rw[] >> simp[Abbr `u1`, Abbr `u2`, Abbr `u3`, Abbr `h`, update_var_def]) >>
  `q1.t_mem = tn.t_mem /\ q1.t_stor = tn.t_stor /\
   q1.t_trans = tn.t_trans /\ q1.t_imm = tn.t_imm /\
   (!v. v <> iv ==> op_taint q1 (Var v) = op_taint tn (Var v))` by
    (simp[Abbr `q1`, Abbr `H`, abi_decode_header_insts_def] >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >> simp[]) >>
  `q2.t_mem = q1.t_mem /\ q2.t_stor = q1.t_stor /\
   q2.t_trans = q1.t_trans /\ q2.t_imm = q1.t_imm /\
   (!v. v <> cv ==> op_taint q2 (Var v) = op_taint q1 (Var v))` by
    (simp[NoAsms, Abbr `q2`, Abbr `H`, abi_decode_header_insts_def] >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >> gvs[]) >>
  `q3.t_mem = q2.t_mem /\ q3.t_stor = q2.t_stor /\
   q3.t_trans = q2.t_trans /\ q3.t_imm = q2.t_imm /\
   (!v. v <> cmp ==> op_taint q3 (Var v) = op_taint q2 (Var v))` by
    (simp[NoAsms, Abbr `q3`, Abbr `H`, abi_decode_header_insts_def] >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >> gvs[]) >>
  `th.t_mem = q3.t_mem /\ th.t_stor = q3.t_stor /\
   th.t_trans = q3.t_trans /\ th.t_imm = q3.t_imm /\
   (!v. v <> done ==> op_taint th (Var v) = op_taint q3 (Var v))` by
    (simp[NoAsms, Abbr `th`, Abbr `H`, abi_decode_header_insts_def] >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >> gvs[]) >>
  `op_taint q1 (Var iv) = {}` by
    (simp[Abbr `q1`, Abbr `H`, abi_decode_header_insts_def] >>
     irule prefix_mload_output_clean >> simp[w2n_n2w] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < 32 ==> scratch + k NOTIN tn.t_mem`
       (qspec_then `k` mp_tac) >> simp[ADD_COMM]) >>
  `op_taint q2 (Var cv) = {} /\ op_taint q3 (Var cmp) = {} /\
   op_taint th (Var done) = {}` by
    simp[Abbr `q2`, Abbr `q3`, Abbr `th`, Abbr `H`,
         abi_decode_header_insts_def, prefix_dload_output_taint,
         prefix_guard_output_taint] >>
  simp[Abbr `t`, Abbr `h`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
       jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, Abbr `Gh`, Abbr `g3`, Abbr `g2`, Abbr `g1`,
       FLOOKUP_DRESTRICT] >>
  gvs[] >> metis_tac[]
QED

Resume prefix_bool_header_closed[safety]:
  gen_tac >> strip_tac >>
  `op_taint q1 (Var iv) = {}` by
    (simp[Abbr `q1`, Abbr `H`, abi_decode_header_insts_def] >>
     irule prefix_mload_output_clean >> simp[w2n_n2w] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < 32 ==> scratch+k NOTIN tn.t_mem`
       (qspec_then `k` mp_tac) >> simp[ADD_COMM]) >>
  `op_taint q2 (Var iv) = {} /\ op_taint q2 (Var cv) = {} /\
   op_taint q3 (Var cmp) = {} /\ op_taint th (Var done) = {}` by
    (gvs[] >> simp[Abbr `q2`, Abbr `q3`, Abbr `th`, Abbr `H`,
         abi_decode_header_insts_def, prefix_guard_taint_other,
         prefix_dload_output_taint, prefix_guard_output_taint]) >>
  `abi_decode_header_state iv cv cmp done i ncount s = h` by
    simp[abi_decode_header_state_def, Abbr `h`, Abbr `u3`, Abbr `u2`, Abbr `u1`] >>
  `jump_to (if i < ncount then body_lbl else exit_lbl) h = t` by simp[Abbr `t`] >>
  irule (cj 2 (SRULE [LET_THM] prefix_decode_dload_header_entry_pair)) >>
  simp[] >>
  qexistsl [`n2w a:bytes32`, `body_lbl`, `cmp`, `cv`, `done`, `exit_lbl`,
    `\j. EL j [G;g1;g2;g3;Gh]`, `i`, `id`, `Var ip`, `iv`, `ncount`,
    `n2w scratch:bytes32`, `\j. EL j [tn;q1;q2;q3;th]`, `Var src`,
    `\j. EL j [s;u1;u2;u3;h]`] >>
  simp[Abbr `bb`, Abbr `H`, w2n_n2w] >>
  conj_tac >- suspend "trace" >> suspend "branch"
QED

Resume prefix_bool_header_closed[trace]:
  gen_tac >> strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
  gvs[abi_decode_header_insts_def]
  >- suspend "mload"
  >- suspend "dload"
  >- suspend "lt"
  >> suspend "iszero"
QED

Resume prefix_bool_header_closed[mload]:
  qpat_assum `eval_operand (Var ip) s = _` (mp_then Any assume_tac prefix_mload_step) >>
  qpat_assum `eval_operand (Var ip) s = _` (mp_then Any assume_tac (SRULE [LET_THM] prefix_mload_ghost_step)) >>
  simp[step_inst_non_invoke, Abbr `u1`, Abbr `g1`, Abbr `q1`, w2n_n2w, update_var_def] >>
  irule prefix_mload_ptr_step >> simp[w2n_n2w] >> metis_tac[]
QED

Resume prefix_bool_header_closed[dload]:
  `op_taint q1 (Var src) = {}` by
    simp[Abbr `q1`, prefix_guard_taint_other] >>
  `eval_operand (Var src) u1 = SOME (n2w a)` by
    simp[Abbr `u1`, eval_operand_def, lookup_var_update_var, GSYM eval_operand_def] >>
  `step_inst_base (mk_inst (id+1) DLOAD [Var src] [cv]) u1 = OK u2` by
    (qpat_assum `eval_operand (Var src) u1 = _`
       (mp_then Any mp_tac prefix_dload_step) >>
     gvs[Abbr `u2`, Abbr `u1`, abi_decode_load_def, abi_decode_source_def, update_var_def]) >>
  simp[step_inst_non_invoke] >>
  conj_tac >- simp[step_inst_inst_idx_indep, mk_inst_def,
                   is_terminator_def, exec_result_map_def] >>
  conj_tac >- (irule prefix_dload_ptr_step >>
    gvs[Abbr `u1`, allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[ghost_step_def, step_inst_non_invoke, Abbr `g2`, Abbr `q2`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def, exec_result_map_def]
QED
Resume prefix_bool_header_closed[lt]:
  `step_inst_base (mk_inst (id+2) LT [Var iv;Var cv] [cmp]) u2 = OK u3` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          Abbr `u3`, Abbr `u2`, Abbr `u1`, eval_operand_def,
          lookup_var_update_var, WORD_LO, w2n_n2w] >>
     `i < dimword(:256)` by decide_tac >> simp[]) >>
  simp[step_inst_non_invoke] >>
  conj_tac >- simp[step_inst_inst_idx_indep, mk_inst_def,
                   is_terminator_def, exec_result_map_def] >>
  conj_tac >- (irule prefix_compare_ptr_step >>
    gvs[Abbr `u2`, Abbr `u1`, Abbr `g2`, Abbr `g1`, op_prov_def,
        FLOOKUP_DRESTRICT, allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[ghost_step_def, step_inst_non_invoke, Abbr `g3`, Abbr `q3`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def, exec_result_map_def]
QED
Resume prefix_bool_header_closed[iszero]:
  `step_inst_base (mk_inst (id+3) ISZERO [Var cmp] [done]) u3 =
    OK (abi_decode_header_state iv cv cmp done i ncount s)` by
    (qpat_x_assum `update_var done _ u3 = _` kall_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
          Abbr `u3`, Abbr `u2`, Abbr `u1`, eval_operand_def,
          lookup_var_update_var, abi_decode_header_state_def] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def]) >>
  simp[step_inst_non_invoke] >>
  conj_tac >- simp[step_inst_inst_idx_indep, mk_inst_def,
                   is_terminator_def, exec_result_map_def] >>
  conj_tac >- (irule prefix_iszero_ptr_step >>
    gvs[Abbr `u3`, Abbr `u2`, Abbr `u1`,
        allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[ghost_step_def, step_inst_non_invoke, Abbr `Gh`, Abbr `th`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def, exec_result_map_def]
QED

Resume prefix_bool_header_closed[branch]:
  gvs[abi_decode_header_insts_def] >>
  qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `update_var done _ u3 = _` kall_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
       taint_ok_def, step_inst_non_invoke, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def,
       abi_decode_header_state_def,
       step_inst_base_opcode_eqs, eval_operand_def, lookup_var_update_var,
       allocas_from_def, update_var_def, jump_to_def] >>
  conj_tac >- (Cases >> gvs[op_taint_def]) >>
  gvs[Abbr `u1`, allocas_from_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `i < ncount` >> gvs[bool_to_word_def] >> metis_tac[]
QED

Finalise prefix_bool_header_closed


val _ = export_theory();
