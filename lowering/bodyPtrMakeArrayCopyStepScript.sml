(* Raw copy steps permit tainted data, but never tainted addresses. *)
Theory bodyPtrMakeArrayCopyStep
Ancestors
  typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs venomInst
  venomExecSemantics venomState context ptrSafeRun ptrDiscipline memLocDefs codegenRel contextCodegenRel

Theorem ptr_inst_ok_mstore_raw:
  !D ctx fn G tn s id p v fuel.
    ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MSTORE [Var p; v] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem mstore_raw_ptr_path:
  ptr_covers G tn dst s 32 /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst; value] []) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MSTORE [Var dst; value] []`,
                     `lo` |-> `0`, `u` |-> `mstore (w2n (a:256 word)) w s`]
                    straight_line_ptr_edge) >>
     gvs[] >> simp[mk_inst_def, is_terminator_def, ptr_inst_ok_mstore_raw,
                  Once step_inst_base_def, exec_write2_def, eval_operand_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem ptr_inst_ok_external_load:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [src] [tmp]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem external_load_ptr_path:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [src] [tmp]) u)
    (step_taint (mk_inst id opc [src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [src] [tmp]) u)
    (step_taint (mk_inst id opc [src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id opc [src] [tmp]`, `lo` |-> `0`]
                    straight_line_ptr_edge) >>
     simp[ptr_inst_ok_external_load] >> gvs[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >>
  `step_inst 0 ctx (mk_inst id opc [src] [tmp]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_halted >>
  gvs[mk_inst_def, is_terminator_def]
QED

Theorem mstore_raw_ghost_frame:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
    (mstore (w2n a) w s) = G /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_var = tn.t_var /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_mem =
      (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}) UNION
      {w2n a + k | k IN op_taint tn value}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       store_taint_def, imm_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       eval_operand_def, written_taint_def, range_bytes_def, new_site_bytes_def,
       mstore_def, finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem mstore_raw_old_coverage:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  ptr_covers G tn p s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
    p ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >> drule_all mstore_raw_ghost_frame >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def, allocas_from_def]
QED

(* A raw variable taint map need not be byte-bounded; loaded words are.
   Keep that necessary bound explicit in the outside-word corollary. *)
Theorem mstore_raw_outside_taint:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  (!k. k IN op_taint tn value ==> k < 32) /\
  (i < w2n a \/ w2n a + 32 <= i) ==>
  (i IN (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn).t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> drule_all mstore_raw_ghost_frame >> strip_tac >>
  simp[] >> simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF] >>
  eq_tac >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem external_load_ghost_frame:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a ==>
  step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s) =
    DRESTRICT G (COMPL {tmp}) /\
  (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn).t_var =
    tn.t_var |+ (tmp, if opc = SLOAD then key_taint tn.t_stor a
                     else if opc = TLOAD then key_taint tn.t_trans a else {}) /\
  (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn).t_imm = tn.t_imm
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       written_taint_def, range_bytes_def, new_site_bytes_def, update_var_def,
       finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem external_load_state_frame:
  tmp <> old ==>
  lookup_var tmp ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) = SOME w /\
  lookup_var old ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var old s /\
  ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_memory = s.vs_memory /\
  ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_allocas = s.vs_allocas /\
  ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_fmp = s.vs_fmp
Proof
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem external_load_old_coverage:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a /\ tmp <> p /\ ptr_covers G tn p s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    p ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >>
  mp_tac (Q.INST [`opc` |-> `opc`, `src` |-> `src`, `s` |-> `s`,
                  `a` |-> `a`] external_load_ghost_frame) >>
  simp[] >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
      allocas_from_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem external_load_output_ghost:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a ==>
  FLOOKUP (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s)) tmp = NONE /\
  op_taint (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn) (Var tmp) =
    (if opc = SLOAD then key_taint tn.t_stor a
     else if opc = TLOAD then key_taint tn.t_trans a else {})
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  gvs[]
QED

Theorem external_load_endpoint:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK u ==>
  ?a w. eval_operand src s = SOME a /\ u = update_var tmp w s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
