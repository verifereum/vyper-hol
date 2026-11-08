(* Counted administrative instruction boundaries for For loops. *)
Theory forPtrAdmin
Ancestors forPtrBoundary allocationPtr ghostPcTransportPtr fragExecPtr
  venomInst venomExecProofs ptrDiscipline finite_map venomState ptrSafeRun
  codegenRel contextCodegenRel venomExecSemantics typedCopyPtr

Theorem straight_line_zero_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK u ==>
  gas_path_ptr D lo ctx fn PG G tn s 0
    (step_prov PG G i u) (step_taint i s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all straight_line_single_path_ptr >> simp[]
QED

Theorem alloca_zero_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit szw] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit szw] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit szw] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit szw] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule straight_line_zero_path_ptr >>
  simp[GSYM mk_inst_def, is_terminator_def] >>
  irule ptr_inst_ok_alloca >> simp[]
QED

Theorem alloca_zero_path_ptr_covered:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    out (u with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >> conj_tac
  >- (irule alloca_zero_path_ptr >> simp[]) >>
  simp[] >> drule_all alloca_step_ptr_covers >> simp[]
QED

Theorem alloca_old_variable_ghost_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  p <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) p =
    FLOOKUP G p /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (Var p) = op_taint tn (Var p)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem ptr_inst_ok_eq:
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id EQ [left;right] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem eq_zero_path_ptr:
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [left;right] [out]) /\
  step_inst_base (mk_inst id EQ [left;right] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id EQ [left;right] [out]) u)
    (step_taint (mk_inst id EQ [left;right] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule straight_line_zero_path_ptr >>
  simp[GSYM mk_inst_def, is_terminator_def] >>
  irule ptr_inst_ok_eq >> simp[]
QED

Theorem ptr_inst_ok_assign_literal:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSIGN [Lit w] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, op_taint_def, step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, update_var_def]
QED

Theorem assign_literal_zero_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ASSIGN [Lit w] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [Lit w] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [Lit w] [out]) s (update_var out w s) tn)
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule straight_line_zero_path_ptr >>
  simp[GSYM mk_inst_def, is_terminator_def] >> reverse conj_tac
  >- (irule ptr_inst_ok_assign_literal >> simp[]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]
QED

Theorem assign_literal_scalar_ghost:
  step_prov PG G (mk_inst id ASSIGN [Lit w] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ASSIGN [Lit w] [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, mk_inst_def, taint_component_equality,
       first_prov_def, eval_operand_def]
QED

Theorem copy_len_binop_zero_path_ptr:
  (opc = ADD \/ opc = AND) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [left;right] [out]) /\
  step_inst_base (mk_inst id opc [left;right] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [out]) u)
    (step_taint (mk_inst id opc [left;right] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id opc [left;right] [out]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  irule straight_line_zero_path_ptr >>
  simp[GSYM mk_inst_def] >>
  Cases_on `opc = ADD` >> gvs[is_terminator_def]
QED
