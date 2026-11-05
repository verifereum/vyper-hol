(* Counted read-only storage and transient-storage word producers. *)
Theory bodyPtrSubscriptStorageLoad
Ancestors
  bodyPtrSubscriptWordStorage bodyPtrSubscriptLengthRead fragGasSeqPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomInstProofs venomInst
  venomState emitHelper compileEnv finite_map fragExec codegenRel contextCodegenRel
  contextProps fragGasPathPtr

Theorem ptr_inst_ok_storage_load:
  ~ctx_has_dalloca ctx /\ op_taint tn key = {} ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
Proof
  strip_tac >> Cases_on `tr` >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem storage_load_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) /\
  ~ctx_has_dalloca ctx /\ op_taint tn key = {} /\
  eval_operand key s = SOME (w:bytes32) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id (if tr then TLOAD else SLOAD) [key] [out])
      (update_var out (if tr then tload w s else sload w s) s))
    (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
      (update_var out (if tr then tload w s else sload w s) s) tn)
    (OK (update_var out (if tr then tload w s else sload w s) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s` by
    (irule ptr_inst_ok_storage_load >> simp[]) >>
  `step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s =
    OK (update_var out (if tr then tload w s else sload w s) s)` by
    (Cases_on `tr` >> simp[step_inst_base_def, mk_inst_def,
                           exec_read1_def]) >>
  `~is_terminator (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]).inst_opcode /\
   (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]).inst_opcode <> INVOKE` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def] >> strip_tac >>
  `~(update_var out (if tr then tload w s else sload w s) s with
     vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  Cases_on `tr` >> gvs[] >>
  first_x_assum (qspec_then `PG` assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules, update_var_def]
QED

Theorem storage_load_ghost_clean:
  eval_operand key s = SOME (w:bytes32) /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  op_taint (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
    (update_var out (if tr then tload w s else sload w s) s) tn) (Var out) = {} /\
  (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
    (update_var out (if tr then tload w s else sload w s) s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
    (update_var out (if tr then tload w s else sload w s) s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
    (update_var out (if tr then tload w s else sload w s) s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [key] [out]) s
    (update_var out (if tr then tload w s else sload w s) s) tn).t_imm = tn.t_imm
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, update_var_def, store_taint_def, adopt_reset_def,
      imm_taint_def, FLOOKUP_UPDATE, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem emit_storage_load_counted_scalar:
  emit_op (if tr then TLOAD else SLOAD) [key] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand key s = SOME (w:bytes32) /\ op_taint tn key = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf = (update_var out (if tr then tload w s else sload w s) s with
          vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G
      (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out])
      (update_var out (if tr then tload w s else sload w s) s) /\
    tnf = step_taint
      (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out]) s
      (update_var out (if tr then tload w s else sload w s) s) tn /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var out sf = SOME (if tr then tload w s else sload w s) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `t = update_var out (if tr then tload w s else sload w s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [key] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (unabbrev_all_tac >>
    irule storage_load_counted_edge >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `t`] >>
  conj_tac >- simp[Abbr `Gf`, Abbr `t`] >>
  conj_tac >- simp[Abbr `tnf`, Abbr `t`] >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule storage_load_ghost_clean >> simp[]) >>
  `op_prov Gf (Var out) = NONE` by
    (Cases_on `tr` >> simp[Abbr `Gf`, step_prov_def, set_prov_def,
                           out_prov_def, mk_inst_def, op_prov_def,
                           FLOOKUP_DRESTRICT]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  Cases_on `tr` >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
