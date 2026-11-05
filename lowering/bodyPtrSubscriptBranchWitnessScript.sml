(* Counted branch adapters for the constructive named-scalar pilot. *)
Theory bodyPtrSubscriptBranchWitness
Ancestors
  bodyPtrSubscriptNamedScalar bodyPtrSubscriptWordProvenance
  stmtAssertPtr bodyPtrCtrlCases fragGasSeqPtr fragGasPathPtr
  exprSimIfExp exprSimOperators emitHelper exprLoweringProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  venomExecProofs gasCount finite_map pred_set codegenRel contextCodegenRel
  compileEnv fragExec

Theorem scalar_assign_checked_step:
  ~ctx_has_dalloca ctx /\
  eval_operand src s = SOME w /\ op_taint tn src = {} /\ op_prov G src = NONE ==>
  ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst iid ASSIGN [src] [out]) s /\
  step_inst_base (mk_inst iid ASSIGN [src] [out]) s = OK (update_var out w s) /\
  op_prov (step_prov PG G (mk_inst iid ASSIGN [src] [out])
    (update_var out w s)) (Var out) = NONE /\
  op_taint (step_taint (mk_inst iid ASSIGN [src] [out]) s
    (update_var out w s) tn) (Var out) = {}
Proof
  strip_tac >> rpt conj_tac
  >- simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          allocas_from_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, step_inst_non_invoke,
          step_inst_base_def, update_var_def]
  >- simp[step_inst_base_def, mk_inst_def]
  >- (simp[op_prov_def] >>
      irule scalar_forward_output_provenance_none >> simp[mk_inst_def]) >>
  simp[step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, out_taint_def] >> gvs[op_taint_def]
QED

Theorem scalar_assign_counted_path:
  emit_inst ASSIGN [src] [out] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand src s = SOME w /\ op_taint tn src = {} /\ op_prov G src = NONE ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id ASSIGN [src] [out]) s (update_var out w s) tn)
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSIGN [src] [out]]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ASSIGN [src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst sa.cs_next_id ASSIGN [src] [out]) s /\
   step_inst_base (mk_inst sa.cs_next_id ASSIGN [src] [out]) s = OK (update_var out w s)` by
    (drule_all scalar_assign_checked_step >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id ASSIGN [src] [out]) s (update_var out w s) tn)
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> simp[gas_path_ptr_rules, update_var_def]
QED

Theorem scalar_assign_old_ghost:
  (!p. not_fresh_at sa p ==> p <> out) ==>
  (step_taint (mk_inst iid ASSIGN [src] [out]) s (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst iid ASSIGN [src] [out]) s (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst iid ASSIGN [src] [out]) s (update_var out w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst iid ASSIGN [src] [out]) s (update_var out w s) tn).t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==>
    lookup_var p (update_var out w s with vs_inst_idx := k) = lookup_var p s /\
    FLOOKUP (step_prov PG G (mk_inst iid ASSIGN [src] [out]) (update_var out w s)) p =
      FLOOKUP G p /\
    op_taint (step_taint (mk_inst iid ASSIGN [src] [out]) s (update_var out w s) tn)
      (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  simp[step_taint_def, mk_inst_def, mem_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, update_var_def, source_memory_write_ranges_def,
       range_bytes_def] >>
  conj_tac >- (simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, step_prov_def,
       set_prov_def, set_var_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_DRESTRICT] >>
  CASE_TAC >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
