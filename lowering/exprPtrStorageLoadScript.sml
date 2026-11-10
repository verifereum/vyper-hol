(* Shared storage/transient word-load boundaries. *)
Theory exprPtrStorageLoad
Ancestors
  bodyPtrDefs accountsRelProps ptrDiscipline exprSimUnwrap
  stmtAppendStorageRunPtr exprSimPtrProps venomExecSemantics venomInstProofs
  venomInst venomState compileEnv loweringStateRelDefs emitHelper emitHelperProps codegenRel fragExec

Theorem ptr_vv_base_key_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  eval_operand p.ptr_operand s = SOME a /\
  evaluate_type (get_tenv cx) t = SOME ty /\ 0 < type_slot_size ty ==>
  (p.ptr_location = LocStorage ==> key_taint tn.t_stor a = {}) /\
  (p.ptr_location = LocTransient ==> key_taint tn.t_trans a = {})
Proof
  simp[ptr_vv_ok_def, key_taint_def, pred_setTheory.EXTENSION] >>
  rpt strip_tac >> simp[] >> spose_not_then strip_assume_tac >>
  first_x_assum (qspecl_then [`a`, `ty`, `a`, `x`] mp_tac) >>
  simp[] >> strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem storage_load_step_ptr:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [arg] [out]) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var out (if tr then tload a s else sload a s) s
             with vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id (if tr then TLOAD else SLOAD) [arg] [out]` >>
  qabbrev_tac `u = update_var out (if tr then tload a s else sload a s) s` >>
  `step_inst_base i s = OK u` by
    (Cases_on `tr` >>
     simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule append_scalar_inst_check >>
     simp[Abbr `u`, update_var_def] >> Cases_on `tr` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G i u)
      (step_taint i s u tn) (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule gas_path_ptr_one_step >>
     simp[Abbr `i`, Abbr `u`, mk_inst_def, update_var_def] >>
     Cases_on `tr` >> simp[is_terminator_def]) >>
  `step_taint i s u tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[Abbr `i`] >> irule scalar_storage_load_taint >>
     simp[Abbr `u`, update_var_def]) >>
  qexistsl [`step_prov PG G i u`, `step_taint i s u tn`] >>
  simp[Abbr `u`, ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  reverse conj_tac
  >- (rpt strip_tac >> simp[Abbr `i`, scalar_step_old_prov]) >>
  irule step_prov_out_none >> simp[Abbr `i`, mk_inst_def] >>
  irule out_prov_other_none >> Cases_on `tr` >> simp[mk_inst_def]
QED

Theorem emit_storage_load_ptr_path:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out G' tn' u.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    u = (update_var out (if tr then tload a s else sload a s) s
           with vs_inst_idx := SUC s.vs_inst_idx) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [arg]
           [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all storage_load_step_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`STRING #"%" (toString sa.cs_next_var)`, `G'`, `tn'`,
    `update_var (STRING #"%" (toString sa.cs_next_var))
      (if tr then tload a s else sload a s) s
        with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[update_var_def] >> rpt strip_tac >>
  gvs[not_fresh_at_def]
QED
