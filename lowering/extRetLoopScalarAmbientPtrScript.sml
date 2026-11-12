Theory extRetLoopScalarAmbientPtr
Ancestors
  extRetBytesCopyCountedPtr fragGasPathPtr fragExec emitHelper compileEnv
  ptrDiscipline ptrSafeRun bodyPtrDefs venomExecSemantics venomInst venomState
  words finite_map pred_set arithmetic codegenRel contextCodegenRel

(* The older bulk producer's check and ghost equations are local.  This
   boundary retains the immediate-taint frame of the concrete instruction. *)
Theorem loop_bulk_binop_check[local]:
  (opc = MUL \/ (opc = GT /\ ?k. right = Lit k)) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id opc [left;right] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem loop_bulk_binop_ghost[local]:
  (opc = MUL \/ opc = GT) /\ op_taint tn left = {} /\ op_taint tn right = {} ==>
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn) (Var out) = {} /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_imm = tn.t_imm /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn) (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  gvs[] >> Cases_on `eval_operand left s` >>
  qpat_x_assum `op_taint tn left = _` (assume_tac o SRULE [op_taint_def]) >>
  qpat_x_assum `op_taint tn right = _` (assume_tac o SRULE [op_taint_def]) >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       imm_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_bulk_binop_ambient_counted_ptr:
  (opc = MUL /\ f = word_mul \/
   opc = GT /\ (?k. right = Lit k) /\
   f = (\a b. bool_to_word (w2n a > w2n b))) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    gvs[is_terminator_def] >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >>
     simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_pure2_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] loop_bulk_binop_check) >> metis_tac[]) >>
  gvs[] >> simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `tnf`, Abbr `Gf`,
       loop_bulk_binop_ghost |> SPEC_ALL |> Q.INST [`opc` |-> `MUL`] |> SRULE [],
       loop_bulk_binop_ghost |> SPEC_ALL |> Q.INST [`opc` |-> `GT`] |> SRULE []] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[loop_bulk_binop_ghost, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED
