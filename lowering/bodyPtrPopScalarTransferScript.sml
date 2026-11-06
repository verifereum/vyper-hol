Theory bodyPtrPopScalarTransfer
Ancestors
  bodyPtrPopRootTransfer fragGasSeqPtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel finite_map pred_set

Theorem pop_scalar_binary_step:
  (opc = SUB /\ z = x-y \/ opc = ADD /\ z = x+y \/ opc = MUL /\ z = x*y) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx ==>
  step_inst_base (mk_inst id opc [a;b] [out]) s = OK (update_var out z s) /\
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a;b] [out]) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [a;b] [out]) s = OK (update_var out z s)` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
                   eval_operands_def]) >>
  simp[] >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >> metis_tac[]
QED

Theorem pop_scalar_binary_ghost:
  (opc = SUB \/ opc = ADD \/ opc = MUL) /\
  op_prov G a = NONE /\ op_prov G b = NONE ==>
  step_prov PG G (mk_inst id opc [a;b] [out]) (update_var out z s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc [a;b] [out]) s (update_var out z s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var out z s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem pop_scalar_binary_transfer:
  (opc = SUB /\ z = x-y \/ opc = ADD /\ z = x+y \/ opc = MUL /\ z = x*y) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id opc [a;b] [out]] s G' tn' /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. v <> out ==> FLOOKUP G' v = FLOOKUP G v /\
          op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [a;b] [out]) s = OK (update_var out z s) /\
   ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [a;b] [out]) s` by
    (irule pop_scalar_binary_step >> metis_tac[]) >>
  `step_prov PG G (mk_inst id opc [a;b] [out]) (update_var out z s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc [a;b] [out]) s (update_var out z s) tn =
      tn with t_var := tn.t_var |+ (out,{})` by
    (irule pop_scalar_binary_ghost >> metis_tac[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {out})`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  gvs[] >> simp[inst_seq_ptr_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE]
QED
