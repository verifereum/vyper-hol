(* Only the numeric instruction family needed by the fixed historical trace. *)
Theory bodyPtrSubscriptNumeric
Ancestors
  bodyPtrAttributeAdd bodyPtrSubscriptWordProvenance stmtAppendStorageRunPtr
  decoderGhostFramePtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs ptrSafeRun
  ptrDiscipline venomInst venomExecSemantics venomState finite_map
  emitHelperProps emitHelper compileEnv list codegenRel contextCodegenRel exprSendPtr
  exprLoweringProps fragExec rich_list

Theorem numeric_inst_check:
  MEM opc [ISZERO; SUB; MUL; LT; OR] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[GSYM IMP_DISJ_THM] >> rpt strip_tac >>
  gvs[op_prov_def, FLOOKUP_DEF] >>
  qpat_assum `!op. _ ==> _ = NONE` (qspec_then `Var u` mp_tac) >>
  qpat_x_assum `!op. _ ==> _ = NONE` (qspec_then `Var w` mp_tac) >> simp[]
QED

Theorem numeric_out_taint_none:
  MEM opc [ISZERO; SUB; MUL; LT; OR] /\
  (!op. MEM op ops ==> op_taint tn op = {}) ==>
  out_taint tn (mk_inst id opc ops [out]) s = {}
Proof
  strip_tac >> Cases_on `ops`
  >- simp[out_taint_def, mk_inst_def] >>
  Cases_on `t`
  >- (gvs[] >> simp[out_taint_def, mk_inst_def] >>
      Cases_on `eval_operand h s` >> simp[]) >>
  Cases_on `t'`
  >- (gvs[] >> simp[out_taint_def, mk_inst_def] >>
      Cases_on `eval_operand h s` >> simp[]) >>
  gvs[] >> simp[out_taint_def, mk_inst_def]
QED

Theorem numeric_ghost_frame:
  MEM opc [ISZERO; SUB; MUL; LT; OR] /\
  (!op. MEM op ops ==> op_prov G op = NONE) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc ops [out]) t = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s t tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `first_prov G ops = NONE` by (irule first_prov_none >> simp[]) >>
  `out_taint tn (mk_inst id opc ops [out]) s = {}` by
    (irule numeric_out_taint_none >> simp[]) >>
  conj_tac
  >- (gvs[] >> simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def]) >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def, mk_inst_def,
       taint_component_equality, DRESTRICT_UNIV] >>
  namedCases_on `ops` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b tail"] >> simp[] >>
  namedCases_on `tail` ["", "c more"] >> simp[] >>
  Cases_on `more` >> simp[]
QED

Theorem emit_numeric_counted:
  MEM opc [ISZERO; SUB; MUL; LT; OR] /\
  emit_op opc ops sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id opc ops [dst]) s =
         OK (update_var dst w s)) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  `!dst. ptr_inst_ok D 0 0 ctx func G tn (mk_inst sa.cs_next_id opc ops [dst]) s`
    by (gen_tac >> irule numeric_inst_check >> simp[update_var_def] >>
        goal_assum (drule_at Any) >> simp[]) >>
  `opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc` by
    (gvs[] >> simp[is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  drule_all attribute_emit_op_path_ptr >>
  `!op. MEM op ops ==> op_prov G op = NONE` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `step_prov PG G (mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) =
      DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var)} ) /\
   step_taint (mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn =
      (tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}))`
    by (irule numeric_ghost_frame >> simp[update_var_def]) >>
  simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  qpat_x_assum `!PG'. gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `PG` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

Theorem numeric_iszero_step:
  eval_operand arg s = SOME a ==>
  step_inst_base (mk_inst id ISZERO [arg] [out]) s =
    OK (update_var out (bool_to_word (a = 0w)) s)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def]
QED

Theorem numeric_binary_step:
  (opc = SUB /\ f = word_sub \/ opc = MUL /\ f = word_mul \/
   opc = OR /\ f = word_or \/
   opc = LT /\ f = (\a b. bool_to_word (w2n a < w2n b))) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out (f a b) s)
Proof
  rpt strip_tac >> gvs[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                   instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

(* An explicit frame for the exact endpoint exported by emit_numeric_counted;
   no additional execution witness is selected. *)
Theorem numeric_endpoint_frame:
  p <> out ==>
  lookup_var p (update_var out w s with vs_inst_idx := n) = lookup_var p s /\
  FLOOKUP (DRESTRICT G (COMPL {out})) p = FLOOKUP G p /\
  op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var p) = op_taint tn (Var p) /\
  FLOOKUP (DRESTRICT G (COMPL {out})) out = NONE /\
  op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var out) = {}
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def]
QED

Theorem emit_numeric_assert_counted:
  emit_void ASSERT [arg] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME w /\ w <> 0w /\ op_taint tn arg = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ASSERT [arg] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all assert_ok_path_ptr >> simp[arithmeticTheory.ADD1]
QED

Theorem numeric_endpoint_observations:
  lookup_var out (update_var out w s with vs_inst_idx := n) = SOME w /\
  (update_var out w s with vs_inst_idx := n).vs_memory = s.vs_memory /\
  (update_var out w s with vs_inst_idx := n).vs_allocas = s.vs_allocas /\
  (update_var out w s with vs_inst_idx := n).vs_fmp = s.vs_fmp /\
  (update_var out w s with vs_inst_idx := n).vs_requests = s.vs_requests /\
  (update_var out w s with vs_inst_idx := n).vs_current_bb = s.vs_current_bb /\
  (update_var out w s with vs_inst_idx := n).vs_halted = s.vs_halted /\
  op_prov (DRESTRICT G (COMPL {out})) (Var out) = NONE /\
  op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var out) = {}
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, op_prov_def]
QED
