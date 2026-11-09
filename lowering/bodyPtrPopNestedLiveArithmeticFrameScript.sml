Theory bodyPtrPopNestedLiveArithmeticFrame
Ancestors
  bodyPtrPopNestedLiveArithmetic bodyPtrPopScalarTransfer bodyPtrAttributeAdd
  bodyPtrDefs emitHelperProps emitHelper compileEnv ptrDiscipline
  venomState venomInst finite_map pred_set words

Theorem pop_scalar_mul_framed_path:
  emit_op MUL [left;right] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    eval_operand dst t = SOME (a*b) /\
    op_prov H dst = NONE /\ op_taint tf dst = {} /\
    not_fresh_at sb out /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = _` SUBST_ALL_TAC >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   not_fresh_at sb (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MUL [left;right] [out]) s =
      OK (update_var out (a*b) s) /\
    ptr_inst_ok D 0 0 ctx fn G tn
      (mk_inst sa.cs_next_id MUL [left;right] [out]) s` by
    (gen_tac >> irule pop_scalar_binary_step >> simp[]) >>
  `!out. step_prov PG G (mk_inst sa.cs_next_id MUL [left;right] [out])
      (update_var out (a*b) s) = DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst sa.cs_next_id MUL [left;right] [out]) s
      (update_var out (a*b) s) tn = tn with t_var := tn.t_var |+ (out,{})` by
    (gen_tac >> irule pop_scalar_binary_ghost >> simp[]) >>
  fs[FORALL_AND_THM] >>
  `MUL <> INVOKE /\ MUL <> GAS /\ ~is_terminator MUL` by
    simp[is_terminator_def] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var)}))
    (tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}))
    (OK (update_var (STRING #"%" (toString sa.cs_next_var)) (a*b) s
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all attribute_emit_op_path_ptr >>
     disch_then (qspec_then `PG` mp_tac) >>
     simp[is_terminator_def] >>
     `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
       gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
           fresh_id_def, emit_def, comp_return_def] >> simp[arithmeticTheory.ADD1]) >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, op_prov_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `v <> STRING #"%" (toString sa.cs_next_var)` by gvs[not_fresh_at_def] >> simp[]
QED
