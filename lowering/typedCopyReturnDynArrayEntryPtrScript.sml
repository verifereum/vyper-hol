(* Shared counted entry for dynamic typed-array copying. *)
Theory typedCopyReturnDynArrayEntryPtr
Ancestors bodyPtrSubscriptLengthRead bodyPtrBopInHeaderControl
  exprSimBopRestWordTail typedCopyReturnControlPtr bodyPtrPopMemoryStore
  fragExec fragGasPathPtr fragGasSeqPtr emitHelperProps emitHelper compileEnv
  venomState venomInst venomExecSemantics ptrDiscipline finite_map words
  typedCopyLayoutPtr representationCleanPtr valueEncodingProps ptrCoverage typedCopyPtr
  bodyPtrDefs

Theorem typed_copy_capacity_counted[local]:
  emit_op GT [len; Lit (n2w cap)] sa = (flagop,sb) /\
  emit_op ISZERO [flagop] sb = (okop,sc) /\
  emit_inst ASSERT [okop] [] sc = ((),sd) /\
  fn_has_code sa sd fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_taint tn len = {} /\ op_prov G len = NONE ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all rest_word_capacity_check_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id GT [len; Lit (n2w cap)] [invvar]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id+1) ISZERO [Var invvar] [validvar]) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (sa.cs_next_id+2) ASSERT [Var validvar] [])` by
    (conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     conj_tac >- (first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all membership_capacity_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  gvs[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem typed_copy_dynarray_checked_length[local]:
  emit_op MLOAD [Var src] sa = (Var len,sb) /\
  emit_op GT [Var len; Lit (n2w cap)] sb = (flag,sc) /\
  emit_op ISZERO [flag] sc = (valid,sd) /\
  emit_inst ASSERT [valid] [] sd = ((),se) /\
  fn_has_code sa sb fn /\ fn_has_code sb se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME a /\
  LENGTH vs <= cap /\ cap < dimword(:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic oldcap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\ ~t.vs_halted /\
    lookup_var len t = SOME (n2w (LENGTH vs)) /\
    op_taint tm (Var len) = {} /\ op_prov H (Var len) = NONE /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule dynarray_in_memory_robust_length >> strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all exprSimPtrPropsTheory.emit_mload_ptr_path >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qpat_x_assum `out = _` kall_tac >> gvs[] >>
  qabbrev_tac `sf = update_var len (n2w (LENGTH vs)) s with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  `not_fresh_at sb len /\
   (!p. not_fresh_at sa p ==> not_fresh_at sb p)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand (Var len) sf = SOME (n2w (LENGTH vs))` by
    simp[Abbr `sf`, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (simp[Abbr `sf`, update_var_def] >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def]) >>
  drule_all typed_copy_capacity_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  conj_tac >- (fs[Abbr `sf`] >> qpat_x_assum `s.vs_inst_idx = _` SUBST_ALL_TAC >>
    drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >>
  `lookup_var len t = lookup_var len sf /\
   FLOOKUP H len = FLOOKUP G' len /\
   op_taint tm (Var len) = op_taint tn' (Var len)` by metis_tac[] >>
  fs[op_prov_def, Abbr `sf`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (qpat_x_assum `t = _` SUBST1_TAC >> simp[]) >>
  metis_tac[]
QED
