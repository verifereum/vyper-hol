(* Compiler-shaped bounds interface, shared by literal and code-read lengths. *)
Theory bodyPtrSubscriptSeamArrayCodeBounds
Ancestors
  bodyPtrSubscriptSignedBounds bodyPtrSubscriptRejectedSelector bodyPtrSubscriptBoundsRun
  exprSimArrayIndex loweringShapeRules emitHelper compileEnv ptrDiscipline
  fragGasPathPtr venomState words integer_word

Theorem array_bounds_check_counted_ok:
  array_bounds_check idx len sgn sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  idx_in_range sgn a b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel ctx func cenv cx es sf)
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def, comp_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emit_op_facts >> gvs[] >>
  gvs[idx_in_range_def, WORD_LTi, word_0_w2i]
  >- (`0 <= w2i a` by intLib.ARITH_TAC >>
      drule_all signed_bounds_counted_read_only >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]) >>
  drule_all unsigned_bounds_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Theorem array_bounds_check_counted_oob:
  array_bounds_check idx len sgn sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  ~idx_in_range sgn a b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t)))
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def, comp_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emit_op_facts >> gvs[] >>
  gnvs[idx_in_range_def, WORD_LTi, word_0_w2i]
  >- (`~(0 <= w2i a /\ w2n a < w2n b)` by intLib.ARITH_TAC >>
      drule_all signed_flag_assert_rejects_counted >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]) >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   op_prov G (Lit 0w) = NONE /\ (!q. Lit 0w = Var q ==> not_fresh_at sa q) /\
   (!l. Lit 0w <> Label l) /\ ~(0w = 0w /\ w2n a < w2n b)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule (bounds_flag_assert_rejects_counted |>
    Q.INST [`negflag` |-> `Lit 0w`, `n` |-> `0w`]) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED
