(* Rejection stops at ASSERT, before computing any element address. *)
Theory bodyPtrSubscriptRejectedSelector
Ancestors
  bodyPtrSubscriptBoundsOutcome bodyPtrSubscriptMarkedEndpoint
  bodyPtrSubscriptSignedSelector bodyPtrSubscriptDynamicSelector
  bodyPtrSubscriptLengthRead bodyPtrSubscriptReadOnly bodyPtrSubscriptBounds
  exprLoweringProps emitHelperProps freshWrites emitHelper compileEnv
  ptrDiscipline bodyPtrDefs venomState venomInst fragGasPathPtr fragExec
  venomExecSemantics words integer_word

Theorem bounds_flag_assert_rejects_counted:
  emit_op LT [idx;len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  eval_operand negflag s = SOME n /\ ~(n = 0w /\ w2n a < w2n b) /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\ op_taint tn negflag = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\ op_prov G negflag = NONE /\
  (!q. negflag = Var q ==> not_fresh_at sa q) /\ (!l. negflag <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa sq` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sq func /\ fn_has_code sq sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all bounds_flag_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t`] strip_assume_tac) >>
  `eval_operand (Var valid) t = SOME 0w` by simp[bool_to_word_def] >>
  drule_all emitted_selector_assert_rejects_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] mp_tac) >> strip_tac >>
  qexistsl_tac [`G1`, `tn1`, `t`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem signed_flag_assert_rejects_counted:
  emit_op SLT [idx;Lit 0w] sa = (Var negflag,sk) /\
  emit_op LT [idx;len] sk = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [Var negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  ~(0 <= w2i a /\ w2n a < w2n b) /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sk /\ ci_mono sk sm /\ ci_mono sm sn /\
   ci_mono sn sp /\ ci_mono sp sq` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa sq` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sq func /\ fn_has_code sq sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all signed_bounds_flag_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t`] strip_assume_tac) >>
  `eval_operand (Var valid) t = SOME 0w` by simp[bool_to_word_def] >>
  drule_all emitted_selector_assert_rejects_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] mp_tac) >> strip_tac >>
  qexistsl_tac [`G1`, `tn1`, `t`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem signed_dynamic_selector_rejects_counted:
  compile_array_subscript (Var p) idx T 0 32 elem_size T
    (\op. emit_op MLOAD [op]) sa = (op,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ 32 <= parent_sz /\ lookup_var p s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  ~(0 <= w2i w /\ w2n w < LENGTH vs) /\ LENGTH vs < dimword (:256) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule signed_dynamic_selector_emissions >> strip_tac >> gnvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 sn /\ ci_mono sn s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s5 s6` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s6 /\ cs_extends s6 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s6 func /\ fn_has_code s6 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all emit_dynarray_length_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t1`] strip_assume_tac) >>
  `eval_operand idx t1 = SOME w /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    (drule_all reserved_operand_read_only >> simp[]) >>
  `eval_operand (Var len) t1 = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  `~(0 <= w2i w /\ w2n w < w2n (n2w (LENGTH vs):bytes32))` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `not_fresh_at s1 len` by
    (qpat_assum `emit_op MLOAD _ _ = _`
      (mp_then Any mp_tac emitted_operand_reserved) >> simp[]) >>
  `(!q. idx = Var q \/ Var len = Var q ==> not_fresh_at s1 q) /\
   (!l. idx <> Label l /\ Var len <> Label l)` by
    (simp[] >> rpt strip_tac >> gvs[] >>
     metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono]) >>
  drule_all signed_flag_assert_rejects_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at s1 q` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED

Theorem unsigned_dynamic_selector_rejects_counted:
  compile_array_subscript (Var p) idx T 0 32 elem_size F
    (\op. emit_op MLOAD [op]) sa = (op,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ 32 <= parent_sz /\ lookup_var p s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  LENGTH vs <= w2n w /\ LENGTH vs < dimword (:256) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule dynamic_selector_emissions >> strip_tac >> gnvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s5 s6` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s6 /\ cs_extends s6 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s6 func /\ fn_has_code s6 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all emit_dynarray_length_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t1`] strip_assume_tac) >>
  `eval_operand idx t1 = SOME w /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    (drule_all reserved_operand_read_only >> simp[]) >>
  `eval_operand (Var len) t1 = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  `~(w2n w < w2n (n2w (LENGTH vs):bytes32))` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `eval_operand (Lit 0w) t1 = SOME 0w /\ op_taint tn1 (Lit 0w) = {} /\
   op_prov G1 (Lit 0w) = NONE /\
   (!q. Lit 0w = Var q ==> not_fresh_at s1 q) /\ (!l. Lit 0w <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (bounds_flag_assert_rejects_counted |> Q.INST [`n` |-> `0w`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at s1 q` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED

Theorem dynamic_selector_rejects_counted:
  compile_array_subscript (Var p) idx T 0 32 elem_size sgn
    (\op. emit_op MLOAD [op]) sa = (op,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ 32 <= parent_sz /\ lookup_var p s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  (if sgn then w2i w = i else 0 <= i /\ w2n w = Num i) /\
  (i < 0 \/ LENGTH vs <= Num i) /\ LENGTH vs < dimword (:256) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> reverse (Cases_on `sgn`)
  >- (gnvs[] >> `LENGTH vs <= w2n w` by intLib.ARITH_TAC >>
      drule_all unsigned_dynamic_selector_rejects_counted >> simp[]) >>
  gnvs[] >>
  `~(0 <= w2i w /\ w2n w < LENGTH vs)` by
    (strip_tac >>
     `w2n w = Num (w2i w)` by
       (Cases_on `word_msb w`
        >- (fs[w2i_def] >> `w2n w < dimword (:256)` by simp[w2n_lt] >>
            intLib.ARITH_TAC) >> simp[w2i_def]) >>
     intLib.ARITH_TAC) >>
  drule_all signed_dynamic_selector_rejects_counted >> simp[]
QED
