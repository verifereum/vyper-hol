(* Code-address selection after a checked bound. *)
Theory bodyPtrSubscriptSeamArrayCodeSuffix
Ancestors
  bodyPtrSubscriptSeamArrayCodeAddress bodyPtrSubscriptSeamArrayCodeBounds
  bodyPtrSubscriptSeamArrayCodeLoad bodyPtrSubscriptReadOnly
  exprSimArrayIndex loweringShapeRules emitHelper compileEnv ptrDiscipline
  fragGasPathPtr venomState words emitHelperProps fragExec freshWrites
  exprLoweringProps exprSimUnopProps context

Theorem code_array_elem_ptr_counted:
  array_elem_ptr base_op idx dyn 32 elem_size sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand op sf = SOME (a + n2w ((if dyn then 32 else 0) + i * elem_size)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
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
  Cases_on `dyn` >> simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emit_op_facts >> gvs[] >>
  `(!q. base_op = Var q ==> not_fresh_at sa q) /\
   (!q. idx = Var q ==> not_fresh_at sa q) /\
   (!l. base_op <> Label l) /\ (!l. idx <> Label l)` by metis_tac[]
  >- (drule_all code_dynamic_address_counted >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl [`Gf`, `tnf`, `sf`] >> simp[eval_operand_def]) >>
  drule_all code_mul_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `sf`] >> simp[eval_operand_def]
QED

Theorem code_array_check_parts_fresh:
  straight_fresh (array_bounds_check idx len sgn) /\
  straight_fresh (array_elem_ptr base_op idx dyn ws elem_size)
Proof
  conj_tac >> rw[array_bounds_check_def, array_bounds_valid_def, array_elem_ptr_def] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
    gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    MATCH_ACCEPT_TAC straight_fresh_return, IF_CASES_TAC])
QED

Theorem code_array_check_ptr_counted_ok:
  comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn 32 elem_size) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l /\ len <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  eval_operand len s = SOME bound /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  idx_in_range sgn (n2w i) bound ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand op sf = SOME (a + n2w ((if dyn then 32 else 0) + i * elem_size)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
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
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >>
  gvs[oneTheory.one] >> strip_tac >>
  `straight_fresh (array_bounds_check idx len sgn) /\
   straight_fresh (array_elem_ptr base_op idx dyn 32 elem_size)` by
    simp[code_array_check_parts_fresh] >>
  `cs_extends sa cs' /\ sa.cs_next_var <= cs'.cs_next_var /\ cs_extends cs' sb` by
    metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code sa cs' func /\ fn_has_code cs' sb func` by metis_tac[fn_has_code_split] >>
  `(!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
   (!l. idx <> Label l /\ len <> Label l)` by metis_tac[] >>
  drule_all array_bounds_check_counted_ok >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\ op_prov G1 base_op = NONE /\
   eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    (conj_tac >- metis_tac[reserved_operand_read_only] >>
     metis_tac[reserved_operand_read_only]) >>
  `(!q. base_op = Var q \/ idx = Var q ==> not_fresh_at cs' q) /\
   (!l. base_op <> Label l /\ idx <> Label l)` by metis_tac[not_fresh_at_mono] >>
  drule_all code_array_elem_ptr_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  rpt strip_tac >> metis_tac[local_ptrs_reserved_next_var]
QED

Theorem code_array_check_ptr_counted_oob:
  comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn ws elem_size) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  eval_operand len s = SOME bound /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  ~idx_in_range sgn w bound ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t)))
Proof
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >>
  gvs[oneTheory.one] >> strip_tac >>
  `straight_fresh (array_bounds_check idx len sgn) /\
   straight_fresh (array_elem_ptr base_op idx dyn ws elem_size)` by
    simp[code_array_check_parts_fresh] >>
  `cs_extends sa cs' /\ cs_extends cs' sb` by metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code sa cs' func` by metis_tac[fn_has_code_split] >>
  drule_all array_bounds_check_counted_oob >> simp[]
QED

Theorem runtime_code_selector_counted_ok:
  compile_array_subscript base_op idx T cnt 32 elem_size sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  idx_in_range sgn (n2w i) (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand op sf = SOME (a + n2w (32 + i * elem_size)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
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
  simp[compile_array_subscript_split, comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >>
  `ci_mono sa cs'` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx len_op sgn)
     (array_elem_ptr base_op idx T 32 elem_size))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends cs' sb` by metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code sa cs' func /\ fn_has_code cs' sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all compile_imm_load_word_runtime_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`out`, `G1`, `tn1`, `s1`] strip_assume_tac) >> gvs[] >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\ op_prov G1 base_op = NONE /\
   eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    metis_tac[reserved_operand_read_only] >>
  `(!q. base_op = Var q \/ idx = Var q \/ Var out = Var q ==> not_fresh_at cs' q) /\
   (!l. base_op <> Label l /\ idx <> Label l /\ Var out <> Label l)` by
    (`not_fresh_at cs' out` by
       (qpat_x_assum `compile_imm_load_word _ _ _ _ = _`
          (mp_tac o REWRITE_RULE [compile_imm_load_word_runtime]) >>
        disch_then (strip_assume_tac o MATCH_MP emit_op_facts) >> gvs[]) >>
     simp[] >> metis_tac[ci_mono_def, not_fresh_at_mono]) >>
  `eval_operand (Var out) s1 = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[eval_operand_def] >>
  drule_all code_array_check_ptr_counted_ok >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[ci_mono_def, not_fresh_at_mono]) >>
  rpt strip_tac >> metis_tac[ci_mono_def, local_ptrs_reserved_next_var]
QED

Theorem runtime_code_selector_counted_oob:
  compile_array_subscript base_op idx T cnt 32 elem_size sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  ~idx_in_range sgn w (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t)))
Proof
  simp[compile_array_subscript_split, comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >>
  `ci_mono sa cs'` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx len_op sgn)
     (array_elem_ptr base_op idx T 32 elem_size))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends cs' sb` by metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code sa cs' func /\ fn_has_code cs' sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all compile_imm_load_word_runtime_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`out`, `G1`, `tn1`, `s1`] strip_assume_tac) >> gvs[] >>
  `eval_operand idx s1 = SOME w /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    metis_tac[reserved_operand_read_only] >>
  `(!q. idx = Var q \/ Var out = Var q ==> not_fresh_at cs' q) /\
   (!l. idx <> Label l /\ Var out <> Label l)` by
    (`not_fresh_at cs' out` by
       (qpat_x_assum `compile_imm_load_word _ _ _ _ = _`
          (mp_tac o REWRITE_RULE [compile_imm_load_word_runtime]) >>
        disch_then (strip_assume_tac o MATCH_MP emit_op_facts) >> gvs[]) >>
     simp[] >> metis_tac[ci_mono_def, not_fresh_at_mono]) >>
  `eval_operand (Var out) s1 = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[eval_operand_def] >>
  drule_all code_array_check_ptr_counted_oob >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t`] strip_assume_tac) >>
  qexistsl [`G2`, `tn2`, `t`] >> drule_all gas_path_ptr_then >> simp[]
QED

Theorem code_selector_counted_ok:
  compile_array_subscript base_op idx dyn cnt 32 elem_size sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  idx_in_range sgn (n2w i) (if dyn then word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w)) else n2w cnt) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand op sf = SOME (a + n2w ((if dyn then 32 else 0) + i * elem_size)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
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
  Cases_on `dyn` >> simp[]
  >- (strip_tac >> drule_all runtime_code_selector_counted_ok >> simp[]) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def] >> strip_tac >>
  `(!q. base_op = Var q \/ idx = Var q \/ Lit (n2w cnt) = Var q ==> not_fresh_at sa q) /\
   (!l. base_op <> Label l /\ idx <> Label l /\ Lit (n2w cnt) <> Label l)` by (simp[] >> metis_tac[]) >>
  `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt) /\
   op_taint tn (Lit (n2w cnt)) = {} /\ op_prov G (Lit (n2w cnt)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all code_array_check_ptr_counted_ok >> simp[]
QED

Theorem code_selector_counted_oob:
  compile_array_subscript base_op idx dyn cnt 32 elem_size sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q \/ idx = Var q ==> not_fresh_at sa q) /\
  (!l. base_op <> Label l /\ idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME w /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  ~idx_in_range sgn w (if dyn then word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w)) else n2w cnt) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t)))
Proof
  Cases_on `dyn` >> simp[]
  >- (strip_tac >> drule_all runtime_code_selector_counted_oob >> simp[]) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def] >> strip_tac >>
  `(!q. idx = Var q \/ Lit (n2w cnt) = Var q ==> not_fresh_at sa q) /\
   (!l. idx <> Label l /\ Lit (n2w cnt) <> Label l)` by (simp[] >> metis_tac[]) >>
  `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt) /\
   op_taint tn (Lit (n2w cnt)) = {} /\ op_prov G (Lit (n2w cnt)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all code_array_check_ptr_counted_oob >> simp[]
QED
