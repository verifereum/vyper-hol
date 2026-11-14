(* The terminal arithmetic and REVERT steps preserve pointer safety. *)
Theory stmtSimCustomErrorPtrTail
Ancestors
  stmtSimCustomErrorPtrBoundary stmtAbortPtr bodyPtrAttributeAdd
  exprSimPtrLiteralOps typedMemoryCopy bodyPtrDefs fragGasPathPtr emitHelperProps
  compileEnv emitHelper ptrDiscipline venomExecSemantics venomState venomInst
  loweringStateRelDefs words finite_map arithmetic

Theorem custom_error_revert_suffix_run_ptr:
  emit_op ADD [Var x; Lit 28w] st = (offset,sn) /\
  (if no_args then len = Lit 4w /\ sr = sn
   else emit_op ADD [Lit 4w;encoded_len] sn = (len,sr)) /\
  emit_inst REVERT [offset;len] [] sr = ((),en) /\
  fn_has_code st sn func /\ fn_has_code sn sr func /\ fn_has_code sr en func /\
  lookup_var x s = SOME (n2w d) /\ ptr_covers G tn x s (B+32) /\
  (~no_args ==> eval_operand encoded_len s = SOME (n2w k) /\
    op_taint tn encoded_len = {} /\
    (!v. encoded_len = Var v ==> not_fresh_at st v)) /\
  not_fresh_at st x /\ d+B+32 < dimword (:256) /\ k <= B /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  !D PG. ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort t)
Proof
  strip_tac >> rpt gen_tac >>
  `op_taint tn (Var x) = {}` by gvs[ptr_covers_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`,
    `left` |-> `Var x`, `right` |-> `Lit 28w`,
    `sa` |-> `st`, `sb` |-> `sn`, `dst` |-> `offset`,
    `a` |-> `n2w d`, `b` |-> `28w`]
    (SPEC_ALL attribute_emit_binop_path_ptr)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  rename1 `offset = Var out` >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u)` >>
  `?base cap. FLOOKUP G x = SOME (base,cap) /\ base <= d /\
    d+B+32 <= base+cap` by
    (gvs[ptr_covers_def, w2n_n2w] >>
     `d < dimword (:256)` by decide_tac >> gvs[]) >>
  rename1 `FLOOKUP G x = SOME (pb,capacity)` >>
  `d+28 < dimword (:256)` by decide_tac >>
  `ptr_covers G1 tn1 out u (B+4)` by
    (qpat_x_assum `u = _` SUBST_ALL_TAC >>
     qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
     simp[word_add_n2w] >>
     mp_tac (Q.INST [`src` |-> `x`, `w` |-> `n2w d`,
       `off` |-> `28`, `sz` |-> `B+4`, `b` |-> `pb`, `n` |-> `capacity`,
       `dst` |-> `out`, `id` |-> `st.cs_next_id`]
       (SPEC_ALL literal_add_ptr_covers)) >>
     simp[w2n_n2w, ptr_covers_def, lookup_var_def, update_var_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, update_var_def]) >>
  `~not_fresh_at st out /\ not_fresh_at sn out` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  Cases_on `no_args`
  >- (fs[] >>
      `ptr_covers G1 tn1 out u 4` by
        (gvs[ptr_covers_def] >> metis_tac[DECIDE ``a+B+4 <= n ==> a+4 <= n``]) >>
      `ptr_inst_ok D 0 0 ctx func G1 tn1
        (mk_inst sn.cs_next_id REVERT [Var out;Lit 4w] []) u` by
        (irule custom_error_revert_ptr_inst_ok >>
         simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
      `?t. step_inst_base (mk_inst sn.cs_next_id REVERT [Var out;Lit 4w] []) u =
        Abort Revert_abort t` by
        (gvs[ptr_covers_def] >>
         simp[step_inst_base_def, mk_inst_def, eval_operand_def,
           update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
      `gas_path_ptr D 0 ctx func PG G1 tn1 u 0 G1 tn1
        (Abort Revert_abort t)` by
        (irule emit_abort_zero_path_ptr >> conj_tac >- fs[] >>
         qexistsl_tac [`REVERT`, `[Var out;Lit 4w]`, `sn`, `en`] >> gvs[]) >>
      metis_tac[gas_path_ptr_then, ADD_0]) >>
  fs[] >>
  `encoded_len <> Var out` by metis_tac[] >>
  `eval_operand encoded_len u = SOME (n2w k)` by
    (Cases_on `encoded_len` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn1 encoded_len = {}` by
    (Cases_on `encoded_len` >> fs[op_taint_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`,
    `left` |-> `Lit 4w`, `right` |-> `encoded_len`,
    `sa` |-> `sn`, `sb` |-> `sr`, `dst` |-> `len`,
    `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`,
    `a` |-> `4w`, `b` |-> `n2w k`]
    (SPEC_ALL attribute_emit_binop_path_ptr)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  rename1 `len = Var len_out` >>
  rename1 `gas_path_ptr D 0 ctx func PG G1 tn1 u 0 G2 tn2 (OK v)` >>
  `~not_fresh_at sn len_out` by
    (qpat_x_assum `emit_op ADD [Lit 4w;encoded_len] _ = _`
      (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `out <> len_out` by metis_tac[] >>
  `ptr_covers G2 tn2 out v (B+4)` by
    (qpat_x_assum `v = _` SUBST1_TAC >>
     irule attribute_ptr_covers_update >> metis_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = sr.cs_current_bb /\
    v.vs_inst_idx = LENGTH sr.cs_current_insts` by
    (`sr.cs_current_bb = sn.cs_current_bb /\
      LENGTH sr.cs_current_insts = SUC (LENGTH sn.cs_current_insts)` by
       (qpat_x_assum `emit_op ADD [Lit 4w;encoded_len] _ = _` mp_tac >>
        simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >>
        strip_tac >> gvs[]) >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [update_var_def] >> metis_tac[]) >>
  `4+k < dimword (:256)` by decide_tac >>
  `eval_operand (Var len_out) v = SOME (n2w (4+k))` by
    (qpat_x_assum `v = _` SUBST1_TAC >>
     simp[eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, word_add_n2w]) >>
  `ptr_covers G2 tn2 out v (4+k)` by
    (gvs[ptr_covers_def] >> decide_tac) >>
  `ptr_inst_ok D 0 0 ctx func G2 tn2
    (mk_inst sr.cs_next_id REVERT [Var out;Var len_out] []) v` by
    (irule custom_error_revert_ptr_inst_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `n2w (4+k)` >> conj_tac >- first_assum ACCEPT_TAC >>
     `w2n (n2w (4+k) : bytes32) = 4+k` by simp[w2n_n2w] >>
     pop_assum (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  `?t. step_inst_base (mk_inst sr.cs_next_id REVERT
    [Var out;Var len_out] []) v = Abort Revert_abort t` by
    (gvs[ptr_covers_def, eval_operand_def] >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx func PG G2 tn2 v 0 G2 tn2
    (Abort Revert_abort t)` by
    (irule emit_abort_zero_path_ptr >> conj_tac >- fs[] >>
     qexistsl_tac [`REVERT`, `[Var out;Var len_out]`, `sr`, `en`] >> gvs[]) >>
  metis_tac[gas_path_ptr_then, ADD_0]
QED
