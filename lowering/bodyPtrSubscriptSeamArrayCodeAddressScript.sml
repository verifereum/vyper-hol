(* ADD on code addresses is clean arithmetic, not a memory-coverage step. *)
Theory bodyPtrSubscriptSeamArrayCodeAddress
Ancestors
  bodyPtrAttributeAdd bodyPtrSubscriptAddress bodyPtrSubscriptReadOnly
  bodyPtrSubscriptBoundsRun emitHelperProps exprLoweringProps finite_map
  venomState venomInst ptrDiscipline emitHelper compileEnv
  bodyPtrSubscriptBounds bodyPtrSubscriptNamedTuplePostBoundary freshWrites words
  fragExec fragGasPathPtr

Theorem emit_clean_add_counted:
  emit_op ADD [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a+b) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
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
  strip_tac >>
  drule_all (attribute_emit_binop_path_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >> gvs[] >>
  `!q. not_fresh_at sa q ==> q <> out` by
    (drule emitted_operand_reserved >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` >>
  `op_prov Gf (Var out) = NONE` by
    (simp[Abbr `Gf`, op_prov_def] >> irule step_prov_add_none >> simp[mk_inst_def]) >>
  `!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    stmt_state_rel ctx func cenv cx es sf` by
    (rpt strip_tac >> simp[Abbr `sf`] >> irule fresh_add_stmt_state_rel >>
     simp[] >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qexistsl [`Gf`, `tnf`, `sf`] >>
  gvs[Abbr `sf`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem code_mul_add_counted:
  emit_op MUL [idx;Lit (n2w elem_size)] sa = (Var offset,sm) /\
  emit_op ADD [base_op;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q ==> not_fresh_at sa q) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
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
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `eval_operand (Lit (n2w elem_size)) s = SOME (n2w elem_size) /\
   op_taint tn (Lit (n2w elem_size)) = {} /\
   op_prov G (Lit (n2w elem_size)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (binary_counted_read_only |>
    Q.INST [`opc` |-> `MUL`, `f` |-> `word_mul`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[word_mul_n2w] >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `eval_operand (Var offset) s1 = SOME (n2w (i * elem_size))` by simp[eval_operand_def] >>
  drule_all emit_clean_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm q` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem code_dynamic_address_counted:
  emit_op ADD [base_op;Lit 32w] sa = (Var data,sm) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sm = (Var offset,sn) /\
  emit_op ADD [Var data;Var offset] sn = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (32 + i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
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
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, cs_extends_trans, fn_has_code_split] >>
  `eval_operand (Lit 32w) s = SOME 32w /\
   op_taint tn (Lit 32w) = {} /\ op_prov G (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all emit_clean_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `not_fresh_at sm data` by metis_tac[emitted_operand_reserved] >>
  `(!q. Var data = Var q ==> not_fresh_at sm q) /\
   (!l. Var data <> Label l) /\ eval_operand (Var data) s1 = SOME (a + 32w)` by
    simp[eval_operand_def] >>
  drule_all code_mul_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl [`G2`, `tn2`, `s2`] >>
  simp[GSYM word_add_n2w, WORD_ADD_ASSOC] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm q` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED
