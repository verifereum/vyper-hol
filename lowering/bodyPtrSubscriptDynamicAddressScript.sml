(* Address tail of the actual unsigned dynamic-memory selector. *)
Theory bodyPtrSubscriptDynamicAddress
Ancestors
  bodyPtrSubscriptCountedAdd bodyPtrSubscriptBoundsRun bodyPtrSubscriptReadOnly
  bodyPtrSubscriptBounds appendStorageGhostPtr emitHelperProps exprLoweringProps
  freshWrites fragExec fragGasPathPtr emitHelper compileEnv ptrDiscipline bodyPtrDefs
  venomState venomInst venomExecSemantics finite_map words loweringPosts

Theorem mul_add_counted_read_only:
  emit_op MUL [idx;Lit (n2w elem_size)] sa = (Var offset,sm) /\
  emit_op ADD [Var p;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  i * elem_size + child_sz <= parent_sz /\
  w2n a + i * elem_size < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
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
  `ptr_covers G1 tn1 p s1 parent_sz` by
    (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_var p s1 = SOME a /\ not_fresh_at sm p` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (Var offset) s1 = SOME (n2w (i * elem_size))` by simp[eval_operand_def] >>
  `i * elem_size < dimword (:256)` by decide_tac >>
  drule_all emit_add_displacement_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm q` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem dynamic_address_counted_read_only:
  emit_op ADD [Var p;Lit 32w] sa = (Var data,sm) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sm = (Var offset,sn) /\
  emit_op ADD [Var data;Var offset] sn = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  32 + i * elem_size + child_sz <= parent_sz /\
  w2n a + 32 + i * elem_size < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (32 + i * elem_size)) /\
    ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, cs_extends_trans, fn_has_code_split] >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\
   op_taint tn (Lit 32w) = {} /\ op_prov G (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `32 < dimword (:256) /\ 32 + (parent_sz - 32) <= parent_sz /\
   w2n a + 32 < dimword (:256)` by (simp[] >> decide_tac) >>
  drule_all (emit_add_displacement_counted |>
    Q.INST [`off` |-> `32`, `child_sz` |-> `parent_sz - 32`]) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `not_fresh_at sm data` by metis_tac[emitted_operand_reserved] >>
  `i * elem_size + child_sz <= parent_sz - 32 /\
   w2n (a + 32w) + i * elem_size < dimword (:256)` by
    (simp[w2n_add_2] >> decide_tac) >>
  drule_all mul_add_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >>
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
