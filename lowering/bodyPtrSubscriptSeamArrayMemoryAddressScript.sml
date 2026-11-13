Theory bodyPtrSubscriptSeamArrayMemoryAddress
Ancestors
  bodyPtrSubscriptSeamArrayMemoryNumeric bodyPtrSubscriptCountedAdd
  bodyPtrSubscriptReadOnly bodyPtrSubscriptBounds appendStorageGhostPtr
  emitHelperProps exprLoweringProps freshWrites fragExec fragGasPathPtr
  emitHelper compileEnv ptrDiscipline bodyPtrDefs venomState venomInst
  venomExecSemantics finite_map words loweringPosts

(* MUL with a literal discards provenance even when idx has provenance. *)
Theorem literal_mul_add_counted:
  emit_op MUL [idx;Lit (n2w elem_size)] sa = (Var offset,sm) /\
  emit_op ADD [Var p;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\
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
  `!dst. step_inst_base (mk_inst sa.cs_next_id MUL [idx;Lit (n2w elem_size)] [dst]) s =
    OK (update_var dst (n2w (i * elem_size)) s)` by
    (gen_tac >> rewrite_tac[GSYM word_mul_n2w] >> irule step_MUL >>
     simp[eval_operand_def]) >>
  drule_all (literal_numeric_counted_read_only |> Q.INST [`opc` |-> `MUL`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `ptr_covers G1 tn1 p s1 parent_sz` by
    (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_var p s1 = SOME a /\ not_fresh_at sm p` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >>
  `eval_operand (Var offset) s1 = SOME (n2w (i * elem_size))` by simp[eval_operand_def] >>
  `i * elem_size < dimword (:256)` by decide_tac >>
  drule_all emit_add_displacement_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> `not_fresh_at sm q` by
        metis_tac[ci_mono_def, not_fresh_at_mono] >> metis_tac[]) >>
  rpt strip_tac >> `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >> metis_tac[]
QED
