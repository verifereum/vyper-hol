(* A selected local Name read, scalar merge assignment and unentered join. *)
Theory bodyPtrSubscriptNamedArm
Ancestors
  bodyPtrSubscriptNamedFrame bodyPtrSubscriptBranchWitness
  bodyPtrCtrlCases fragGasPathPtr bodyPtrDefs loweringPosts
  emitHelper venomState venomInst ptrDiscipline finite_map
  exprLoweringProps compileEnv fragExec codegenRel contextCodegenRel

Theorem named_scalar_arm_continuation:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann id) bs = (eop,bm) /\
  fn_has_code bs bm func /\ local_ptrs_reserved cenv bs /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at bs x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at bs x) /\
  stmt_state_rel ctx func cenv cx es (jump_to bl tt) /\
  ghost_inv d cenv cx es G tn (jump_to bl tt) /\ ~tt.vs_halted /\
  bs.cs_current_bb = bl /\ bs.cs_current_insts = [] /\
  emit_inst ASSIGN [eop] [rv] bm = ((),bn) /\ fn_has_code bm bn func /\
  bo.cs_blocks = bn.cs_blocks /\ bo.cs_current_bb = bn.cs_current_bb /\
  bo.cs_current_insts = bn.cs_current_insts ++
    [mk_inst bn.cs_next_id JMP [Label xl] []] /\ fn_has_code bn bo func /\
  root.cs_next_var <= bs.cs_next_var /\
  (!p. not_fresh_at root p ==> p <> rv) ==>
  ?entry u w Gf tnf sf.
    lookup_scopes id es.scopes = SOME entry /\
    expr_post ctx func cenv cx (Name ann id) es bs bm (jump_to bl tt)
      (es with gas_obs := []) entry.value eop u /\
    eval_operand eop u = SOME w /\
    sf = jump_to xl (update_var rv w u with vs_inst_idx := SUC u.vs_inst_idx) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn (jump_to bl tt) 0 Gf tnf (OK sf) /\
    ~sf.vs_halted /\ op_prov Gf (Var rv) = NONE /\ op_taint tnf (Var rv) = {} /\
    sf.vs_memory = (jump_to bl tt).vs_memory /\
    sf.vs_accounts = (jump_to bl tt).vs_accounts /\
    sf.vs_transient = (jump_to bl tt).vs_transient /\
    sf.vs_call_ctx = (jump_to bl tt).vs_call_ctx /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at root p ==>
      lookup_var p sf = lookup_var p (jump_to bl tt) /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `~(jump_to bl tt).vs_halted /\
   (jump_to bl tt).vs_current_bb = bs.cs_current_bb /\
   (jump_to bl tt).vs_inst_idx = LENGTH bs.cs_current_insts` by
    simp[jump_to_def] >>
  drule_all named_word_scalar_path_frame >>
  disch_then (qspec_then `PG`
    (qx_choose_then `entry` (qx_choose_then `Gu`
      (qx_choose_then `tnu` (qx_choose_then `u` strip_assume_tac))))) >>
  `?w. eval_operand eop u = SOME w` by
    (fs[expr_post_def, expr_val_rel_def]) >>
  `op_taint tnu eop = {}` by fs[ptr_val_ok_def] >>
  qabbrev_tac `Gf = step_prov PG Gu (mk_inst bm.cs_next_id ASSIGN [eop] [rv]) (update_var rv w u)` >>
  qabbrev_tac `tnf = step_taint (mk_inst bm.cs_next_id ASSIGN [eop] [rv]) u (update_var rv w u) tnu` >>
  qabbrev_tac `t = update_var rv w u with vs_inst_idx := SUC u.vs_inst_idx` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Gu tnu u 0 Gf tnf (OK t)` by
    (simp[NoAsms, Abbr `Gf`, Abbr `tnf`, Abbr `t`] >>
     irule scalar_assign_counted_path >> simp[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Gf tnf t 0 Gf tnf (OK (jump_to xl t))` by
    suspend "jump" >>
  qexistsl_tac [`entry`, `u`, `w`, `Gf`, `tnf`, `jump_to xl t`] >>
  simp[GSYM markerTheory.Abbrev_def] >>
  suspend "finish"
QED

Resume named_scalar_arm_continuation[jump]:
  irule emit_jump_zero_path_ptr >>
  simp[Abbr `t`, update_var_def] >>
  qexistsl_tac [`bn`, `bo`] >> simp[] >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def]
QED

Resume named_scalar_arm_continuation[finish]:
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  `op_prov Gf (Var rv) = NONE /\ op_taint tnf (Var rv) = {}` by
    (simp[NoAsms, Abbr `Gf`, Abbr `tnf`] >>
     drule_all scalar_assign_checked_step >> simp[]) >>
  `tnf.t_mem = tnu.t_mem /\ tnf.t_stor = tnu.t_stor /\
   tnf.t_trans = tnu.t_trans /\ tnf.t_imm = tnu.t_imm /\
   (!p. not_fresh_at root p ==>
     lookup_var p t = lookup_var p u /\ FLOOKUP Gf p = FLOOKUP Gu p /\
     op_taint tnf (Var p) = op_taint tnu (Var p))` by
    (simp[NoAsms, Abbr `Gf`, Abbr `tnf`, Abbr `t`] >>
     irule scalar_assign_old_ghost >> metis_tac[]) >>
  `!p. not_fresh_at root p ==> not_fresh_at bs p` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[Abbr `t`, jump_to_def, update_var_def] >>
  rpt strip_tac >>
  `not_fresh_at bs p /\ p <> rv` by metis_tac[] >>
  gvs[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Finalise named_scalar_arm_continuation
