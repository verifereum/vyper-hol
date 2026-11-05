(* Preserve the concrete read frame on the same typed Name witness.
   ghost_kept deliberately does not expose these raw concrete equalities. *)
Theory bodyPtrSubscriptNamedFrame
Ancestors
  bodyPtrSubscriptNamedScalar bodyPtrSubscriptScalarLoad exprSimProps
  exprSimDefs bodyPtrDefs exprLoweringProps emitHelper venomState
  ptrDiscipline venomInst finite_map compileEnv loweringSlice

Theorem named_word_scalar_path_frame:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?entry Gf tnf sf.
    lookup_scopes id es.scopes = SOME entry /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx func cenv cx (Name ann id) es sa sb s
      (es with gas_obs := []) entry.value op sf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
    ptr_val_ok cx ann entry.value op Gf tnf sf /\
    ghost_kept cenv es sa G tn s Gf tnf /\ op_prov Gf op = NONE /\
    ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all named_word_preparation >> strip_tac >>
  drule_all lower_value_name_word >> strip_tac >>
  `?out. op = Var out` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >> gvs[] >>
  drule_all emit_mload_counted_scalar >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `tnf.t_imm = tn.t_imm` by
    (qpat_x_assum `tnf = _` (fn th => rewrite_tac[th]) >>
     simp[step_taint_def, mk_inst_def, imm_taint_def]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
   ghost_kept cenv es sa G tn s Gf tnf` by
    (irule named_read_ghost_frame >> simp[update_var_def]) >>
  `sf = update_var out (typed_val_to_w256 entry.type entry.value)
    (s with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    gvs[update_var_def] >>
  `expr_post ctx func cenv cx (Name ann id) es sa sb s
    (es with gas_obs := []) entry.value (Var out) sf` by
    (qpat_assum `sf = update_var _ _ (_ with vs_inst_idx := _)`
       (fn th => rewrite_tac[th]) >>
     irule named_typed_word_post >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  simp[ptr_val_ok_def, update_var_def]
QED
