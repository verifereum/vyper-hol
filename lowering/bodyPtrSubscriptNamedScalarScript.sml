(* Typed local preparation for the constructive scalar execution pilot. *)
Theory bodyPtrSubscriptNamedScalar
Ancestors
  bodyPtrSubscriptScalarLoad exprSimNameValue representationCleanPtr
  entryDecodeProps stmtSimReturn exprSimHypsDefs exprLoweringProps
  bodyPtrDefs exprSimDefs loweringPosts vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperValue valueEncoding valueEncodingProps
  codegenRel contextCodegenRel compileEnv ptrDiscipline finite_map
  exprSimProps emitHelper venomState vyperAST localPtrsProps varsExt
  loweringSlice venomInst fragGasPathPtr gasSummary

Theorem named_word_preparation:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?entry p sz a.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ann /\
    lookup_var p s = SOME a /\ ptr_covers G tn p s 32 /\
    mload (w2n a) s = typed_val_to_w256 entry.type entry.value /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `?a. lookup_var p s = SOME a /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `type_memory_size entry.type = 32` by metis_tac[word_type_sizes] >>
  `ptr_covers G tn p s sz /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory entry.type entry.value (w2n a) mem)` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         mem_word_at (w2n a) mem = typed_val_to_w256 entry.type entry.value` by
    (rpt strip_tac >> drule_all val_in_memory_word >> metis_tac[]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  qexistsl_tac [`entry`, `p`, `sz`, `a`] >> simp[] >> conj_tac
  >- (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_ADD]) >>
  rewrite_tac[GSYM mem_word_at_eq_mload] >> first_x_assum irule >>
  simp[mem_agree_outside_def]
QED

(* Unlike the older word_value post, this includes address and bytesN:
   the result word is interpreted using the evaluated annotation. *)
Theorem named_typed_word_post:
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  expr_post ctx func cenv cx (Name ann id) es sa sb s0
    (es with gas_obs := []) v (Var out)
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  `not_local_ptr cenv (es with gas_obs := []).scopes out` by
    (gvs[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`,
                            `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, locals_kept_mem] >>
  rpt strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> x` by
    (strip_tac >> gvs[not_fresh_at_def]) >> simp[]
QED

(* Read-only scalar execution preserves the ghost frame through old variables. *)
Theorem named_read_ghost_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sf.vs_memory = s.vs_memory /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
  ghost_kept cenv es sa G tn s Gf tnf
Proof
  strip_tac >> conj_tac
  >- (fs[ghost_inv_def] >> rpt conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
          first_assum drule_all >> strip_tac >>
          fs[ptr_covers_def] >> metis_tac[])
      >- (Cases_on `d` >> gvs[return_buf_ptr_def, return_buf_frame_def] >>
          PairCases_on `x` >> gvs[return_buf_ptr_def, return_buf_frame_def] >>
          fs[ptr_covers_def] >> metis_tac[]) >>
      gvs[stor_taint_ok_def]) >>
  simp[ghost_kept_def]
QED

Theorem named_word_scalar_path:
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
    ghost_kept cenv es sa G tn s Gf tnf /\ op_prov Gf op = NONE
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
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[ptr_val_ok_def]
QED

Theorem named_word_scalar_outcome:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind (eval_expr cx (Name ann id)) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind (eval_expr cx (Name ann id)) (read_result cx)) (es,s,G,tn)
    (\res ee Gf tnf sf. ?v. res = INL v /\
      expr_post ctx func cenv cx (Name ann id) es sa sb s ee v op sf /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee Gf tnf sf /\
      ptr_val_ok cx (expr_type (Name ann id)) v op Gf tnf sf /\
      (~is_word_type (expr_type (Name ann id)) ==>
         ptr_buf_ok cenv (Name ann id) op Gf sf) /\
      ghost_kept cenv es sa G tn s Gf tnf /\ op_prov Gf op = NONE)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all named_word_scalar_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL entry.value`, `es`, `Gf`, `tnf`, `OK sf`] >>
  simp[expr_type_def] >> gen_tac >>
  qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
    mp_tac eval_name_word >> simp[gas_explicit_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED
