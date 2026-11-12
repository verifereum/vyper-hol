(* Runtime immutable word forcing. *)
Theory exprPtrUnwrapCode
Ancestors
  exprPtrCodeLoad exprSimUnwrapProps exprSimUnwrap exprLoweringProps
  bodyPtrDefs loweringPosts exprLowering context compileEnv
  gasSummaryComposePtr gasSummary vyperState venomState
  finite_map freshWrites exprSimPtrProps exprSimMemorySource

Theorem vv_post_code_source:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = LocCode ==>
  t = post_value_type cenv e /\ ?v a.
    read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME a /\
    immutable_holds cenv cx t (Value v) a ee s
Proof
  strip_tac >> gvs[vv_post_def, vv_holds_def, immutable_holds_def,
    read_result_def, return_def] >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem unwrap_code_word_post:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  read_result cx tv ee = (INL v,ee) /\ p.ptr_location = LocCode /\
  ~cenv.ce_is_ctor /\ is_word_type t /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sa /\ emit_op DLOAD [p.ptr_operand] sm = (op,sb) /\
  eval_operand p.ptr_operand s = SOME a ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op
    (update_var (STRING #"%" (toString sm.cs_next_var))
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
      with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >> gvs[] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all immutable_holds_dload >> strip_tac >>
  `not_local_ptr cenv ee.scopes (STRING #"%" (toString sm.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee
    (update_var (STRING #"%" (toString sm.cs_next_var))
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >>
  irule expr_post_of_vv_post_load_physical >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexistsl [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[update_var_def] >>
  rpt strip_tac >> `x <> STRING #"%" (toString sm.cs_next_var)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem unwrap_code_word_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ is_word_type t /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (post_value_type cenv e) v op Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >>
  `emit_op DLOAD [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule_all emit_code_load_ptr_path >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  drule unwrap_code_word_post >>
  disch_then (qspecl_then [`v`, `sb`, `op`, `a`] mp_tac) >>
  simp[] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  qexistsl [`v`, `G'`, `tn'`, `u`] >>
  gvs[gas_marked_exec_ptr_def, gas_explicit_def, ptr_val_ok_def] >>
  rpt conj_tac
  >- metis_tac[read_result_gas_obs]
  >- (irule ghost_inv_fresh_frame >>
      qexistsl [`G`, `ee`, `s`, `sa`, `tn`] >>
      simp[update_var_def] >> rpt strip_tac >>
      `x <> STRING #"%" (toString sm.cs_next_var)` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- (gvs[ghost_kept_def] >> metis_tac[])
QED
