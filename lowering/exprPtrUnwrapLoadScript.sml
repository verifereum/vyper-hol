(* Word forcing through a checked memory load. *)
Theory exprPtrUnwrapLoad
Ancestors
  exprPtrUnwrapFacts exprSimPtrProps exprSimUnwrapProps exprSimMemoryPath
  exprSimUnwrap exprLoweringProps gasSummaryComposePtr bodyPtrDefs
  exprLowering emitHelper compileEnv loweringPosts vyperState
  venomState finite_map valueEncodingProps gasSummary exprSimMemorySource context

Theorem unwrap_memory_word_input:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type ty v) ==>
  ?v src w.
    t = expr_type e /\ p.ptr_operand = Var src /\
    read_result cx tv ee = (INL v,ee) /\
    eval_operand (Var src) s = SOME w /\ lookup_var src s = SOME w /\
    ptr_covers G tn src s 32 /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
    mload (w2n w) s = typed_val_to_w256 ty v
Proof
  strip_tac >>
  `t = expr_type e /\ ?w v. eval_operand p.ptr_operand s = SOME w /\
     read_result cx tv ee = (INL v,ee) /\
     mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 ty v` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  gvs[ptr_vv_ok_def] >> drule_all ptr_mem_ok_word_input >> strip_tac >>
  gvs[eval_operand_def, mem_word_at_eq_mload]
QED

Theorem unwrap_mload_post:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  read_result cx tv ee = (INL v,ee) /\ p.ptr_location = LocMemory /\
  is_word_type t /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sa /\ emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  eval_operand p.ptr_operand s = SOME w /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op
    (update_var (STRING #"%" (toString sm.cs_next_var)) (mload (w2n w) s) s
       with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all emit_mload_endpoint >> strip_tac >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `not_local_ptr cenv ee.scopes (STRING #"%" (toString sm.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee
     (update_var (STRING #"%" (toString sm.cs_next_var)) (mload (w2n w) s) s
        with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >>
  irule expr_post_of_vv_post_load >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      gvs[vv_post_def, vv_holds_def, read_result_def, return_def,
          mem_word_at_eq_mload]) >>
  qexistsl [`p`, `s`, `sm`, `expr_type e`] >> simp[]
QED

Theorem unwrap_memory_word_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type ty v) ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (expr_type e) v op Gf tnf u /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> drule_all unwrap_memory_word_input >> strip_tac >>
  `emit_op MLOAD [Var src] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >>
  drule_all emit_mload_endpoint >> strip_tac >>
  `emit_op MLOAD [p.ptr_operand] sm = (op,sb)` by simp[] >>
  drule unwrap_mload_post >>
  disch_then (qspecl_then [`w`, `v`, `sb`, `op`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `u = update_var out (mload (w2n w) s) s
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl [`v`, `G'`, `tn'`, `u`] >>
  gvs[gas_marked_exec_ptr_def, gas_explicit_def, Abbr `u`, ptr_val_ok_def] >>
  rpt conj_tac
  >- metis_tac[read_result_gas_obs]
  >- (irule ghost_inv_fresh_frame >>
      qexistsl [`G`, `ee`, `s`, `sa`, `tn`] >>
      simp[update_var_def] >> rpt strip_tac >>
      `x <> STRING #"%" (toString sm.cs_next_var)` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- (gvs[ghost_kept_def] >> metis_tac[])
QED
