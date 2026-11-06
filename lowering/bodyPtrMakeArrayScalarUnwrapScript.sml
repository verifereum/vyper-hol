(* Actual scalar unwrap branches share the clean word/destination interface.
   No scalar source-buffer coverage is required or exported. *)
Theory bodyPtrMakeArrayScalarUnwrap
Ancestors
  bodyPtrMakeArrayUnwrapIdentity bodyPtrMakeArrayScalarSemantics
  bodyPtrMakeArrayMemoryWord bodyPtrMakeArrayMloadFrame
  bodyPtrMakeArrayExternalWord bodyPtrMakeArrayWordClean
  bodyPtrDefs loweringPosts context compileEnv venomState
  exprSimProps exprSimUnwrapProps exprLoweringProps freshWrites
  bodyPtrMakeArrayLoad typedCopyPtr valueEncodingProps

Theorem scalar_stack_unwrap_endpoint:
  unwrap_value ce (StackValue t arg) sm = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 es' tv (StackValue t arg) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t arg) es' G tn s /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx es' G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  ptr_covers G tn dst s n ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v op sf /\
    eval_operand op sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf op = {} /\
    ptr_val_ok cx (expr_type e) v op Gf tnf sf /\
    ghost_inv d ce cx es' Gf tnf sf /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var dst sf = lookup_var dst s /\
    ptr_covers Gf tnf dst sf n
Proof
  strip_tac >> drule_all unwrap_stack_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G`, `tn`, `s`] >>
  gvs[ptr_val_ok_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem scalar_load_expr_post:
  vv_post ctx fn ce cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  sa.cs_next_var <= sm.cs_next_var /\
  not_local_ptr ce es'.scopes tmp /\
  (!x. not_fresh_at sm x ==> x <> tmp) ==>
  expr_post ctx fn ce cx e es sa sb s0 es' v (Var tmp)
    ((update_var tmp (typed_val_to_w256 ty v) s) with
      vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `vv_post ctx fn ce cx e es sa sm s0 es' (Value v) (LocatedValue t p) s`
    by metis_tac[vv_post_read_result] >>
  irule expr_post_of_vv_post_load >>
  conj_tac >- simp[] >>
  conj_tac
  >- simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (rewrite_tac[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >>
      gvs[vv_post_def]) >>
  qexistsl_tac [`p`, `s`, `sm`, `t`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem scalar_external_unwrap_endpoint:
  vv_post ctx fn ce cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) es' G tn s /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ opc = DLOAD)) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [p.ptr_operand] [tmp]) /\
  eval_operand p.ptr_operand s = SOME a /\
  step_inst_base (mk_inst id opc [p.ptr_operand] [tmp]) s =
    OK (update_var tmp (typed_val_to_w256 ty v) s) /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. not_fresh_at sm x ==> x <> tmp) /\
  not_local_ptr ce es'.scopes tmp /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  ghost_inv d ce cx es' G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  s.vs_current_bb = sb.cs_current_bb /\
  SUC s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  tmp <> dst /\ ptr_covers G tn dst s n ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v (Var tmp) sf /\
    eval_operand (Var tmp) sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf (Var tmp) = {} /\
    ptr_val_ok cx (expr_type e) v (Var tmp) Gf tnf sf /\
    ghost_inv d ce cx es' Gf tnf sf /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var dst sf = lookup_var dst s /\
    ptr_covers Gf tnf dst sf n
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_vv_word_key_clean >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> tmp` by
    metis_tac[not_fresh_at_mono] >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  `(opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
   (opc = TLOAD ==> key_taint tn.t_trans a = {})` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
  drule_all scalar_load_expr_post >>
  disch_then (qspec_then `sb` assume_tac) >>
  drule_at (Pat `get_instruction _ _ = _`) external_word_materialize_endpoint >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`ctx`, `PG`, `D`] mp_tac) >>
  impl_tac >- (simp[] >> qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  simp[ptr_val_ok_def] >>
  gvs[update_var_def]
QED

Theorem scalar_memory_unwrap_endpoint:
  vv_post ctx fn ce cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ value_has_type ty v /\
  p.ptr_operand = Var src /\ ptr_covers G tn src s 32 /\
  ptr_mem_ok cx (expr_type e) v (Var src) G tn s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  eval_operand (Var src) s = SOME a /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. not_fresh_at sm x ==> x <> tmp) /\
  not_local_ptr ce es'.scopes tmp /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  s.vs_current_bb = sb.cs_current_bb /\
  SUC s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  tmp <> dst /\ ptr_covers G tn dst s n ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v (Var tmp) sf /\
    eval_operand (Var tmp) sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf (Var tmp) = {} /\
    ptr_val_ok cx (expr_type e) v (Var tmp) Gf tnf sf /\
    ghost_inv d ce cx es' Gf tnf sf /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var dst sf = lookup_var dst s /\ ptr_covers Gf tnf dst sf n
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_load_expr_post >> disch_then (qspec_then `sb` assume_tac) >>
  `!x. not_fresh_at sa x ==> x <> tmp` by metis_tac[not_fresh_at_mono] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem`
    by metis_tac[ptr_mem_word_clean] >>
  `val_in_memory ty v (w2n a) s.vs_memory` by
    (gvs[ptr_mem_ok_def] >> first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload (w2n a) s = typed_val_to_w256 ty v` by
    metis_tac[val_in_memory_word_type, mem_word_at_eq_mload] >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn`,
    `(update_var tmp (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule mload_ptr_path >> simp[]) >>
  conj_tac >- gvs[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def,
                   finite_mapTheory.FLOOKUP_UPDATE] >>
  `op_taint (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {}` by
    (drule_all mload_ghost_clean >> simp[]) >>
  simp[ptr_val_ok_def] >>
  conj_tac >- simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.step_prov_def,
                    ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
                    venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  conj_tac >-
    (qpat_x_assum `SUC _ = _` (fn th => rewrite_tac[GSYM th]) >>
     irule mload_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule mload_ghost_kept >> simp[] >> metis_tac[]) >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `mload _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `SUC _ = _` (fn th => rewrite_tac[GSYM th]) >>
  irule (SRULE [update_var_def] mload_ptr_old_coverage) >> simp[]
QED

(* vv_post's memory representation and val_wf are not semantic typing.
   This probe records why the public scalar interface needs a typing audit. *)
Theorem scalar_memory_typing_gap:
  val_in_memory (BaseTV BoolT) NoneV 0 mem /\
  val_wf (BaseTV BoolT) NoneV /\
  ~value_has_type (BaseTV BoolT) NoneV
Proof
  EVAL_TAC
QED
