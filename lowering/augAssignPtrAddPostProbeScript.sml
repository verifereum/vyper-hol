(* Post-interface probe only. Updating provenance here makes no assertion
   about reachability of the updated ghost along the original RHS path. *)
Theory augAssignPtrAddPostProbe
Ancestors
  augAssignPtrProvenanceProbe augAssignPtrScalarWitnessProbe bodyPtrDefs
  exprLowering compileEnv context emitHelper finite_map ptrDiscipline venomInst

Theorem uint256_safe_add_sequence:
  compile_safe_add x y (BaseT (UintT 256)) =
  comp_bind (emit_op ADD [x; y]) (\res.
    comp_bind (emit_op LT [res; x]) (\lt_res.
      comp_bind (emit_op ISZERO [lt_res]) (\ok.
        comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res))))
Proof
  simp[compile_safe_add_def, type_bits_def, is_signed_type_def]
QED

Theorem ghost_inv_tag_fresh_result:
  ghost_inv d cenv cx ee G tn t /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa rhs /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) ==>
  ghost_inv d cenv cx ee (G |+ (rhs, site)) tn t
Proof
  strip_tac >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     p <> rhs` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[ghost_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `p <> rhs` by metis_tac[] >>
      first_x_assum (drule_then strip_assume_tac) >>
      gvs[ptr_covers_def, FLOOKUP_UPDATE]) >>
  simp[] >> Cases_on `d` >> fs[return_buf_ptr_def] >>
  PairCases_on `x` >> fs[return_buf_ptr_def] >>
  `x <> rhs` by metis_tac[] >>
  fs[ptr_covers_def, FLOOKUP_UPDATE]
QED

Theorem ghost_kept_tag_fresh_result:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ~not_fresh_at sa rhs ==>
  ghost_kept cenv es sa G0 tn0 s0 (G |+ (rhs, site)) tn
Proof
  simp[ghost_kept_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Every normal-post conjunct is retained, including expr_post's hidden
   stmt_state_rel. Only the ghost is changed, not either machine state. *)
Theorem word_normal_post_tag_fresh_result:
  is_word_type (expr_type e) /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa rhs /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  res = INL v /\
  expr_post ctx fn cenv cx e es sa sb s0 ee v (Var rhs) t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (expr_type e) v (Var rhs) G tn t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e (Var rhs) G t) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  res = INL v /\
  expr_post ctx fn cenv cx e es sa sb s0 ee v (Var rhs) t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx ee (G |+ (rhs, site)) tn t /\
  ptr_val_ok cx (expr_type e) v (Var rhs) (G |+ (rhs, site)) tn t /\
  (~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (Var rhs) (G |+ (rhs, site)) t) /\
  ghost_kept cenv es sa G0 tn0 s0 (G |+ (rhs, site)) tn
Proof
  strip_tac >> simp[] >> conj_tac
  >- (irule ghost_inv_tag_fresh_result >> metis_tac[]) >>
  conj_tac >- fs[ptr_val_ok_def] >>
  irule ghost_kept_tag_fresh_result >> metis_tac[]
QED

Theorem tagged_fresh_result_breaks_add_guard:
  FLOOKUP G left = NONE /\ left <> rhs /\ result <> left ==>
  ~access_ok lo
    (step_prov PG (G |+ (rhs, site))
      (mk_inst addid ADD [Var left; Var rhs] [result]) u)
    fn (mk_inst guardid LT [Var result; Var left] [out]) s
Proof
  strip_tac >> irule clean_add_guard_obstruction >>
  simp[FLOOKUP_UPDATE]
QED

(* Conditional existence from the already checked local-name path. The
   modified H below is deliberately NOT asserted to be that path's ghost. *)
Theorem local_name_post_allows_bad_add_guard:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\ lookup_scopes name es.scopes = SOME entry /\
  word_value entry.value /\ emit_op MLOAD [Var p] sa = (Var rhs,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa left /\ FLOOKUP G0 left = NONE /\ result <> left ==>
  ?H tm t. ?v.
    INL entry.value = INL v /\
    expr_post ctx fn cenv cx (Name ann name) es sa sb s0
      (es with gas_obs := []) v (Var rhs) t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) H tm t /\
    ptr_val_ok cx (expr_type (Name ann name)) v (Var rhs) H tm t /\
    (~is_word_type (expr_type (Name ann name)) ==>
       ptr_buf_ok cenv (Name ann name) (Var rhs) H t) /\
    ghost_kept cenv es sa G0 tn0 s0 H tm /\
    ~access_ok lo
      (step_prov PG H (mk_inst addid ADD [Var left; Var rhs] [result]) u)
      fn (mk_inst guardid LT [Var result; Var left] [out]) s
Proof
  strip_tac >>
  `~not_fresh_at sa rhs` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
  drule_all local_name_enriched_path >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `FLOOKUP H left = NONE` by (fs[ghost_kept_def] >> metis_tac[]) >>
  qexistsl_tac [`H |+ (rhs, site)`, `tm`, `t`, `entry.value`] >>
  simp[vyperASTTheory.expr_type_def] >> conj_tac
  >- (irule ghost_inv_tag_fresh_result >> metis_tac[]) >>
  conj_tac >- simp[ptr_val_ok_def] >>
  conj_tac >- (irule ghost_kept_tag_fresh_result >> metis_tac[]) >>
  irule tagged_fresh_result_breaks_add_guard >> simp[] >> metis_tac[]
QED
