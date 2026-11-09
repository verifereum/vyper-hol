(* The expression post exposes the lowered tuple layout. *)
Theory tuplePlaceRhsCert
Ancestors
  tuplePlacePrefixCert tuplePlaceBorrow exprLowering loweringPosts
  valueEncodingProofs compileEnv vyperAST

Theorem tuple_place_post_tuple_type:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys ==>
  post_value_type cenv e = TupleT ltys
Proof
  rpt strip_tac >> Cases_on `e` >>
  gvs[vyperASTTheory.expr_type_def, lowered_value_type_def,
      post_value_type_def]
  >- (Cases_on `b` >> gvs[lowered_value_type_def, concat_buffer_type_def, expr_type_def])
  >- (Cases_on `t0` >> gvs[lowered_value_type_def, expr_type_def]) >>
  rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
  gvs[lowered_value_type_def, post_value_type_def, is_word_type_def,
      is_bytestring_type_def]
QED

Theorem tuple_place_rhs_certificate:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv ==>
  stmt_state_rel ctx func cenv cx es1 sv /\
  expr_val_rel cx (TupleT ltys) (ArrayV (TupleV vs)) op sv /\
  expr_val_at cenv cx (TupleT ltys) sa su es1 (ArrayV (TupleV vs)) op sv /\
  ?w. eval_operand op sv = SOME w /\
    tuple_in_memory vs ltvs (w2n w) sv.vs_memory /\ tuple_val_wf vs ltvs /\
    tuple_place_snapshot cenv cx es1 sa.cs_next_id su.cs_next_id
      tys ltys ltvs w sv
Proof
  rpt strip_tac >>
  `post_value_type cenv e = TupleT ltys` by
    (irule tuple_place_post_tuple_type >> simp[]) >>
  gvs[expr_post_def] >>
  `?w. eval_operand op sv = SOME w /\
       tuple_in_memory vs ltvs (w2n w) sv.vs_memory` by
    gvs[expr_val_rel_def, is_word_type_def, valueEncodingTheory.val_in_memory_def] >>
  qexists `w` >> simp[] >> conj_tac
  >- (drule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
      simp[valueEncodingTheory.val_wf_def]) >>
  Cases_on `ltys = tys`
  >- (drule_all tuplePlaceSnapshotTheory.tuple_place_expr_snapshot_cases >>
      strip_tac
      >- (irule tuple_place_snapshot_zero >> simp[])
      >- (irule tuple_place_snapshot_owned >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
          rpt strip_tac >> first_x_assum drule >> simp[]) >>
      irule tuple_place_snapshot_borrowed >>
      simp[] >> qexistsl [`b`, `n`, `sz`] >> simp[] >>
      irule tuple_place_borrowed_tuple_path >> goal_assum (drule_at Any)) >>
  `expr_val_own cenv cx (TupleT ltys) sa su es1 (ArrayV (TupleV vs)) op sv` by
    metis_tac[vyperASTTheory.type_11] >>
  drule_all tuplePlaceSnapshotTheory.tuple_place_expr_owned_snapshot >> strip_tac
  >- (irule tuple_place_snapshot_zero >> simp[]) >>
  irule tuple_place_snapshot_owned >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
          rpt strip_tac >> first_x_assum drule >> simp[]
QED
