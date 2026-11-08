(* Probe the proposed semantic-purity adapter before using same-state geometry. *)
Theory tuplePlacePointerReady
Ancestors
  supportedTargets targetPlaceLive vyperPureExpr tuplePlaceReachable tuplePlaceHead

Theorem tuple_place_supported_gas_index_not_semantic_pure:
  supported_target_pure tops
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])) /\
  ~EVERY pure_expr (target_indices
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])))
Proof
  EVAL_TAC
QED

(* Actual evaluation may change gas and other non-scope state. *)
Theorem tuple_place_base_target_transition:
  eval_base_place cx bt es = (INL (PlaceR p),ee) ==>
  eval_target_place cx bt es = (INL p,ee)
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_place_def, vyperStateTheory.return_def]
QED

Theorem tuple_place_target_endpoint_writable:
  expr_sim_inv cenv cx env es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) ==>
  writable_place_result cx ee (PlaceR p)
Proof
  rpt strip_tac >>
  drule tuple_place_base_target_transition >> strip_tac >>
  gvs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all exprSimPopNestedLocalSourceTheory.eval_target_place_writable >> simp[]
QED

Theorem tuple_place_head_pointer_operands:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  i <= j /\ j < LENGTH ltys ==>
  ?v. eval_operand (EL j elems) s = SOME v /\
    if is_word_type (EL j ltys) then
      v = typed_val_to_w256 (EL j ltvs) (EL j vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))
Proof
  strip_tac >> fs[tuple_place_head_def] >>
  `MEM (EL j elems) elems` by (irule listTheory.EL_MEM >> simp[]) >>
  `?x. EL j elems = Var x` by gvs[listTheory.EVERY_MEM] >>
  `?v. eval_operand (EL j elems) s0 = SOME v /\
       if is_word_type (EL j ltys) then
         v = typed_val_to_w256 (EL j ltvs) (EL j vs)
       else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))` by
    (qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `j` mp_tac) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists `v` >> conj_tac
  >- (irule tuplePlaceSnapshotTheory.tuple_place_target_operand >>
      conj_tac >- simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[]
QED


Theorem tuple_place_pointer_local_regions:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sp /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s ==>
  (!n b sz. local_region cenv ee.scopes s n b sz <=>
            local_region cenv es.scopes s0 n b sz)
Proof
  strip_tac >>
  drule_all tuplePlaceBorrowTheory.tuple_place_pure_target_scopes >> strip_tac >>
  drule tuplePlaceSnapshotTheory.tuple_place_target_frame >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by simp[] >>
  drule_all wordArgsPtrTheory.wb_frame_local_regions >> metis_tac[]
QED

Theorem tuple_place_pointer_snapshot:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) ==>
  tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s
Proof
  strip_tac >>
  `sp.cs_next_id <= sa.cs_next_id` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!n b sz. local_region cenv ee.scopes s n b sz <=>
             local_region cenv es.scopes s0 n b sz` by
    (irule tuple_place_pointer_local_regions >>
     fs[tuple_place_head_def] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[tuple_place_head_def, tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl [`n`, `b`, `sz`] >> simp[]
QED
