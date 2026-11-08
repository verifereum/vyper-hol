(* Values reconstructed at a later endpoint using historical byte windows. *)
Theory exprExtRequestReconstruct
Ancestors
  exprExtRequestHistory exprExtRequestReadProbe exprExtRequestSuffix
  loweringPosts exprSafeOperand exprSimProps valueEncodingProofs
  valueEncoding compileEnv venomExecSemantics venomState vyperValue
  valueTypingMemoryProps

Theorem extrequest_history_operand:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  safe_operand sc op /\ eval_operand op tc = SOME w ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >>
  gvs[safe_operand_def, eval_operand_def, extrequest_history_frame_def] >>
  metis_tac[]
QED

Theorem extrequest_history_alloc_window:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  FLOOKUP tc.vs_allocas aid = SOME (b,sz) /\ aid < sc.cs_next_id /\
  (!n lb lsz. local_region cenv ec.scopes tc n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len t.vs_memory = mem_bytes_at off len tc.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory` by
    (gvs[extrequest_history_frame_def, regions_disjoint_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> metis_tac[]
QED

Theorem extrequest_history_local_window:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  local_region cenv ec.scopes tc n b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len t.vs_memory = mem_bytes_at off len tc.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> metis_tac[]
QED

Theorem extrequest_history_expr_value:
  expr_val_at cenv cx ty sa sc ec v op tc /\
  expr_val_rel cx ty v op tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  safe_operand sc op ==>
  expr_val_rel cx ty v op t
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `eval_operand op t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >>
  simp[expr_val_rel_def] >> rpt strip_tac >>
  Cases_on `is_word_type ty` >- gvs[] >> gvs[] >>
  irule val_in_memory_footprint_agree >>
  conj_tac >- (gvs[expr_val_at_def] >> metis_tac[]) >>
  qexists_tac `tc.vs_memory` >> simp[] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[] >> sym_tac
  >- (irule extrequest_history_alloc_window >>
      qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule extrequest_history_local_window >>
      qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[mem_bytes_at_def]
QED

Theorem extrequest_history_memory_window:
  vv_at cenv cx ty sa sc ec r (LocatedValue ty p) tc /\
  p.ptr_location = LocMemory /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  read_result cx r ec = (INL v,ec) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand tc = SOME w ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) tc.vs_memory
Proof
  simp[vv_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (irule extrequest_history_alloc_window >>
      qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule extrequest_history_local_window >>
      qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[mem_bytes_at_def]
QED

Theorem extrequest_word_footprint:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def] >>
  rpt strip_tac
  >~ [`evaluate_type _ (FlagT _) = _`]
  >- (gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
      simp[val_footprint_def, type_memory_size_def]) >>
  rename1 `evaluate_type _ (BaseT bt) = _` >> Cases_on `bt` >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def] >>
  Cases_on `b` >> gvs[is_word_type_def, evaluate_type_def,
    val_footprint_def, type_memory_size_def]
QED

Theorem extrequest_history_memory_holds:
  vv_at cenv cx ty sa sc ec r (LocatedValue ty p) tc /\
  vv_holds cenv cx ty r (LocatedValue ty p) ec tc /\
  p.ptr_location = LocMemory /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  safe_operand sc p.ptr_operand ==>
  vv_holds cenv cx ty r (LocatedValue ty p) ee t
Proof
  strip_tac >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def] >> strip_tac >>
  `eval_operand p.ptr_operand t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `read_result cx r ee = (INL v,ee)` by
    (`extrequest_read_frame cx ec ee` by gvs[extrequest_history_frame_def] >>
     drule extrequest_read_result_frame >> simp[]) >>
  simp[vv_holds_def] >> gen_tac >> disch_tac >>
  drule_all extrequest_history_memory_window >> strip_tac >>
  conj_tac
  >- (irule val_in_memory_footprint_agree >>
      conj_tac >- simp[] >> qexists_tac `tc.vs_memory` >> simp[]) >>
  strip_tac >>
  `val_footprint tvt v = 32` by metis_tac[extrequest_word_footprint] >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem extrequest_history_immutable_holds:
  immutable_holds cenv cx ty r w ec tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t ==>
  immutable_holds cenv cx ty r w ee t
Proof
  strip_tac >>
  `extrequest_read_frame cx ec ee` by gvs[extrequest_history_frame_def] >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def] >> strip_tac >>
  `read_result cx r ee = (INL v,ee)` by
    (drule extrequest_read_result_frame >> simp[]) >>
  `ALOOKUP ec.immutables cx.txn.target = ALOOKUP ee.immutables cx.txn.target`
    by gvs[extrequest_read_frame_def] >>
  fs[] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[] >>
  disj2_tac >> simp[] >>
  irule val_in_memory_footprint_agree >>
  conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qexists_tac `tc.vs_memory` >> simp[] >>
  `val_footprint tvt v <= type_memory_size tvt` by
    metis_tac[value_has_type_memory_wf, val_footprint_le] >>
  `mem_bytes_at off (type_memory_size itv) t.vs_memory =
   mem_bytes_at off (type_memory_size itv) tc.vs_memory` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem extrequest_history_holds:
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty op => safe_operand sc op
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) ==>
  vv_holds cenv cx (expr_type e) r vv ee t
Proof
  strip_tac >>
  `extrequest_read_frame cx ec ee` by gvs[extrequest_history_frame_def] >>
  Cases_on `vv`
  >- (gvs[vv_post_def, vv_holds_def, vv_at_def] >>
      `read_result cx r ee = (INL v,ee)` by
        (drule extrequest_read_result_frame >> simp[]) >>
      simp[] >> irule extrequest_history_expr_value >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `t' = expr_type e` by gvs[vv_post_def, vv_holds_def] >> gvs[] >>
  Cases_on `p.ptr_location`
  >- (irule extrequest_history_memory_holds >>
      goal_assum (drule_at Any) >> gvs[vv_post_def] >> metis_tac[]) >>
  gvs[vv_post_def, vv_holds_def] >>
  `eval_operand p.ptr_operand t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >> simp[]
  >- (irule extrequest_storage_holds_kept >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`ec`, `tc`] >> simp[] >>
      metis_tac[slot_loc_def])
  >- (irule extrequest_storage_holds_kept >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`ec`, `tc`] >> simp[] >>
      metis_tac[slot_loc_def]) >>
  irule extrequest_history_immutable_holds >>
  goal_assum (drule_at Any) >> simp[]
QED
