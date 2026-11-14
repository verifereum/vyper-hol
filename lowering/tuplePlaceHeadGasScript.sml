(* Gas composition for a place-valued pointer prefix. *)
Theory tuplePlaceHeadGas
Ancestors
  tuplePlaceSuffixCode tuplePlaceTargetGas tuplePlaceWriteOutcome tuplePlaceSourceGas
  tuplePlaceSourceHead tuplePlaceCompilerStep placeStoreStaticExit
  gasOutcome gasSummary gasSummaryCompose gasExemptCert vyperState
  targetPlaceSimCases exprSimDefs fragGasMode fragGasPath

Theorem tuple_place_gas_outcome_prefix:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> place evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists `left ++ right` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`out`,`fin`,`r`] >>
      conj_tac >- (irule gas_marked_exec_bind_normal >>
                    goal_assum drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err,ef) (callee,tf)` >>
  qexists `left ++ right` >> disj2_tac >>
  qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_bind_place >>
  qexistsl [`mid`,`t`,`v`] >> simp[GSYM ignore_bind_def]
QED

Theorem tuple_place_gas_outcome_bind_exec:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> place evaluation_result) (es,s0) P Exit /\
  (!res ee t. P res ee t ==> ?v. res = INL v) /\
  (!res ee r. Exit res ee r ==> ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
    P (INL v) (mid with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func) (k v) (mid with gas_obs := [],t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o REWRITE_RULE [gas_outcome_def]) assume_tac) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          irule tuple_place_gas_outcome_prefix >>
          qexistsl [`marks`,`mid`,`t`,`v`] >>
          simp[] >> first_x_assum irule >> simp[] >>
          goal_assum (drule_at Any)) >>
      `?ex. res = INR ex /\ R (INR ex) (mid with gas_obs := []) r` by metis_tac[] >>
      gvs[] >> rewrite_tac[gas_outcome_def] >>
      qexists `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR ex`,`mid`,`r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >> simp[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ef) (callee,tf)` >>
  rewrite_tac[gas_outcome_def] >> qexists `marks` >> disj2_tac >>
  qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_error_place >> simp[]
QED

Theorem tuple_place_head_gas_obs[simp]:
  tuple_place_head ctx func cenv cx (es with gas_obs := gs)
    lo cs tys ltys ltvs vs elems w i s =
  tuple_place_head ctx func cenv cx es lo cs tys ltys ltvs vs elems w i s
Proof
  simp[tuplePlaceHeadTheory.tuple_place_head_def,
       tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
QED

Theorem tuple_place_target_post_gas_obs[simp]:
  (target_post ctx func cenv cx (es with gas_obs := gs) sa sb s0 ee pv vt r s =
   target_post ctx func cenv cx es sa sb s0 ee pv vt r s) /\
  (target_post ctx func cenv cx es sa sb s0 (ee with gas_obs := hs) pv vt r s =
   target_post ctx func cenv cx es sa sb s0 ee pv vt r s)
Proof
  simp[loweringPostsTheory.target_post_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def]
QED

(* Replay is the only source of the concrete pointer endpoint used below. *)
Theorem tuple_place_marked_head_step:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ EVERY (supported_expr tops) (target_indices bt) /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\ ~immutable_root cx bt /\
  gas_marked_exec F (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) mid (OK s) /\
  target_post ctx func cenv cx es sp sa s0 (mid with gas_obs := [])
    (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (if is_word_type (EL i ltys) then
     if is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) then
       compile_store_at_loc cenv.ce_imm_alloca (FST r) (EL i elems) (FST (SND r))
     else emit_void INVALID []
   else compile_assign_value cenv (FST r)
     (case FST (SND r) of SOME l => l | NONE => LocMemory)
     (EL i elems)
     (is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))
     NONE (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) (EL i ltys)
     (type_memory_bytes cenv
       (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))) sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?ff t. write_place cx p (EL i vs) (mid with gas_obs := []) = (INL (),ff) /\
    expr_sim_inv cenv cx env ff /\
    gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv es sp s0 cenv ff t) \/
  (?ff rr. write_place cx p (EL i vs) (mid with gas_obs := []) =
      (INR (Error (RuntimeError "write in static context")),ff) /\
    gas_marked_path F ctx func s 0 rr /\
    expr_exit (INR (Error (RuntimeError "write in static context"))) rr)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec _ _ _ (es,s0) marks _ _ _` >>
  `eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL p,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `target_pre cenv cx env bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `value_has_type (EL i ltvs) (EL i vs)` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (irule tuple_place_destination_value_typed >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `write_place cx p (EL i vs) (mid with gas_obs := [])` >>
  rename1 `write_place _ _ _ _ = (res,ff)` >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) s` by
    fs[loweringPostsTheory.target_post_def] >>
  Q.SUBGOAL_THEN
   `res = INL () \/
   (?is_t slot value_ty. p = StoragePlace is_t slot value_ty /\
     cx.txn.is_static /\
     res = INR (Error (RuntimeError "write in static context")) /\
     ff = mid with gas_obs := [])` assume_tac
  >- (irule tuple_place_source_write_outcome >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  reverse (qpat_x_assum `res = INL () \/ _`
    (DISJ_CASES_THEN strip_assume_tac))
  >- (disj2_tac >> gvs[] >> suspend "static") >>
  disj1_tac >> gvs[] >>
  `expr_sim_inv cenv cx env ff` by
    (irule tuple_place_source_write_endpoint >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule tuple_place_target_base_inversion >> strip_tac >>
  `tuple_place_head ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    lo sp tys ltys ltvs vs elems w i s0` by simp[] >>
  `target_post ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    sp sa s0 (mid with gas_obs := []) (PlaceR p) (Type (EL i tys)) r s` by
    (fs[loweringPostsTheory.target_post_def, loweringPostsTheory.locals_kept_def,
        loweringPostsTheory.popped_kept_def] >> metis_tac[]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
      sp s0 cenv ff t` suffices_by
    (strip_tac >> qexists `t` >> gvs[stmtSimDefsTheory.alloca_frame_gas_obs]) >>
  irule tuple_place_compiler_head_step >>
  qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume tuple_place_marked_head_step[static]:
  markerLib.RESUME_TAC >>
  drule tuple_place_target_base_inversion >> strip_tac >>
  `target_pre cenv cx env bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
  drule_all tuple_place_source_target_endpoint >> strip_tac >>
  `?dw. eval_operand (FST r) s = SOME dw /\
    place_ptr_rel cenv cx s (PlaceR (StoragePlace is_t slot value_ty)) dw
      (FST (SND r)) (Type (EL i tys))` by
    fs[loweringPostsTheory.target_post_def] >>
  `SND (SND r) = SOME (ValPT (EL i tys)) /\
   (!x. FST r = Var x ==> not_fresh_at sa x)` by
    fs[loweringPostsTheory.target_post_def, exprLoweringTheory.value_type_place_def] >>
  `FST (SND r) = SOME (if is_t then LocTransient else LocStorage)` by
    fs[loweringPostsTheory.place_ptr_rel_def, loweringPostsTheory.slot_loc_def] >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_fit >> strip_tac >>
  `tuple_place_head ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    lo sp tys ltys ltvs vs elems w i s0` by simp[] >>
  `target_post ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    sp sa s0 (mid with gas_obs := []) (PlaceR (StoragePlace is_t slot value_ty))
    (Type (EL i tys)) r s` by simp[] >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_value_rel >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `is_word_type (EL i ltys)` >- suspend "static_word" >>
  suspend "static_value"
QED

Resume tuple_place_marked_head_step[static_word]:
  `s.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def, loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `eval_operand (EL i elems) s = SOME (typed_val_to_w256 (EL i ltvs) (EL i vs))` by
    fs[loweringPostsTheory.expr_val_rel_def] >>
  `emit_void (if is_t then TSTORE else SSTORE) [FST r; EL i elems] sa = ((),sb)` by
    (Cases_on `is_t` >> gvs[stmtLoweringTheory.compile_store_at_loc_def]) >>
  drule_all (Q.INST [`tr` |-> `is_t`] storageStoreFrameTheory.storage_emit_static_path) >> strip_tac >>
  qexists `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  simp[exprSimDefsTheory.expr_exit_def]
QED

Resume tuple_place_marked_head_step[static_value]:
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_sizes >> strip_tac >>
  `i < LENGTH ltys` by simp[] >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_pointer_element_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) (EL i tys) /\
   0 < type_slot_size (EL i tvs)` by metis_tac[] >>
  `type_alloc_ok cenv (EL i tys)` by
    (irule tuplePlaceBoundsTheory.tuple_place_element_alloc_ok >> metis_tac[]) >>
  `tuple_place_snapshot cenv cx (mid with gas_obs := []) lo sa.cs_next_id
    tys ltys ltvs w s` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_snapshot >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `LENGTH ltvs = LENGTH ltys /\
   stmt_state_rel ctx func cenv cx (mid with gas_obs := []) s` by simp[] >>
  `w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
    type_memory_size (EL i ltvs) < dimword (:256)` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >> simp[]) >>
  `?sw. eval_operand (EL i elems) s = SOME sw /\
    w2n sw = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (drule (Q.INST [`j` |-> `i`]
       tuplePlacePointerReadyTheory.tuple_place_head_pointer_operands) >> simp[] >> metis_tac[]) >>
  `EL i tys <> EL i ltys ==>
    w2n sw + type_memory_size (EL i ltvs) <= s.vs_alloca_next /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
      w2n sw + type_memory_size (EL i ltvs) <= b \/ b + sz <= w2n sw)` by
    (strip_tac >>
     drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >>
     strip_tac >> gvs[] >>
     `alloca_inv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def,
        venomMemDefsTheory.allocas_non_overlapping_def] >>
     conj_tac >- (res_tac >> decide_tac) >>
     map_every qx_gen_tac [`other_aid`, `other_base`, `other_size`] >>
     strip_tac >>
     `aid <> other_aid` by decide_tac >>
     res_tac >> decide_tac) >>
  `compile_assign_value cenv (FST r) (if is_t then LocTransient else LocStorage)
     (EL i elems) (is_word_type (EL i tys)) NONE (EL i tys) (EL i ltys)
     (type_memory_bytes cenv (EL i tys)) sa = ((),sb)` by gvs[] >>
  irule placeStoreStaticExitTheory.place_store_value_static_exit >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `is_t` >> gvs[] >> metis_tac[]
QED

Finalise tuple_place_marked_head_step

Theorem tuple_place_write_gas_exit:
  write_place cx p v es = (INR ex,ff) /\
  gas_marked_path F ctx func s 0 r /\ exit_result r /\
  expr_exit (INR ex) r ==>
  gas_outcome F tops (ctx,func) (ignore_bind (write_place cx p v) next)
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl [`INR ex`,`ff`,`r`] >>
  simp[gas_marked_exec_def] >> rpt strip_tac >>
  drule tuple_place_write_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `r` >> Cases_on `ex` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def]
QED

Theorem tuple_place_write_gas_prefix:
  write_place cx p v es = (INL (),ff) /\
  gas_marked_path F ctx func s 0 (OK t) /\
  gas_outcome F tops (ctx,func) next (ff with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) (ignore_bind (write_place cx p v) next)
    (es,s) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (write_place cx p v)
    (es,s) [] (INL ()) ff (OK t)` by
    (simp[gas_marked_exec_def] >> rpt strip_tac >>
     drule tuple_place_write_gas_obs >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists `[] ++ right` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl [`out`,`fin`,`r`] >>
      conj_tac >- (rewrite_tac[ignore_bind_def] >>
                    irule gas_marked_exec_bind_normal >>
                    qexistsl [`ff`,`t`,`()`] >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err,ef) (callee,tf)` >>
  qexists `[] ++ right` >> disj2_tac >> qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_bind_unit >>
  qexistsl [`ff`,`t`,`()`] >> simp[GSYM ignore_bind_def]
QED

Theorem tuple_place_head_gas_continuation:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ EVERY (supported_expr tops) (target_indices bt) /\
  target_sim ctx func cenv cx env bt es /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\ ~immutable_root cx bt /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  (!ff t. expr_sim_inv cenv cx env ff /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) ==>
    gas_outcome F (cx_tops cx) (ctx,func) next (ff with gas_obs := [],t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt)
      (\p. ignore_bind (write_place cx p (EL i vs)) next)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[targetPlaceSimTheory.target_pre_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule tuple_place_target_gas_admissible >>
     metis_tac[targetPlaceSimTheory.target_pre_def]) >>
  `type_place_target env bt = SOME (Type (EL i tys))` by
    fs[vyperTypeSystemTheory.well_typed_target_def] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
    (\res ee t. ?p. res = INL p /\
      target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r t /\
      t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (irule target_place_sim >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  irule tuple_place_gas_outcome_bind_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >>
    gvs[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def] >> drule gas_marked_path_exec >>
     strip_tac >> metis_tac[gas_path_normal]) >>
  drule_all (SRULE [LET_THM] tuple_place_marked_head_step) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (irule tuple_place_write_gas_prefix >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      first_x_assum irule >> simp[] >>
      qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[loweringPostsTheory.target_post_def] >> strip_tac >>
      rpt strip_tac >>
      `not_fresh_at sa x` by
        (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  rename1 `expr_exit (INR (Error (RuntimeError "write in static context"))) rr` >>
  `exit_result rr` by
    (Cases_on `rr` >>
     gvs[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]) >>
  irule tuple_place_write_gas_exit >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
