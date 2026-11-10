Theory exprSimPopNestedLocalPost
Ancestors
  exprSimPopNestedLocalPtrs exprSimPopNestedLocalSource exprSimPopNestedLocalMemory
  exprSimAttributeFields exprBopSimProps exprSimProps loweringPosts
  localPtrsProps compileEnv loweringStateRelDefs valueEncodingProps venomState
  finite_map arithmetic exprSimPop exprSimAggregateLayout
  vyperPlaceStatePreservation vyperTyping valueEncoding valueEncodingDefs
  vyperState vyperTypeInvariants list rich_list stmtSimAssignStore
  loweringSlice exprLoweringProps

(* One nested header write is precisely an allowed locals_kept change. *)
Theorem pop_path_locals_kept:
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id locbase sz /\ k + 32 <= sz /\
  dynarray_len_at cenv id k /\
  u.vs_memory = (mstore (locbase + k) w s).vs_memory ==>
  locals_kept cenv es s u
Proof
  strip_tac >> simp[locals_kept_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >>
  Cases_on `n = id`
  >- (`b = locbase` by gvs[local_region_def] >> gvs[] >>
      first_x_assum drule >> simp[]) >>
  `regions_disjoint locbase sz b sz'` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Theorem pop_path_wb_frame:
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id locbase sz /\ k + 32 <= sz /\
  dynarray_len_at cenv id k /\
  u.vs_memory = (mstore (locbase + k) w s).vs_memory /\
  u.vs_allocas = s.vs_allocas /\
  (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
         lookup_var x u = SOME v) ==>
  wb_frame cenv es sa s u
Proof
  strip_tac >>
  `locals_kept cenv es s u` by (drule_all pop_path_locals_kept >> simp[]) >>
  simp[wb_frame_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >>
  qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule_all >>
  strip_tac >> decide_tac
QED

(* A memory value in a live local's region, including a recorded popped
   element, supplies both value and location parts of the post. *)
Theorem local_memory_vv_post:
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' u /\
  wb_frame cenv es sa s0 u /\
  read_result cx result es' = (INL v,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) u.vs_memory /\
  eval_operand op u = SOME w /\
  local_region cenv es'.scopes u id locbase sz /\
  locbase <= w2n w /\ w2n w + val_footprint tv v <= locbase + sz /\
  local_val_at cenv cx id (w2n w - locbase) tv v ==>
  vv_post ctx func cenv cx e es sa sb s0 es' result
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u
Proof
  strip_tac >> simp[vv_post_def] >>
  qpat_assum `post_value_type _ _ = _` (fn th => simp[th]) >>
  conj_tac
  >- (simp[vv_holds_def, contextTheory.mk_ptr_def] >>
      strip_tac >> drule_all val_in_memory_word_type >> simp[]) >>
  conj_tac
  >- (simp[vv_at_def, contextTheory.mk_ptr_def] >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`id`, `locbase`, `sz`] >> simp[]) >>
  conj_tac >- simp[contextTheory.mk_ptr_def] >>
  gvs[wb_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem pop_path_result_bounds:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  val_in_memory tv a locbase s.vs_memory /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  type_memory_size tv <= sz ==>
  value_has_type etv (LAST vs) /\ val_wf etv (LAST vs) /\
  k + 32 + (LENGTH vs - 1) * type_memory_size etv +
    val_footprint etv (LAST vs) <= sz
Proof
  strip_tac >> drule_all val_in_memory_mutable_path >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule_all evaluate_subscripts_type >> simp[]) >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `value_has_type etv (LAST vs)` by
    (gvs[value_has_type_def, all_have_type_EVERY, EVERY_EL,
         LAST_EL, PRE_SUB1]) >>
  `val_wf etv (LAST vs)` by
    (gvs[val_wf_def] >> drule elems_val_wf_EL >>
     disch_then (qspec_then `LENGTH vs - 1` mp_tac) >>
     simp[LAST_EL, PRE_SUB1]) >>
  simp[] >>
  `32 + (LENGTH vs - 1) * type_memory_size etv +
     val_footprint etv (LAST vs) <= 32 + n * type_memory_size etv` by
    (`val_footprint etv (LAST vs) <= type_memory_size etv` by
       metis_tac[val_footprint_le] >>
     `LENGTH vs <= n` by gvs[value_has_type_def] >>
     `LENGTH vs * type_memory_size etv <= n * type_memory_size etv` by simp[] >>
     `(LENGTH vs - 1) * type_memory_size etv + type_memory_size etv =
       LENGTH vs * type_memory_size etv` by
       (Cases_on `LENGTH vs` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  gvs[type_memory_size_def] >> decide_tac
QED

(* Reuse the general local-store immutable frame and the existing state
   relation scope wrapper; no field-by-field state relation expansion. *)
Theorem pop_path_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM scopes' /\
  local_ptrs_rel func cenv scopes' u /\
  local_region cenv es.scopes s id locbase sz /\ k + 32 <= sz /\
  u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|> /\
  u.vs_memory = (mstore (locbase + k) w s).vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx (es with scopes := scopes') u
Proof
  strip_tac >>
  `u.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `u = _ with <|vs_vars := _; vs_memory := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore (locbase + k) w s)` by
    (drule_all local_mstore_immutables_at >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u` by
    (irule immutables_rel_mem_agree >>
     qexists_tac `mstore (locbase + k) w s` >> simp[mstore_def]) >>
  `immutable_base_zero cenv u` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`immutable_base_zero cenv s`] >- gvs[stmt_state_rel_def]
     >~ [`u.vs_labels = s.vs_labels`]
     >- (qpat_x_assum `u = _ with <|vs_vars := _; vs_memory := _|>`
           (fn th => once_rewrite_tac[th]) >> simp[]) >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule pop_stmt_state_rel_scopes >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `id'` >>
      `local_ptrs_rel func cenv es.scopes s` by
        gvs[stmt_state_rel_def, state_rel_def] >>
      irule local_region_frame >> conj_tac
      >- (qexists_tac `func` >> simp[]) >>
      qexistsl_tac [`sa`, `scopes'`, `u`] >> simp[]) >>
  gvs[]
QED

(* The removed element remains a statically identified part of the local,
   even though its live array has just become shorter. *)
Theorem local_path_at_dynamic_element:
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\ i < n ==>
  local_path_at cenv cx id (k + 32 + i * type_memory_size etv) etv
Proof
  strip_tac >>
  `mem_step_offset (ArrayTV etv (Dynamic n)) (ValueSubscript (IntV (&i))) =
    SOME (32 + i * type_memory_size etv,etv)` by simp[mem_step_offset_def] >>
  drule_all local_path_at_step >> pure_rewrite_tac[ADD_ASSOC] >> simp[]
QED

(* Post assembly uses only the live root encoding before the store.  The
   source transition supplies read_result, including its history fallback. *)
Theorem pop_path_vv_post:
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' u /\ wb_frame cenv es sa s0 u /\
  read_result cx result es' = (INL (LAST vs),es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  val_in_memory tv a locbase s.vs_memory /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  type_memory_size tv <= sz /\
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\
  local_region cenv es'.scopes u id locbase sz /\
  u.vs_memory = (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
  eval_operand op u = SOME w /\
  w2n w = locbase + k + 32 + (LENGTH vs - 1) * type_memory_size etv ==>
  vv_post ctx func cenv cx e es sa sb s0 es' result
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u
Proof
  strip_tac >>
  `value_has_type etv (LAST vs) /\ val_wf etv (LAST vs) /\
   k + 32 + (LENGTH vs - 1) * type_memory_size etv +
     val_footprint etv (LAST vs) <= sz` by
    (drule_all pop_path_result_bounds >> simp[]) >>
  `val_in_memory etv (LAST vs) (w2n w) u.vs_memory` by
    (drule_all pop_path_elem_in_memory >> simp[]) >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule mem_path_offset_sound >> strip_tac >>
     drule_all evaluate_subscripts_type >> simp[]) >>
  `LENGTH vs - 1 < n` by
    (gvs[value_has_type_def] >> Cases_on `vs` >> gvs[]) >>
  `local_val_at cenv cx id (w2n w - locbase) etv (LAST vs)` by
    (simp[local_val_at_def] >> disj1_tac >>
     drule_all local_path_at_dynamic_element >>
     pure_rewrite_tac[ADD_ASSOC] >> simp[]) >>
  irule local_memory_vv_post >> simp[] >>
  qexistsl_tac [`id`, `locbase`, `sz`] >> gvs[] >> decide_tac
QED
