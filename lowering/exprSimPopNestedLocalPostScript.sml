Theory exprSimPopNestedLocalPost
Ancestors
  exprSimPopNestedLocalPtrs exprSimPopNestedLocalSource exprSimPopNestedLocalMemory
  exprSimAttributeFields exprBopSimProps exprSimProps loweringPosts
  localPtrsProps compileEnv loweringStateRelDefs valueEncodingProps venomState
  finite_map arithmetic exprSimPop exprSimAggregateLayout
  vyperPlaceStatePreservation vyperTyping valueEncoding valueEncodingDefs
  vyperState vyperTypeInvariants list rich_list stmtSimAssignStore
  loweringSlice exprLoweringProps

(* A nested pop's header write, with its snapshot recorded in the local's
   history, is a frame step (locals_kept_live_pop). *)
Theorem pop_path_wb_frame:
  !func cenv es es' s u id locbase sz k w sa entry updated hnew path arr etv n.
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id locbase sz /\ k + 32 <= sz /\
  dynarray_len_at cenv id k /\
  u.vs_memory = (mstore (locbase + k) w s).vs_memory /\
  u.vs_allocas = s.vs_allocas /\
  (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
         lookup_var x u = SOME v) /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\
  lookup_scopes id es.scopes = SOME entry /\
  lookup_scopes id es'.scopes =
    SOME (entry with <|value := updated; popped := hnew :: entry.popped|>) /\
  (!j. j <> id ==> lookup_scopes j es'.scopes = lookup_scopes j es.scopes) /\
  snapshot_in entry.type locbase sz hnew u.vs_memory /\
  EVERY (\q. ?err. evaluate_subscripts entry.type entry.value q = INR err)
    (MAP FST entry.popped) /\
  evaluate_subscripts entry.type entry.value path = INL arr /\
  mem_path_offset entry.type path = SOME (k, ArrayTV etv (Dynamic n)) ==>
  wb_frame cenv es es' sa s u
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`func`, `cenv`, `es`, `es'`, `s`, `u`, `id`, `locbase`, `sz`,
               `k`, `w`, `entry`,
               `entry with <|value := updated; popped := hnew :: entry.popped|>`,
               `hnew`, `path`, `arr`, `etv`, `n`] mp_tac locals_kept_live_pop >>
  impl_tac >- fs[] >> strip_tac >>
  simp[wb_frame_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >>
  qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule_all >>
  strip_tac >> decide_tac
QED

(* A memory value in a live local's region, including a recorded popped
   element, supplies both value and location parts of the post. *)
Theorem local_memory_vv_post:
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' u /\
  wb_frame cenv es es' sa s0 u /\
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
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[contextTheory.mk_ptr_def]
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

(* The popped element stays in place past the new length: the snapshot a
   nested pop records sits in memory after the header write. *)
Theorem pop_path_snapshot_in:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  val_in_memory tv a locbase s.vs_memory /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  type_memory_size tv <= sz ==>
  snapshot_in tv locbase sz
    (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
    (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  strip_tac >>
  drule_all pop_path_result_bounds >> strip_tac >>
  drule_all pop_path_elem_in_memory >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule mem_path_offset_sound >> strip_tac >>
     drule_all evaluate_subscripts_type >> simp[]) >>
  `LENGTH vs - 1 < n` by
    (gvs[value_has_type_def] >> Cases_on `vs` >> gvs[]) >>
  `mem_path_offset tv (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
     SOME (k + (32 + (LENGTH vs - 1) * type_memory_size etv), etv)` by
    (irule mem_path_offset_snoc >> simp[mem_step_offset_def]) >>
  `k + (32 + (LENGTH vs - 1) * type_memory_size etv) + type_memory_size etv <=
     type_memory_size tv` by metis_tac[mem_path_offset_sound] >>
  `locbase + (k + (32 + (LENGTH vs - 1) * type_memory_size etv)) =
   locbase + k + 32 + (LENGTH vs - 1) * type_memory_size etv` by decide_tac >>
  rw[snapshot_in_def] >>
  `k + locbase = locbase + k` by decide_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  `k + (locbase + (type_memory_size etv * (LENGTH vs - 1) + 32)) =
     locbase + k + 32 + (LENGTH vs - 1) * type_memory_size etv` by decide_tac >>
  pop_assum (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC
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
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' u /\ wb_frame cenv es es' sa s0 u /\
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
