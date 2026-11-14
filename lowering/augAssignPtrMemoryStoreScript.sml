Theory augAssignPtrMemoryStore
Ancestors
  bodySimAugPlaceStore augAssignPtrFieldStore augAssignPtrStore
  valueEncodingProofs robustCopyTransportPtr bodyPtrDefs
  augAssignPtrFieldStorePost exprSimProps localPtrsProps
  stmtSimAssignStore vyperLookup finite_map list compileEnv loweringStateRelDefs
  bodySimAugPlaceLoad vyperState vyperValueOperation loweringPosts
  exprSimDefs exprSimHypsDefs vyperTypeInvariants stmtSimDeclStore exprSimBuffer
  exprLoweringProps exprSimSource

Theorem aug_place_path_mstore_robust:
  mem_path_offset tv path = SOME (k,ptv) /\
  well_formed_type_value tv /\ value_has_type tv a /\ val_wf tv a /\
  evaluate_subscripts tv a path = INL old /\
  assign_subscripts tv a path (Replace v) = INL a' /\
  store_lays_out etv ptv v /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory tv a locbase m) ==>
  !m. mem_agree_outside
    (dirty DIFF {i | locbase+k <= i /\ i < locbase+k+32})
    (mstore (locbase+k) (typed_val_to_w256 etv v) s).vs_memory m ==>
    val_in_memory tv a' locbase m
Proof
  rpt strip_tac >> drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `val_in_memory tv a locbase u` by metis_tac[] >>
  `val_wf tv a' /\ val_in_memory tv a' locbase
    (mstore (locbase+k) (typed_val_to_w256 etv v)
      (s with vs_memory := u)).vs_memory` by
    (irule aug_place_path_mstore >> simp[] >> metis_tac[]) >>
  irule (cj 1 val_in_memory_mem_agree_proof) >>
  goal_assum (drule_at Any) >> simp[] >>
  drule memory_byte_agree_window >> strip_tac >>
  qexists_tac `(mstore (locbase+k) (typed_val_to_w256 etv v)
      (s with vs_memory := u)).vs_memory` >> simp[]
QED

Theorem ghost_local_path_word_store:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  assign_subscripts entry.type entry.value path (Replace v) = INL updated /\
  store_lays_out etv ptv v /\ k+32 <= sz /\
  lookup_scopes name scopes' = SOME (entry with <|value := updated; popped := []|>) /\
  (!n. n <> name ==> lookup_scopes n scopes' = lookup_scopes n es.scopes) ==>
  !n e q sq.
    lookup_scopes n scopes' = SOME e /\
    FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
    ptr_covers G tn q s sq /\
    !b mem. lookup_var q s = SOME b /\
      mem_agree_outside
        (tn.t_mem DIFF {i | w2n a+k <= i /\ i < w2n a+k+32})
        (mstore (w2n a+k) (typed_val_to_w256 etv v) s).vs_memory mem ==>
      val_in_memory e.type e.value (w2n b) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `n = name`
  >- (gvs[] >> conj_tac
      >- (fs[ghost_inv_def] >> metis_tac[]) >>
      rpt strip_tac >> gvs[] >> irule aug_place_path_mstore_robust >>
      simp[] >>
      qexistsl_tac [`entry.value`, `tn.t_mem`, `etv`, `k`, `old`, `path`, `ptv`, `s`, `v`] >>
      simp[] >> reverse conj_tac >- (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      fs[ghost_inv_def] >> metis_tac[]) >>
  `lookup_scopes n es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt strip_tac >> irule mstore_robust_exterior >>
  conj_tac >- (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  qexistsl_tac [`w2n a+k`, `s`, `tn.t_mem`, `typed_val_to_w256 etv v`] >>
  simp[] >> conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  `name <> n /\ w2n a <= w2n a+k /\ (w2n a+k)+32 <= w2n a+sz` by
    (simp[] >> decide_tac) >>
  drule_all local_contained_word_store_exterior >> simp[]
QED

Theorem ghost_inv_write_local_path_word:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  find_containing_scope name es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ lookup_var dst s = SOME da /\
  w2n da = w2n a+k /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  assign_subscripts entry.type entry.value path (Replace v) = INL updated /\
  store_lays_out etv ptv v /\ k+32 <= sz /\
  eval_operand value s = SOME (typed_val_to_w256 etv v) /\ op_taint tn value = {} ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++ (env |+ (name,entry with
      <|value := updated; popped := []|>)) :: rest)
    G (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n da) (typed_val_to_w256 etv v) s) tn)
    ((mstore (w2n da) (typed_val_to_w256 etv v) s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  irule ghost_inv_mstore_transport >> simp[] >>
  conj_tac
  >- (`k+w2n a = w2n a+k` by decide_tac >>
      pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
      MATCH_MP_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC] ghost_local_path_word_store) >>
      simp[lookup_scopes_update, lookup_scopes_update_other] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_inv_write_memory_place_word:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace name path)) da
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env es /\ lookup_scopes name es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  write_place cx (MemoryPlace name path) v es = (INL (),fin) /\
  lookup_var dst s = SOME da /\
  eval_operand value s = SOME (typed_val_to_w256 etv v) /\ op_taint tn value = {} ==>
  ghost_inv d cenv cx fin G
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n da) (typed_val_to_w256 etv v) s) tn)
    ((mstore (w2n da) (typed_val_to_w256 etv v) s) with vs_inst_idx := pc)
Proof
  strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `find_containing_scope name es.scopes` >> gvs[return_def, raise_def] >>
  rename1 `find_containing_scope name es.scopes = SOME fc` >> PairCases_on `fc` >>
  `fc2 = entry` by metis_tac[find_containing_scope_lookup, optionTheory.SOME_11] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
      set_scopes_def, replace_memory_entry_def, AllCaseEqs()] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace v)` >>
  gvs[return_def, raise_def] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule aug_place_lookup_typed >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  `local_ptrs_rel fn cenv es.scopes s /\ alloca_room ctx fn s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `type_memory_size entry.type <= sz /\ w2n b+sz <= s.vs_alloca_next` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `k + type_memory_size ptv <= type_memory_size entry.type` by
    metis_tac[mem_path_offset_sound] >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b+n2w k) = w2n b+k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  irule ghost_inv_write_local_path_word >> simp[] >>
  metis_tac[]
QED

Theorem augassign_memory_store_case_ptr:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME da /\ eval_operand value s = SOME (typed_val_to_w256 etv v) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace name path)) da
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env es /\ lookup_scopes name es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv v /\
  write_place cx (MemoryPlace name path) v es = (INL (),fin) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    stmt_state_rel ctx fn cenv cx fin sf /\ ghost_inv d cenv cx fin G tnf sf /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!q. lookup_var q sf = lookup_var q s) /\ tnf.t_var = tn.t_var
Proof
  strip_tac >> drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_inv d cenv cx fin G tnf sf` by
    (drule_all ghost_inv_write_memory_place_word >>
     disch_then (qspecl_then [`LENGTH sb.cs_current_insts`, `sa.cs_next_id`] mp_tac) >>
     gvs[]) >>
  `stmt_state_rel ctx fn cenv cx fin
      (mstore (w2n da) (typed_val_to_w256 etv v) s)` by
    (irule aug_place_memory_write_state_rel >> metis_tac[]) >>
  qexistsl_tac [`tnf`, `sf`] >> simp[] >>
  qpat_x_assum `sf = _` SUBST1_TAC >> metis_tac[stmt_state_rel_inst_idx]
QED
