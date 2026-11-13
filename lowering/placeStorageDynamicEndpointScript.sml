(* A single counted endpoint for a normalized dynamic storage buffer. *)
Theory placeStorageDynamicEndpoint
Ancestors
  placeStorageDynamicExecution placeStorageDynamicAgreement placeStorageBufferBounds
  placeStorageFinalHistory stmtSimAssignStorageCopy placeStorageElementPaths
  stmtSimStoreCopy bodyMemAssignTopCopyPaths arithmetic words list rich_list

Theorem dynamic_storage_prefix_flat[local]:
  !n a.
    a.vs_memory = s.vs_memory ==>
    store_copy_prefix (if tr then LocTransient else LocStorage)
      (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a (n) =
    FOLDL (\t i. (if tr then tstore else sstore) (d+n2w i)
      (if i = 0 then v else mload (w2n (p+n2w (32*i))) s) t)
      a (MAP (\i. 1+j*ew+i) (COUNT_LIST (n)))
Proof
  Induct >> rpt strip_tac
  >- simp[store_copy_prefix_def, COUNT_LIST_def] >>
  simp_tac std_ss [topcopy_prefix_suc, COUNT_LIST_SNOC, MAP_SNOC, FOLDL_SNOC] >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  `d+n2w (1+j*ew)+n2w n = d+n2w (1+j*ew+n)` by
    simp_tac std_ss [GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
  `32+j*(32*ew)+n*32 = 32*(1+j*ew+n)` by
    (simp_tac std_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_ASSOC] >>
     metis_tac[MULT_COMM, MULT_ASSOC]) >>
  `p+n2w (32+j*(32*ew))+n2w n*32w =
   p+n2w (32*(1+j*ew+n))` by
    (pure_rewrite_tac [wordsTheory.WORD_ADD_ASSOC,
       GSYM wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w] >>
     simp_tac std_ss [wordsTheory.WORD_LEFT_ADD_DISTRIB,
       wordsTheory.WORD_RIGHT_ADD_DISTRIB, wordsTheory.WORD_MULT_ASSOC,
       wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_MULT_CLAUSES] >>
     metis_tac[wordsTheory.WORD_MULT_COMM, wordsTheory.WORD_MULT_ASSOC]) >>
  `1+j*ew+n <> 0` by decide_tac >>
  pure_asm_rewrite_tac [venomStateTheory.mload_def] >>
  Cases_on `tr` >> simp[]
QED

Theorem dynamic_storage_elements_flat[local]:
  !js a. a.vs_memory = s.vs_memory ==>
    FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
      (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a ew) a js =
    FOLDL (\t i. (if tr then tstore else sstore) (d+n2w i)
      (if i = 0 then v else mload (w2n (p+n2w (32*i))) s) t)
      a (FLAT (MAP (\j. MAP (\i. 1+j*ew+i) (COUNT_LIST ew)) js))
Proof
  Induct >> rpt strip_tac >- simp[] >>
  simp_tac std_ss [FOLDL, MAP, FLAT, FOLDL_APPEND] >>
  first_x_assum (qspec_then `store_copy_prefix
    (if tr then LocTransient else LocStorage)
    (p+n2w (32+h*(32*ew))) (d+n2w (1+h*ew)) a ew` mp_tac) >>
  asm_simp_tac (srw_ss()) [topcopy_prefix_memory] >>
  disch_then SUBST1_TAC >>
  AP_THM_TAC >> AP_TERM_TAC >>
  irule dynamic_storage_prefix_flat >> simp[]
QED

Theorem dynamic_storage_fold_flat[local]:
  (if tr then tstore d v else sstore d v)
    (FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
      (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a ew) s js) =
  FOLDL (\t i. (if tr then tstore else sstore) (d+n2w i)
    (if i = 0 then v else mload (w2n (p+n2w (32*i))) s) t) s
    (FLAT (MAP (\j. MAP (\i. 1+j*ew+i) (COUNT_LIST ew)) js) ++ [0])
Proof
  simp_tac std_ss [FOLDL_APPEND, FOLDL] >>
  `FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
      (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a ew) s js =
   FOLDL (\t i. (if tr then tstore else sstore) (d+n2w i)
    (if i = 0 then v else mload (w2n (p+n2w (32*i))) s) t) s
    (FLAT (MAP (\j. MAP (\i. 1+j*ew+i) (COUNT_LIST ew)) js))` by
    (irule dynamic_storage_elements_flat >> simp[]) >>
  Cases_on `tr` >> simp[wordsTheory.WORD_ADD_0]
QED

Theorem dynamic_storage_fold_state[local]:
  stmt_state_rel ctx fn ce cx es s /\
  h = (if tr then tstore d v else sstore d v)
    (FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
      (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a ew) s js) /\
  storage_agree (storage_dead cx tr stor) stor
    ((if tr then contract_transient else contract_storage) h) ==>
  stmt_state_rel ctx fn ce cx (set_storage cx es tr stor) h
Proof
  strip_tac >> gvs[dynamic_storage_fold_flat] >>
  ho_match_mp_tac storage_copy_state_fold >> simp[] >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  Cases_on `tr` >>
  simp[storage_copy_backend_fold, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem dynamic_storage_subregion_state[local]:
  stmt_state_rel ctx fn ce cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n d = w2n k+delta /\
  w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n p) s.vs_memory /\
  w2n p+32*(1+LENGTH vs*type_slot_size tv) <= dimword(:256) ==>
  stmt_state_rel ctx fn ce cx
    (set_storage cx es tr (apply_writes d writes (get_storage cx es tr)))
    ((if tr then tstore d (n2w (LENGTH vs)) else sstore d (n2w (LENGTH vs)))
      (FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
        (p+n2w (32+j*(32*type_slot_size tv)))
        (d+n2w (1+j*type_slot_size tv)) a (type_slot_size tv)) s (COUNT_LIST (LENGTH vs))))
Proof
  strip_tac >>
  irule dynamic_storage_fold_state >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`d`, `type_slot_size tv`, `COUNT_LIST (LENGTH vs)`,
                    `p`, `s`, `n2w (LENGTH vs)`] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `FOLDL ff s js` >>
  `((if tr then contract_transient else contract_storage)
      ((if tr then tstore d (n2w (LENGTH vs)) else sstore d (n2w (LENGTH vs)))
        (FOLDL ff s js))) =
    update_storage d (n2w (LENGTH vs))
      ((if tr then contract_transient else contract_storage) (FOLDL ff s js))` by
    (Cases_on `tr` >> simp[venomStateTheory.sstore_def, venomStateTheory.tstore_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]) >>
  pure_asm_rewrite_tac [] >>
  unabbrev_all_tac >>
  drule storage_copy_initial_agree >>
  disch_then (qspec_then `tr` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_at (Pos hd) storage_dynamic_subregion_backend_agree >>
  simp[] >> disch_then assume_tac >>
  Cases_on `tr` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cap`, `path`] >> simp[]
QED

Theorem dynamic_storage_normalized_endpoint_fields:
  compile_dynarray_to_storage src dst ((type_memory_bytes ce et+31) DIV 32)
    (type_memory_bytes ce et) tr sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s /\ alloca_history fn s /\
  evaluate_type tenv (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  type_memory_bytes ce et = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n p) s.vs_memory /\
  w2n p + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword(:256) /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n d = w2n k+delta /\ w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      stmt_state_rel ctx fn ce cx
        (set_storage cx es tr (apply_writes d writes (get_storage cx es tr))) t /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all dynamic_storage_buffer_bounds >> strip_tac >>
  drule_at (Pos hd) dyn_storage_path_nonempty_bound >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`LENGTH vs`, `fn`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- metis_tac[] >>
    qpat_x_assum `!j. j < LENGTH vs ==> _` mp_tac >> simp[])) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `!a. (if a = 1 then 32 else 32*a) = 32*a` by (gen_tac >> Cases_on `a = 1` >> simp[]) >>
  gvs[] >> qexists_tac `t` >> simp[] >>
  suspend "semantic"
QED

Resume dynamic_storage_normalized_endpoint_fields[semantic]:
  `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `LENGTH vs <= cap` by fs[Once vyperTypingTheory.value_has_type_def] >>
  `LENGTH vs * type_slot_size tv <= cap * type_slot_size tv` by simp[] >>
  `w2n p+32*(1+LENGTH vs*type_slot_size tv) <= dimword(:256)` by
    (qpat_x_assum `type_memory_size (ArrayTV _ _) + _ <= _` mp_tac >>
     simp_tac std_ss [valueEncodingTheory.type_memory_size_def,
       valueEncodingPropsTheory.type_memory_size_slots,
       LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_ASSOC] >> decide_tac) >>
  `stmt_state_rel ctx fn ce cx
    (set_storage cx es tr (apply_writes d writes (get_storage cx es tr)))
    (store_copy_normalize s t)` by
    (asm_rewrite_tac [] >>
     pure_rewrite_tac [valueEncodingPropsTheory.type_memory_size_slots] >>
     mp_tac dynamic_storage_subregion_state >> simp[] >> disch_then irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule storage_copy_normalized_state >>
      qexistsl_tac [`s`, `sa`] >>
      simp_tac std_ss [GSYM stmtSimStoreCopyTheory.store_copy_normalize_def] >>
      metis_tac[]) >>
  suspend "history"
QED

Resume dynamic_storage_normalized_endpoint_fields[history]:
  conj_tac
  >- (drule_at (Pos hd) dyn_storage_normalized_history >> simp[] >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `store_copy_normalize s t = h` >>
  `h.vs_alloca_next = s.vs_alloca_next /\ h.vs_memory = s.vs_memory /\
   h.vs_labels = s.vs_labels /\ h.vs_allocas = s.vs_allocas` by
    (qabbrev_tac `H = \i. FOLDL (\a j. store_copy_prefix
       (if tr then LocTransient else LocStorage)
       (p+n2w (32+j*type_memory_size tv))
       (d+n2w (1+j*type_slot_size tv)) a (type_slot_size tv)) s (COUNT_LIST i)` >>
     `!j. (H j).vs_memory = s.vs_memory /\
          (H j).vs_allocas = s.vs_allocas /\
          (H j).vs_alloca_next = s.vs_alloca_next /\
          (H j).vs_call_ctx = s.vs_call_ctx /\
          (H j).vs_labels = s.vs_labels` by
       (irule storage_element_fold_fields >> simp[Abbr `H`] >>
        qexistsl_tac [`d`, `type_slot_size tv`,
          `if tr then LocTransient else LocStorage`, `p`, `type_memory_size tv`] >>
        simp_tac std_ss [MULT_COMM]) >>
     qpat_x_assum `!j. (H j).vs_memory = _ /\ _`
       (qspec_then `LENGTH vs` mp_tac) >>
     Cases_on `tr` >> simp[Abbr `h`, Abbr `H`, venomStateTheory.sstore_def,
       venomStateTheory.tstore_def]) >>
  qpat_x_assum `store_copy_normalize s t = h` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM
    `(\a. (a.vs_alloca_next,a.vs_memory,a.vs_labels,a.vs_allocas))`) >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def]
QED
Finalise dynamic_storage_normalized_endpoint_fields

(* Preserve the original public interface as a projection of the same endpoint. *)
Theorem dynamic_storage_normalized_endpoint:
  compile_dynarray_to_storage src dst ((type_memory_bytes ce et+31) DIV 32)
    (type_memory_bytes ce et) tr sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s /\ alloca_history fn s /\
  evaluate_type tenv (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  type_memory_bytes ce et = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n p) s.vs_memory /\
  w2n p + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword(:256) /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n d = w2n k+delta /\ w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      stmt_state_rel ctx fn ce cx
        (set_storage cx es tr (apply_writes d writes (get_storage cx es tr))) t /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dynamic_storage_normalized_endpoint_fields >>
  strip_tac >> qexists_tac `t` >> simp[]
QED
