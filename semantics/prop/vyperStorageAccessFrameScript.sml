(*
 * What expr_accesses says about the running contract's storage at run
 * time: an expression with no risky call (no external call, send, raw_call,
 * create or call-family builtin, in it or in an internal function it
 * reaches) writes storage only inside the declared regions of variables
 * its accesses write, and the transient nonreentrant lock slot.
 *
 * The regions are those of the writes the evaluation made: a finite list
 * ws of declared regions (a variable, or a hashmap leaf at the keys
 * written), never every key of a written hashmap.  A slot outside all of
 * them, and not the lock, holds what it held before.
 *
 * The function premise ties the accesses analysis to the code that runs:
 * an internal call the expression reaches is looked up in mods, and the
 * function the evaluator calls is the one function_accesses reads (or the
 * empty constructor lookup_function synthesizes).
 *
 * TOP-LEVEL:
 *   eval_expr_unwritten_storage
 *)

Theory vyperStorageAccessFrame
Ancestors
  vyperSubscriptOverlap vyperInterpreter vyperState vyperContext
  vyperStorageBackend vyperStorageLayoutSafety
  vyperStoragePlaceRegion vyperEncodeDecode vyperStoragePlaceProvenance
  vyperMisc words list arithmetic option vyperValue
  vyperStatePreservation
  vyperTypeInvariants vyperTypeCallStackSoundness vyperTypeEvalSoundness
  vyperTypeCallGraphSoundness vyperTypeCallGraph relation pred_set alist

(* Why it holds (a reader may ignore this): inside an expression only
   Pop writes storage directly; in a reached internal callee Assign,
   AugAssign, Append and Pop do, each through a StoragePlace resolved from a
   target rooted at TopLevelNameTarget (mid,n), whose accesses_target emits
   WriteAcc (StateRef (mid,n)) (eval_target_place_region in
   vyperStoragePlaceProvenance gives the declared region).  Typed values
   keep encode writes inside the region (encode_writes_bounded,
   storage_subregion_bounds; append_place checks len < capacity).  The lock
   is the only other storage write (lock_if_nr/unlock_if_nr, transient).
   External calls, creates, sends and raw calls are RiskyAcc.  A callee's
   own accesses are in expr_accesses via reached_functions, and the glue
   premise makes the evaluator's callee the function function_accesses
   read; nested callees are reached too (contract_call_edges_function,
   MEM_reachable_nodes_NRC in vyperTypeCallGraphSoundness).  The
   evaluate_read_only induction in vyperReadOnlyEval has the same shape
   (statements, loops and calls included). *)

(* Word-address formulation: no numeric non-wrapping premise is needed. *)
Theorem apply_writes_word_frame:
  !writes (base:bytes32) storage k.
    (!off. MEM off (MAP FST writes) ==> k <> base + n2w off) ==>
    lookup_storage k (apply_writes base writes storage) =
    lookup_storage k storage
Proof
  rpt strip_tac >> rename1 `apply_writes root_slot writes storage` >>
  qspecl_then [`writes`, `w2n root_slot`, `storage`, `w2n (k - root_slot)`]
    mp_tac vyperEncodeDecodeTheory.apply_writes_lookup_miss_num >>
  pure_rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
                   GSYM wordsTheory.WORD_ADD_SUB_ASSOC,
                   wordsTheory.WORD_ADD_SUB2] >>
  metis_tac[]
QED

Theorem typed_write_storage_word_frame:
  value_has_type tv v /\
  write_storage_slot cx b slot tv v st = (res,st') /\
  (tr <> b \/ (!i. i < type_slot_size tv ==> k <> slot + n2w i)) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  simp[write_storage_slot_eq, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `tr = b`
  >- (gvs[get_storage_after_set] >> irule apply_writes_word_frame >>
      rpt strip_tac >>
      drule_all (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
      metis_tac[]) >>
  simp[get_storage_after_set_other]
QED

Theorem storage_subregion_word_exclusion:
  storage_subregion root path delta leaf /\
  (!i. i < type_slot_size root ==> k <> slot + n2w i) ==>
  !i. i < type_slot_size leaf ==> k <> (slot + n2w delta) + n2w i
Proof
  strip_tac >> drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
  strip_tac >> rpt strip_tac >>
  `delta + i < type_slot_size root` by decide_tac >>
  first_x_assum (qspec_then `delta + i` mp_tac) >>
  simp[GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC]
QED

Theorem typed_subregion_write_word_frame:
  storage_subregion root path delta leaf /\ value_has_type leaf v /\
  write_storage_slot cx b (slot + n2w delta) leaf v st = (res,st') /\
  (tr <> b \/ (!i. i < type_slot_size root ==> k <> slot + n2w i)) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  strip_tac >> irule typed_write_storage_word_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[storage_subregion_word_exclusion]
QED

Theorem declared_region_frame_append:
  (!tr k.
    (!mid n subs slot tv i.
       MEM (mid,n,subs) ws1 /\
       declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
       i < type_slot_size tv ==> k <> slot + n2w i) /\
    (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
    lookup_storage k (get_storage cx st1 tr) = lookup_storage k (get_storage cx st0 tr)) /\
  (!tr k.
    (!mid n subs slot tv i.
       MEM (mid,n,subs) ws2 /\
       declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
       i < type_slot_size tv ==> k <> slot + n2w i) /\
    (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
    lookup_storage k (get_storage cx st2 tr) = lookup_storage k (get_storage cx st1 tr)) ==>
  !tr k.
    (!mid n subs slot tv i.
       MEM (mid,n,subs) (ws1 ++ ws2) /\
       declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
       i < type_slot_size tv ==> k <> slot + n2w i) /\
    (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
    lookup_storage k (get_storage cx st2 tr) = lookup_storage k (get_storage cx st0 tr)
Proof
  simp[listTheory.MEM_APPEND] >> rpt strip_tac >>
  `lookup_storage k (get_storage cx st1 tr) =
   lookup_storage k (get_storage cx st0 tr)` by
    (first_x_assum (qspecl_then [`tr`,`k`] irule) >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  `lookup_storage k (get_storage cx st2 tr) =
   lookup_storage k (get_storage cx st1 tr)` by
    (first_x_assum (qspecl_then [`tr`,`k`] irule) >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  simp[]
QED

Theorem storage_pop_word_frame:
  pop_place cx (StoragePlace b slot (ArrayTV tv (Dynamic n))) st = (res,st') /\
  (tr <> b \/ k <> slot) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, write_storage_slot_eq,
       vyperStorageTheory.encode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `tr = b`
  >- (gvs[get_storage_after_set] >> irule apply_writes_word_frame >>
      simp[wordsTheory.WORD_ADD_0]) >>
  simp[get_storage_after_set_other]
QED

Theorem storage_append_word_frame:
  value_has_type tv v /\
  append_place cx (StoragePlace b slot (ArrayTV tv (Dynamic n))) v st = (res,st') /\
  (tr <> b \/
   (!i. i < type_slot_size (ArrayTV tv (Dynamic n)) ==> k <> slot + n2w i)) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  simp[append_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_assum_abbrev_tac `write_storage_slot cx b elem_slot tv v st = (wr,mid)` >>
  `lookup_storage k (get_storage cx mid tr) =
   lookup_storage k (get_storage cx st tr)` by
    (`storage_subregion (ArrayTV tv (Dynamic n))
        [ValueSubscript (IntV (&(w2n (lookup_storage slot (get_storage cx st b)))))]
        (type_slot_size tv * w2n (lookup_storage slot (get_storage cx st b)) + 1) tv`
       by simp[storage_subregion_def] >>
     irule typed_subregion_write_word_frame >>
     goal_assum (drule_at Any) >>
     simp[Abbr `elem_slot`] >> metis_tac[]) >>
  `lookup_storage k (get_storage cx st' tr) =
   lookup_storage k (get_storage cx mid tr)` by
    (qpat_x_assum `lookup_storage k (get_storage cx mid tr) = _` kall_tac >>
     qpat_x_assum `write_storage_slot cx b slot _ _ mid = _` mp_tac >>
     simp[write_storage_slot_eq, vyperStorageTheory.encode_value_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     Cases_on `tr = b`
     >- (gvs[get_storage_after_set] >> irule apply_writes_word_frame >>
         simp[wordsTheory.WORD_ADD_0] >>
         first_x_assum (qspec_then `0` mp_tac) >>
         simp[vyperValueTheory.type_slot_size_def, wordsTheory.WORD_ADD_0]) >>
     simp[get_storage_after_set_other]) >>
  simp[]
QED

Theorem acquire_lock_word_frame:
  acquire_nonreentrant_lock cx.txn.target lock is_view st = (res,st') /\
  (tr ==> k <> n2w lock) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  strip_tac >>
  drule vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_frame >>
  strip_tac >> Cases_on `tr` >>
  gvs[get_storage_def, vfmExecutionTheory.lookup_transient_storage_def]
QED

Theorem release_lock_word_frame:
  release_nonreentrant_lock cx.txn.target lock st = (res,st') /\
  (tr ==> k <> n2w lock) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  simp[vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq] >>
  strip_tac >> gvs[] >> Cases_on `tr` >>
  gvs[get_storage_def, vfmExecutionTheory.update_transient_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
      combinTheory.APPLY_UPDATE_THM]
QED

Theorem lock_if_nr_word_frame:
  lock_if_nr cx nr is_view st = (res,st') /\
  (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >> Cases_on `is_view` >>
  simp[lock_if_nr_def, ignore_bind_def, bind_def, return_def, raise_def,
       check_not_static_def, check_def, assert_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  irule acquire_lock_word_frame >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem unlock_if_nr_word_frame:
  unlock_if_nr cx nr is_view st = (res,st') /\
  (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
  lookup_storage k (get_storage cx st' tr) =
  lookup_storage k (get_storage cx st tr)
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >> Cases_on `is_view` >>
  simp[unlock_if_nr_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  irule release_lock_word_frame >> goal_assum (drule_at Any) >> metis_tac[]
QED

(* Private closed terms: notation only, not logical definitions. *)
val labelled_place = ``\cx A p. case p of
    StoragePlace tr slot leaf =>
      (?mid n keys root tv path delta.
        MEM (WriteAcc (StateRef (mid,n))) A /\
        declared_storage_region cx mid n keys = SOME (tr,root,tv) /\
        storage_subregion tv path delta leaf /\ slot = root + n2w delta)
  | MemoryPlace id path => T
  | ImmutablePlace mid id path => T``;

val labelled_mapping = ``\cx A tr slot vt.
  ?mid n prefix. MEM (WriteAcc (StateRef (mid,n))) A /\
    (!subs leaf_slot leaf_tv.
      resolve_hashmap_leaf (get_tenv cx) slot vt subs = SOME (leaf_slot,leaf_tv) ==>
      declared_storage_region cx mid n (prefix ++ subs) = SOME (tr,leaf_slot,leaf_tv))``;

val labelled_result = ``\cx A pv. case pv of
    PlaceR p => ^labelled_place cx A p
  | HashMapRef tr slot kt vt => ^labelled_mapping cx A tr slot (HashMapT kt vt)
  | Value v => T``;

Theorem declared_labelled_place[local]:
  declared_storage_region cx mid n keys = SOME (tr,slot,tv) /\
  MEM (WriteAcc (StateRef (mid,n))) A ==>
  ^labelled_place cx A (StoragePlace tr slot tv)
Proof
  strip_tac >> simp[] >>
  qexistsl_tac [`mid`,`n`,`keys`,`slot`,`tv`,`[]`,`0`] >>
  simp[storage_subregion_def, WORD_ADD_0]
QED

Theorem lookup_global_labelled_mapping[local]:
  lookup_global cx mid n st = (INL (HashMapRef tr slot kt vt),st') /\
  MEM (WriteAcc (StateRef (mid,n))) A ==>
  ^labelled_mapping cx A tr slot (HashMapT kt vt)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[option_CASE_rator, prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  simp_tac (srw_ss()) [] >>
  qexistsl_tac [`mid`,`n`,`[]`] >> simp[] >> rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [declared_storage_region_def]
QED

Theorem lookup_global_labelled_result[local]:
  lookup_global cx mid n st = (INL pv,st') /\
  MEM (WriteAcc (StateRef (mid,n))) A ==>
  ^labelled_result cx A pv
Proof
  Cases_on `pv` >> simp[]
  >- (rename1 `PlaceR p` >> Cases_on `p` >> simp[] >> strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all declared_labelled_place >> simp[]) >>
  rpt strip_tac >> drule_all lookup_global_labelled_mapping >> simp[]
QED

Theorem extend_storage_labelled_place[local]:
  ^labelled_place cx A (StoragePlace tr slot tv) /\
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  ^labelled_place cx A p
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule extend_storage_place_subregion >> strip_tac >>
  qmatch_assum_rename_tac `storage_subregion tv [sb] step_delta leaf` >>
  gvs[] >>
  qmatch_assum_rename_tac
    `declared_storage_region cx source_mid source_name source_keys =
       SOME (tr,declared_root,declared_tv)` >>
  qmatch_assum_rename_tac `storage_subregion declared_tv base_path base_delta tv` >>
  drule_all storage_subregion_append >> strip_tac >> simp[] >>
  qexistsl_tac [`source_mid`,`source_name`,`source_keys`,`declared_root`,`declared_tv`,
               `base_path ++ [sb]`,`base_delta + step_delta`] >>
  asm_simp_tac bool_ss [GSYM word_add_n2w, WORD_ADD_ASSOC]
QED

Theorem mapping_prefix_step[local]:
  (!subs ls lt.
    resolve_hashmap_leaf (get_tenv cx) slot (HashMapT kt vt) subs = SOME (ls,lt) ==>
    declared_storage_region cx mid n (prefix ++ subs) = SOME (tr,ls,lt)) ==>
  !subs ls lt.
    resolve_hashmap_leaf (get_tenv cx)
      (hashmap_slot slot (encode_hashmap_key kt key)) vt subs = SOME (ls,lt) ==>
    declared_storage_region cx mid n ((prefix ++ [ValueSubscript key]) ++ subs) =
      SOME (tr,ls,lt)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`ValueSubscript key::subs`,`ls`,`lt`] mp_tac) >>
  pure_once_rewrite_tac [resolve_hashmap_leaf_def] >>
  asm_simp_tac bool_ss
    [subscript_to_value_def, option_case_def, APPEND, GSYM APPEND_ASSOC]
QED

Theorem extend_mapping_labelled_result[local]:
  ^labelled_mapping cx A tr slot (HashMapT kt vt) /\
  extend_place cx (HashMapRef tr slot kt vt) sb st = (INL pv,st') ==>
  ^labelled_result cx A pv
Proof
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_type_CASE_rator, option_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  drule mapping_prefix_step >> disch_then (qspec_then `v` assume_tac)
  >- (first_x_assum (qspecl_then
        [`[]`,`hashmap_slot slot (encode_hashmap_key kt v)`,`tv`] mp_tac) >>
      simp[resolve_hashmap_leaf_def] >> strip_tac >>
      drule_all declared_labelled_place >> simp[]) >>
  qexistsl_tac [`mid`,`n`,`prefix ++ [ValueSubscript v]`] >> simp[]
QED

Theorem extend_labelled_result[local]:
  ^labelled_result cx A pv /\
  extend_place cx pv sb st = (INL next,st') ==>
  ^labelled_result cx A next
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >> simp[] >> strip_tac >>
      gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
          AllCaseEqs(), extend_memory_place_def] >>
      metis_tac[SRULE [] extend_storage_labelled_place]) >>
  metis_tac[SRULE [] extend_mapping_labelled_result]
QED

Theorem eval_base_place_labelled_region:
  !bt cx st pv st'.
    eval_base_place cx bt st = (INL pv,st') ==>
    ^labelled_result cx (accesses_target bt) pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >> TRY (PairCases_on `p`) >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), get_scopes_def,
       type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
       accesses_expr_def] >>
  rpt strip_tac >> gvs[] >>
  FIRST [simp[] >> NO_TAC,
         drule lookup_global_labelled_result >>
         disch_then (qspec_then `[ReadAcc (StateRef (p0,p1)); WriteAcc (StateRef (p0,p1))]` mp_tac) >>
         simp[] >> NO_TAC,
         qmatch_assum_rename_tac `eval_base_place cx child st = (INL child_pv,child_st)` >>
         qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
         simp[vyperASTTheory.expr_size_def] >> strip_tac >>
         first_x_assum drule >> strip_tac >>
         drule_at Any (SRULE [] extend_labelled_result) >>
         disch_then drule >> strip_tac >>
         Cases_on `pv` >> gvs[] >>
         TRY (rename1 `PlaceR p` >> Cases_on `p` >> gvs[]) >>
         metis_tac[]]
QED

Theorem eval_target_place_labelled_region:
  eval_target_place cx bt st = (INL (StoragePlace tr slot leaf),st') ==>
  ?mid n keys root tv path delta.
    MEM (WriteAcc (StateRef (mid,n))) (accesses_target bt) /\
    declared_storage_region cx mid n keys = SOME (tr,root,tv) /\
    storage_subregion tv path delta leaf /\ slot = root + n2w delta
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule eval_base_place_labelled_region >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >> metis_tac[]
QED

(* Callee-local variables are hidden, but state writes and risk survive. *)
Theorem callee_accesses_write:
  !xs. MEM (WriteAcc (StateRef ns)) (callee_accesses xs) <=>
       MEM (WriteAcc (StateRef ns)) xs
Proof
  recInduct callee_accesses_ind >> simp[callee_accesses_def]
QED

Theorem callee_accesses_risky:
  !xs. MEM RiskyAcc (callee_accesses xs) <=> MEM RiskyAcc xs
Proof
  recInduct callee_accesses_ind >> simp[callee_accesses_def]
QED

Theorem reached_function_accesses:
  !src fn mods e ts dflts body a.
  MEM (src,fn) (reached_functions mods e) /\
  ALOOKUP mods src = SOME ts /\
  (find_function fn ts = SOME (dflts,body) \/ (dflts = [] /\ body = [])) /\
  MEM a (callee_accesses (accesses_exprs dflts ++ accesses_stmts body)) ==>
  MEM a (expr_accesses mods e)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[accesses_expr_def, accesses_stmt_def, callee_accesses_def] >>
  simp[expr_accesses_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> disj2_tac >>
  qexists_tac `(src,fn)` >> simp[function_accesses_def]
QED

Theorem direct_function_reached:
  MEM callee (int_calls_expr e) ==> MEM callee (reached_functions mods e)
Proof
  simp[reached_functions_def]
QED

Theorem direct_expr_accesses:
  MEM a (accesses_expr e) ==> MEM a (expr_accesses mods e)
Proof
  simp[expr_accesses_def]
QED

(* Unlike the self-cycle boundary, this also preserves distinct endpoints. *)
Theorem LRC_path_shorten[local]:
  LRC R ls x y /\ ~ALL_DISTINCT ls ==>
  ?m. 0 < m /\ m < LENGTH ls /\ NRC R m x y
Proof
  strip_tac >> drule not_ALL_DISTINCT_split >> strip_tac >>
  gvs[LRC_APPEND, LRC_def] >>
  qexists_tac `LENGTH (p ++ e::r)` >> simp[NRC_LRC] >>
  qexists_tac `p ++ e::r` >> simp[LRC_APPEND, LRC_def] >> metis_tac[]
QED

Theorem finite_TC_path_bound[local]:
  (!x y. R x y ==> MEM x nodes /\ MEM y nodes) ==>
  TC R x y ==>
  ?n. 0 < n /\ n <= LENGTH nodes /\ NRC R n x y
Proof
  rpt strip_tac >>
  `?n. 0 < n /\ NRC R n x y` by
    (gvs[TC_eq_NRC] >> qexists_tac `SUC n` >> simp[]) >>
  qspec_then `\m. 0 < m /\ NRC R m x y` mp_tac WOP >>
  (impl_tac >- (qexists_tac `n` >> simp[])) >> strip_tac >>
  fs[NRC_LRC] >>
  `ALL_DISTINCT ls'` by
    (spose_not_then assume_tac >> drule_all LRC_path_shorten >>
     fs[NRC_LRC] >> metis_tac[]) >>
  `set ls' SUBSET set nodes` by
    (rw[SUBSET_DEF] >> drule_all LRC_MEM >> metis_tac[]) >>
  qexists_tac `n'` >> simp[] >>
  `CARD (set ls') <= CARD (set nodes)` by
    metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  `CARD (set nodes) <= LENGTH nodes` by simp[CARD_LIST_TO_SET] >>
  conj_tac
  >- (`CARD (set ls') = LENGTH ls'` by
        simp[ALL_DISTINCT_CARD_LIST_TO_SET] >> decide_tac) >>
  qexists_tac `ls'` >> simp[]
QED

Theorem contract_reachable_TC:
  MEM callee (reachable_nodes (contract_call_edges mods)
                (LENGTH (contract_call_nodes mods)) caller) <=>
  TC (call_edge_rel (contract_call_edges mods)) caller callee
Proof
  eq_tac
  >- (simp[MEM_reachable_nodes_NRC] >> strip_tac >>
      Cases_on `n` >> gvs[TC_eq_NRC] >> metis_tac[]) >>
  strip_tac >>
  `?n. 0 < n /\ n <= LENGTH (contract_call_nodes mods) /\
       NRC (call_edge_rel (contract_call_edges mods)) n caller callee` by
    (irule finite_TC_path_bound >> simp[call_edge_rel_def] >>
     metis_tac[contract_call_edge_nodes, pairTheory.FST, pairTheory.SND]) >>
  simp[MEM_reachable_nodes_NRC] >> qexists_tac `n` >> simp[]
QED

Theorem reached_functions_edge:
  MEM caller (reached_functions mods e) /\
  MEM (caller,callee) (contract_call_edges mods) ==>
  MEM callee (reached_functions mods e)
Proof
  simp[reached_functions_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
       contract_reachable_TC] >>
  rpt strip_tac >> disj2_tac
  >- (qexists_tac `caller` >> simp[] >>
      metis_tac[TC_SUBSET, call_edge_rel_def]) >>
  qexists_tac `y` >> simp[] >>
  metis_tac[TC_TRANSITIVE, transitive_def, TC_SUBSET, call_edge_rel_def]
QED

Theorem reached_callable_calls:
  !src fn mods e ts in_deploy mut nr args dflts ret body callee.
  MEM (src,fn) (reached_functions mods e) /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
  MEM callee (function_int_calls dflts body) ==>
  MEM callee (reached_functions mods e)
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_callable_function_SOME_decompose >>
  strip_tac >> gvs[function_int_calls_def, int_calls_expr_def, int_calls_stmt_def] >>
  irule reached_functions_edge >> qexists_tac `(src,fn)` >> simp[] >>
  irule contract_call_edges_function >>
  drule ALOOKUP_MEM >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[function_int_calls_def]
QED

Theorem reached_function_write_accesses:
  !src fn mods e ts dflts body ns.
  MEM (src,fn) (reached_functions mods e) /\
  ALOOKUP mods src = SOME ts /\
  (find_function fn ts = SOME (dflts,body) \/ (dflts = [] /\ body = [])) /\
  MEM (WriteAcc (StateRef ns)) (accesses_exprs dflts ++ accesses_stmts body) ==>
  MEM (WriteAcc (StateRef ns)) (expr_accesses mods e)
Proof
  metis_tac[reached_function_accesses, callee_accesses_write]
QED

Theorem reached_function_no_risky:
  !src fn mods e ts dflts body.
  MEM (src,fn) (reached_functions mods e) /\
  ALOOKUP mods src = SOME ts /\
  (find_function fn ts = SOME (dflts,body) \/ (dflts = [] /\ body = [])) /\
  ~MEM RiskyAcc (expr_accesses mods e) ==>
  ~MEM RiskyAcc (accesses_exprs dflts ++ accesses_stmts body)
Proof
  metis_tac[reached_function_accesses, callee_accesses_risky]
QED

(* Closed proof-interface notation; no additional logical definitions. *)
val frame = ``\cx A st st'. ?ws.
  EVERY (\(mid,n,subs). MEM (WriteAcc (StateRef (mid,n))) A) ws /\
  !tr k.
    (!mid n subs slot tv i.
       MEM (mid,n,subs) ws /\
       declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
       i < type_slot_size tv ==> k <> slot + n2w i) /\
    (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
    lookup_storage k (get_storage cx st' tr) =
    lookup_storage k (get_storage cx st tr)``;
val typed_state = ``\env cx st.
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx``;
val allowed_writes = ``\A xs. !ns.
  MEM (WriteAcc (StateRef ns)) xs ==> MEM (WriteAcc (StateRef ns)) A``;
val safe_accesses = ``\A (R:(num option # string) list) xs cs.
  ^allowed_writes A xs /\ ~MEM RiskyAcc xs /\
  (!c. MEM c cs ==> MEM c R)``;
val callable_closed = ``\cx A R.
  !src fn ts mut nr args dflts ret body.
    MEM (src,fn) R /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
    ^safe_accesses A R (accesses_exprs dflts ++ accesses_stmts body)
      (function_int_calls dflts body)``;

Theorem finite_frame_refl:
  ^frame cx A st st
Proof
  simp[] >> qexists_tac `[]` >> simp[]
QED

Theorem finite_frame_trans:
  ^frame cx A s0 s1 /\ ^frame cx A s1 s2 ==> ^frame cx A s0 s2
Proof
  simp[] >> strip_tac >> qexists_tac `ws ++ ws'` >>
  conj_tac >- simp[EVERY_APPEND] >> rpt strip_tac >>
  `lookup_storage k (get_storage cx s2 tr) =
   lookup_storage k (get_storage cx s1 tr)` by
    (qpat_x_assum `!tr k. _ ==> _ = lookup_storage k (get_storage cx s1 tr)`
       (qspecl_then [`tr`,`k`] irule) >>
     simp[] >> rpt strip_tac >> metis_tac[MEM_APPEND]) >>
  `lookup_storage k (get_storage cx s1 tr) =
   lookup_storage k (get_storage cx s0 tr)` by
    (qpat_x_assum `!tr k. _ ==> _ = lookup_storage k (get_storage cx s0 tr)`
       (qspecl_then [`tr`,`k`] irule) >>
     simp[] >> rpt strip_tac >> metis_tac[MEM_APPEND]) >> simp[]
QED

Theorem finite_frame_stk:
  ^frame (cx with stk := stk') A s0 s1 <=> ^frame cx A s0 s1
Proof
  simp[oneline get_storage_def]
QED

Theorem callable_closed_stk:
  ^callable_closed (cx with stk := stk') A R <=> ^callable_closed cx A R
Proof
  simp[get_module_code_def]
QED

Theorem safe_accesses_append:
  ^safe_accesses A R (xs ++ ys) (cs ++ ds) <=>
  ^safe_accesses A R xs cs /\ ^safe_accesses A R ys ds
Proof
  simp[] >> metis_tac[]
QED

Theorem safe_accesses_expr_initial:
  ~MEM RiskyAcc (expr_accesses mods e) ==>
  ^safe_accesses (expr_accesses mods e) (reached_functions mods e)
    (accesses_expr e) (int_calls_expr e)
Proof
  simp[] >> metis_tac[direct_expr_accesses, direct_function_reached]
QED

Theorem callable_closed_initial:
  (!src fn ts mut nr args dflts ret body.
     MEM (src,fn) (reached_functions mods e) /\
     get_module_code cx src = SOME ts /\
     lookup_callable_function cx.in_deploy fn ts =
       SOME (mut,nr,args,dflts,ret,body) ==>
     ALOOKUP mods src = SOME ts /\
     (find_function fn ts = SOME (dflts,body) \/
      (dflts = [] /\ body = []))) /\
  ~MEM RiskyAcc (expr_accesses mods e) ==>
  ^callable_closed cx (expr_accesses mods e) (reached_functions mods e)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  (conj_tac >- metis_tac[reached_function_write_accesses]) >>
  (conj_tac >- metis_tac[reached_function_no_risky]) >>
  metis_tac[reached_callable_calls]
QED

Theorem evaluate_finite_frame:
  (!cx s. !A R env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_stmt s) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_stmt s) (int_calls_stmt s) /\
    eval_stmt cx s st = (res,st') ==> ^frame cx A st st') /\
  (!cx ss. !A R env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_stmts ss) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_stmts ss) (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res,st') ==> ^frame cx A st st') /\
  (!cx it. !A R env ty st res st'.
    well_typed_iterator env ty it /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_iterator it) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_iterator it) (int_calls_iterator it) /\
    eval_iterator cx it st = (res,st') ==> ^frame cx A st st') /\
  (!cx tyv id body vs. !A R env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    ^typed_state env cx st /\ call_evaluation_safe cx (int_calls_stmts body) /\
    ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_stmts body) (int_calls_stmts body) /\
    eval_for cx tyv id body vs st = (res,st') ==> ^frame cx A st st') /\
  (!cx e. !A R env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    ^typed_state env cx st /\ call_evaluation_safe cx (int_calls_expr e) /\
    ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_expr e) (int_calls_expr e) /\
    eval_expr cx e st = (res,st') ==> ^frame cx A st st') /\
  (!cx es. !A R env st res st'.
    well_typed_exprs env es /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_exprs es) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) /\
    eval_exprs cx es st = (res,st') ==> ^frame cx A st st') /\
  (!cx bt. !A R env vt st res st'.
    type_place_target env bt = SOME vt /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_target bt) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_target bt) (int_calls_target bt) /\
    eval_base_place cx bt st = (res,st') ==> ^frame cx A st st') /\
  (!cx bt. !A R env ty st res st'.
    well_typed_target env bt ty /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_target bt) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_target bt) (int_calls_target bt) /\
    eval_target_place cx bt st = (res,st') ==> ^frame cx A st st') /\
  (!cx g v. !A R env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    ^typed_state env cx st /\ call_evaluation_safe cx (int_calls_atarget g) /\
    ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_atarget g) (int_calls_atarget g) /\
    assign_tuple_targets cx g v st = (res,st') ==> ^frame cx A st st') /\
  (!cx gs vs. !A R env tys st res st'.
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_atargets gs) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_atargets gs) (int_calls_atargets gs) /\
    assign_tuple_target_list cx gs vs st = (res,st') ==> ^frame cx A st st') /\
  (!cx es. !A R env st res st'.
    well_typed_exprs env es /\ ^typed_state env cx st /\
    call_evaluation_safe cx (int_calls_exprs es) /\ ^callable_closed cx A R /\
    ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) /\
    eval_expr_results cx es st = (res,st') ==> ^frame cx A st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once evaluate_def, return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- (rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- (rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- (rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
          accesses_expr_def, int_calls_expr_def,
          Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      (conj_tac >- (qexists_tac `R` >> conj_tac
        >- first_assum ACCEPT_TAC >> simp[])) >>
      qexists_tac `env` >> simp[]) (* Return (SOME e): retain effects of e. *)
  >- (rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- (rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[])
  >- suspend "raise_reason"
  >- suspend "raise_custom"
  >- suspend "assert_bare"
  >- suspend "assert_bare"
  >- suspend "assert_reason"
  (* Call inventory: IntCall; five risky families; RawLog; RawRevert;
     SelfDestructTarget. Inspect only the outer branch's final premises,
     never conditional recursive IHs. Non-call cases remain with siblings. *)
  >> (fn g =>
        let
          fun final_pre tm =
            let val (_,b) = strip_forall tm
                val (p,q) = dest_imp b
            in if is_forall q orelse is_imp q then final_pre q else p end
          val call = total (find_term
            (can (match_term ``well_typed_expr env (Call ty tgt es drv)``)))
            (final_pre (#2 g))
        in case call of
          NONE =>
            let
              val p = final_pre (#2 g)
              fun has pat = can (find_term (can (match_term pat))) p
            in
              if has ``type_stmt env ret_ty (Assign (BaseTarget t) e)`` then
                suspend "assign_base" g
              else if has ``type_stmt env ret_ty (Assign (TupleTarget gs) e)`` then
                suspend "assign_tuple" g
              else if has ``type_stmt env ret_ty (AugAssign ty t bop e)`` then
                suspend "augassign" g
              else if has ``type_stmt env ret_ty (Append t e)`` then suspend "append" g
              else if has ``well_typed_expr env (Pop ty bt)`` then suspend "pop" g
              else if has ``well_typed_atarget env (BaseTarget t) ty`` then
                suspend "tuple_base" g
              else if has ``well_typed_atarget env (TupleTarget gs) ty`` then
                suspend "tuple_nested" g
              else if has ``LIST_REL (\g ty. well_typed_atarget env g ty) [] tys`` then
                suspend "tuple_list_nil" g
              else if has ``assign_tuple_target_list cx (g::gs) (v::vs) st`` then
                suspend "tuple_list_cons" g
              else if has ``LIST_REL (\g ty. well_typed_atarget env g ty) gs tys`` then
                suspend "tuple_list_error" g
              else if has ``eval_expr_results cx (e::es) st`` then
                suspend "results_cons" g
              else if has ``eval_expr_results cx [] st`` then
                suspend "results_nil" g
              else if has ``eval_target_place cx bt st`` then
                suspend "target_place" g
              else if has ``eval_exprs cx [] st`` then suspend "exprs_nil" g
              else if has ``eval_exprs cx (e::es) st`` then suspend "exprs_cons" g
              else if has ``eval_base_place cx (NameTarget id) st`` then suspend "base_name" g
              else if has ``eval_base_place cx (TopLevelNameTarget srcid) st`` then suspend "base_global" g
              else if has ``eval_base_place cx (AttributeTarget t id) st`` then suspend "base_attr" g
              else if has ``eval_base_place cx (SubscriptTarget t e) st`` then suspend "base_subscript" g
              else if has ``eval_expr cx (Name ty id) st`` then suspend "expr_name" g
              else if has ``eval_expr cx (TopLevelName ty nsid) st`` then suspend "expr_global" g
              else if has ``eval_expr cx (FlagMember ty nsid mid) st`` then suspend "expr_flag" g
              else if has ``eval_expr cx (Literal ty l) st`` then suspend "expr_literal" g
              else if has ``eval_expr cx (Attribute ty e id) st`` then suspend "expr_attr" g
              else if has ``eval_expr cx (StructLit ty nsid kes) st`` then suspend "expr_struct" g
              else if has ``eval_expr cx (TypeBuiltin ty tb typ es) st`` then suspend "expr_typebuiltin" g
              else if has ``eval_expr cx (Builtin ty bt es) st`` then suspend "expr_builtin" g
              else if has ``eval_expr cx (IfExp ty c yes no) st`` then suspend "expr_ifexp" g
              else if has ``eval_expr cx (Subscript ty arr idx) st`` then suspend "expr_subscript" g
              else if has ``eval_stmt cx (Assert e (AssertCustomError err)) st`` then suspend "assert_custom" g
              else if has ``eval_stmt cx (Log id es) st`` then suspend "stmt_log" g
              else if has ``eval_stmt cx (AnnAssign id ty e) st`` then suspend "stmt_annassign" g
              else if has ``eval_stmt cx (If e yes no) st`` then suspend "stmt_if" g
              else if has ``eval_stmt cx (For id ty it n bdy) st`` then suspend "stmt_for" g
              else if has ``eval_stmt cx (Expr e) st`` then suspend "stmt_expr" g
              else if has ``eval_stmts cx [] st`` then suspend "stmts_nil" g
              else if has ``eval_stmts cx (s::ss) st`` then suspend "stmts_cons" g
              else if has ``eval_iterator cx (Array e) st`` then suspend "iterator_array" g
              else if has ``eval_iterator cx (Range e1 e2) st`` then suspend "iterator_range" g
              else if has ``eval_for cx tyv id bdy [] st`` then suspend "for_nil" g
              else if has ``eval_for cx tyv id bdy (v::vs) st`` then suspend "for_cons" g
              else FAIL_TAC "unassigned-evaluate-case" g
            end
        | SOME tm =>
            let val e = List.nth (snd (strip_comb tm),1)
                val target = List.nth (snd (strip_comb e),1)
                val name = fst (dest_const (fst (strip_comb target)))
            in case name of
              "IntCall" => suspend "intcall" g
            | "RawLog" => suspend "rawlog" g
            | "RawRevert" => suspend "rawrevert" g
            | "SelfDestructTarget" => suspend "selfdestruct" g
            | _ => suspend ("risky_" ^ name) g
            end
        end)
QED

Resume evaluate_finite_frame[assign_base]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "target_ih") (mk_asm "value_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      safe_accesses_append] >>
  gvs[accesses_atarget_def, int_calls_atarget_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (value_res,value_st)` >>
  `^frame cx A st value_st` by
    (BETA_TAC >> asm "value_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st value_st` (mk_asm "prefix") >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `value_res`
  >- (strip_tac >>
      qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
        (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
      drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >>
      strip_tac >> gvs[vyperTypeSystemTheory.well_typed_atarget_def] >>
      asm_x "target_ih" drule >>
      disch_then (mk_asm "target_frame") >>
      Cases_on `eval_target_place cx bt value_st` >>
      rename1 `eval_target_place cx bt value_st = (target_res,target_st)` >>
      `^frame cx A value_st target_st` by
        (BETA_TAC >> asm "target_frame" (irule o BETA_RULE) >>
         goal_assum (drule_at Any) >> simp[] >>
         (conj_tac >- (qexists_tac `R` >> conj_tac
           >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
         qexists_tac `env` >> gvs[vyperTypeSystemTheory.well_typed_target_def]) >>
      qpat_x_assum `^frame cx A value_st target_st` (mk_asm "target_prefix") >>
      reverse (Cases_on `target_res`)
      >- (gvs[bind_def, raise_def] >> irule (BETA_RULE finite_frame_trans) >>
          qexists_tac `value_st` >> conj_tac
          >- asm "prefix" (ACCEPT_TAC o BETA_RULE) >>
          asm "target_prefix" (ACCEPT_TAC o BETA_RULE)) >>
      gvs[bind_def] >>
      qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
        (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
      Cases_on `read_result cx x target_st` >>
      rename1 `read_result cx x target_st = (loaded,read_st)` >>
      drule read_result_state >> strip_tac >> gvs[] >>
      reverse (Cases_on `loaded`)
      >- (gvs[] >> irule (BETA_RULE finite_frame_trans) >>
          qexists_tac `value_st` >> conj_tac
          >- asm "prefix" (ACCEPT_TAC o BETA_RULE) >>
          asm "target_prefix" (ACCEPT_TAC o BETA_RULE)) >>
      gvs[] >>
      qspecl_then [`cx`,`bt`] (drule_all o cj 2)
        (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
      drule (cj 8 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >>
      strip_tac >>
      `eval_result_typed (env,cx,read_st) x (Type (expr_type e))` by
        (irule eval_result_typed_transport >> qexists_tac `value_st` >> simp[]) >>
      `runtime_consistent env cx st` by simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
      drule_all vyperTypeEvalStoragePreservationTheory.eval_expr_success_storage_facts >>
      strip_tac >>
      gvs[] >> drule_all live_result_transport >> strip_tac >>
      drule_all typed_result_read_sound >> strip_tac >>
      gvs[] >>
      `value_has_type tv x''` by
        (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
         drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
         strip_tac >> gvs[]) >>
      irule (BETA_RULE finite_frame_trans) >> qexists_tac `value_st` >>
      (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
      irule (BETA_RULE finite_frame_trans) >> qexists_tac `read_st` >>
      (conj_tac >- asm "target_prefix" (ACCEPT_TAC o BETA_RULE)) >>
      Cases_on `x'`
      >- (gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
          drule eval_target_place_labelled_region >> strip_tac >> gvs[] >>
          qexists_tac `[(mid,n,keys)]` >> simp[] >>
          rpt strip_tac >> irule typed_subregion_write_word_frame >>
          goal_assum (drule_at Any) >>
          gvs[write_place_def] >> metis_tac[]) 
      >- (drule vyperPlaceFramesTheory.write_memory_place_storage >>
          strip_tac >> qexists_tac `[]` >> simp[]) >>
      drule vyperPlaceFramesTheory.write_immutable_place_storage >>
      strip_tac >> qexists_tac `[]` >> simp[]) >>
  strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)
QED
Resume evaluate_finite_frame[assign_tuple]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tuple_ih") (mk_asm "value_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      safe_accesses_append] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (value_res,value_st)` >>
  `^frame cx A st value_st` by
    (BETA_TAC >> asm "value_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st value_st` (mk_asm "prefix") >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `value_res`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `read_result cx x value_st` >>
  rename1 `read_result cx x value_st = (loaded,read_st)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `loaded`)
  >- (gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  `runtime_consistent env cx st` by simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  drule_all vyperTypeEvalStoragePreservationTheory.eval_expr_success_storage_facts >> strip_tac >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >> strip_tac >>
  asm_x "tuple_ih" drule >> disch_then (mk_asm "tuple_frame") >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `read_st` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  asm "tuple_frame" (irule o BETA_RULE) >>
  goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
  qexists_tac `env` >> simp[] >>
  `value_runtime_typed env ty x'` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type]) >>
  metis_tac[]
QED
Resume evaluate_finite_frame[augassign]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "value_ih") (mk_asm "target_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      AllCaseEqs()] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (pr,ps)` >>
  `^frame cx A st ps` by
    (BETA_TAC >> asm "target_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st ps` (mk_asm "prefix") >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `pr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
    (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `read_place cx x ps` >>
  rename1 `read_place cx x ps = (cr,cs)` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `cr`)
  >- (gvs[raise_def] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  `place_type_value cx x cs = (INL tv,cs)` by
    fs[runtime_place_typed_def] >>
  gvs[] >>
  asm_x "value_ih" drule >> disch_then drule >> disch_then drule >>
  disch_then (mk_asm "value_frame") >>
  Cases_on `eval_expr cx e cs` >>
  rename1 `eval_expr cx e cs = (vr,vs)` >>
  `^frame cx A cs vs` by
    (BETA_TAC >> asm "value_frame" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A cs vs` (mk_asm "value_prefix") >>
  gvs[] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `cs` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  reverse (Cases_on `vr`)
  >- (gvs[raise_def] >> asm "value_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `read_result cx x'' vs` >>
  rename1 `read_result cx x'' vs = (rr,rs)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `rs` >>
  (conj_tac >- asm "value_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  reverse (Cases_on `rr`)
  >- (gvs[] >> qexists_tac `[]` >> simp[]) >>
  gvs[] >>
  `runtime_consistent env cx cs` by
    simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  drule_all vyperTypeEvalStoragePreservationTheory.eval_expr_success_storage_facts >>
  strip_tac >> drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `lift_sum binres rs` >>
  Cases_on `binres`
  >- (gvs[lift_sum_def, return_def] >>
      Cases_on `x`
      >- (rename1 `write_place cx (StoragePlace b slot leaf) result rs = (res,st')` >>
          `live_memory_result cs (PlaceR (StoragePlace b slot leaf))` by
            simp[live_memory_result_def] >>
          drule_all live_place_read_sound >> strip_tac >> gvs[] >>
          fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
          `value_has_type leaf result` by
            (irule vyperTypeBuiltinsTheory.well_typed_binop_success_type >>
             goal_assum (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)) >>
             simp[] >> goal_assum (drule_at Any) >> simp[] >>
             metis_tac[]) >>
          gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
          drule eval_target_place_labelled_region >> strip_tac >> gvs[] >>
          qexists_tac `[(mid,n,keys)]` >> simp[] >> rpt strip_tac >>
          irule typed_subregion_write_word_frame >> goal_assum (drule_at Any) >>
          gvs[write_place_def] >> goal_assum (drule_at Any) >>
          simp[] >> metis_tac[])
      >- (drule vyperPlaceFramesTheory.write_memory_place_storage >>
          strip_tac >> qexists_tac `[]` >> simp[]) >>
      drule vyperPlaceFramesTheory.write_immutable_place_storage >>
      strip_tac >> qexists_tac `[]` >> simp[]) >>
  gvs[lift_sum_def, raise_def] >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[append]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "value_ih") (mk_asm "target_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      safe_accesses_append, AllCaseEqs()] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[vyperTypeSystemTheory.well_typed_target_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (pr,ps)` >>
  `^frame cx A st ps` by
    (BETA_TAC >> asm "target_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st ps` (mk_asm "prefix") >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >> reverse (Cases_on `pr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
    (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
  asm_x "value_ih" drule >> disch_then (mk_asm "value_frame") >>
  Cases_on `eval_expr cx e ps` >>
  rename1 `eval_expr cx e ps = (vr,vs)` >>
  `^frame cx A ps vs` by
    (BETA_TAC >> asm "value_frame" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A ps vs` (mk_asm "value_prefix") >>
  gvs[] >> reverse (Cases_on `vr`)
  >- (gvs[raise_def] >> irule (BETA_RULE finite_frame_trans) >>
      qexists_tac `ps` >> conj_tac
      >- asm "prefix" (ACCEPT_TAC o BETA_RULE) >>
      asm "value_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `read_result cx x' vs` >>
  rename1 `read_result cx x' vs = (rr,rs)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `ps` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `rs` >>
  (conj_tac >- asm "value_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  reverse (Cases_on `rr`)
  >- (gvs[] >> qexists_tac `[]` >> simp[]) >>
  gvs[] >>
  `runtime_consistent env cx ps` by
    simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  drule_all vyperTypeEvalStoragePreservationTheory.eval_expr_success_storage_facts >>
  strip_tac >> drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  Cases_on `x`
  >- (gvs[runtime_place_typed_def, place_type_value_def, return_def,
          vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      drule eval_target_place_labelled_region >> strip_tac >> gvs[] >>
      `value_has_type tv' x''` by
        (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
         drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
         strip_tac >> gvs[]) >>
      qexists_tac `[(mid,n',keys)]` >> simp[] >> rpt strip_tac >>
      asm_x "target_ih" kall_tac >> asm_x "value_frame" kall_tac >>
      asm_x "closure" kall_tac >> asm_x "prefix" kall_tac >>
      asm_x "value_prefix" kall_tac >>
      irule storage_append_word_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      Cases_on `tr = b` >> simp[] >>
      metis_tac[storage_subregion_word_exclusion])
  >- (drule vyperPlaceStoragePreservationTheory.append_memory_place_storage >>
      strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule vyperPlaceStoragePreservationTheory.append_immutable_place_storage >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[pop]:
  rpt gen_tac >> disch_then (mk_asm "target_ih") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def] >>
  `well_typed_target env bt (ArrayT v10 (Dynamic n))` by
    simp[vyperTypeSystemTheory.well_typed_target_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (pr,ps)` >>
  `^frame cx A st ps` by
    (BETA_TAC >> asm "target_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st ps` (mk_asm "prefix") >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `pr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `ps` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
    (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `x`
  >- (gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
      drule eval_target_place_labelled_region >> strip_tac >> gvs[] >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      rename1 `declared_storage_region cx mid name keys = SOME (b,root,tv)` >>
      qexists_tac `[(mid,name,keys)]` >> simp[] >> rpt strip_tac >>
      asm_x "target_ih" kall_tac >> asm_x "closure" kall_tac >>
      asm_x "prefix" kall_tac >>
      irule storage_pop_word_frame >> goal_assum (drule_at Any) >>
      Cases_on `tr = b` >> simp[] >>
      `!i. i < type_slot_size (ArrayTV tv' (Dynamic n)) ==>
           k <> (root + n2w delta) + n2w i` by
        (metis_tac[storage_subregion_word_exclusion]) >>
      first_x_assum (qspec_then `0` mp_tac) >>
      simp[vyperValueTheory.type_slot_size_def, wordsTheory.WORD_ADD_0])
  >- (drule vyperPlaceStoragePreservationTheory.pop_memory_place_storage >>
      strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule vyperPlaceStoragePreservationTheory.pop_immutable_place_storage >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[tuple_base]:
  markerLib.RESUME_TAC >> rpt gen_tac >> disch_then (mk_asm "target_ih") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.well_typed_atarget_def, accesses_atarget_def,
      int_calls_atarget_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (pr,ps)` >>
  `^frame cx A st ps` by
    (BETA_TAC >> asm "target_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st ps` (mk_asm "prefix") >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >> reverse (Cases_on `pr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >> gvs[] >>
  qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
    (cj 8 eval_scc_type_sound_results_mutual) >> strip_tac >>
  gvs[eval_result_typed_def] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `ps` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  Cases_on `x`
  >- (gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
      drule eval_target_place_labelled_region >> strip_tac >> gvs[] >>
      gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      qexists_tac `[(mid,n,keys)]` >> simp[] >> rpt strip_tac >>
      irule typed_subregion_write_word_frame >> goal_assum (drule_at Any) >>
      gvs[write_place_def] >> metis_tac[])
  >- (drule vyperPlaceFramesTheory.write_memory_place_storage >>
      strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule vyperPlaceFramesTheory.write_immutable_place_storage >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[tuple_nested]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, vyperTypeSystemTheory.well_typed_atarget_def,
      accesses_atarget_def, int_calls_atarget_def, AllCaseEqs(), raise_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> qexists_tac `tys` >> simp[]
QED
Resume evaluate_finite_frame[tuple_list_nil]:
  markerLib.RESUME_TAC >> rpt gen_tac >> rpt strip_tac >>
  gvs[Once evaluate_def, return_def] >>
  qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[tuple_list_cons]:
  markerLib.RESUME_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_ih") (mk_asm "head_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[LIST_REL_CONS1, accesses_atarget_def, int_calls_atarget_def,
      safe_accesses_append] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (hr,hs)` >>
  `^frame cx A st hs` by
    (BETA_TAC >> asm "head_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st hs` (mk_asm "prefix") >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  reverse (Cases_on `hr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >> gvs[] >>
  drule_all (cj 9 eval_scc_type_sound_results_mutual) >> strip_tac >>
  asm_x "tail_ih" drule >> disch_then (mk_asm "tail_frame") >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `hs` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  asm "tail_frame" (irule o BETA_RULE) >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
  qexists_tac `env` >> metis_tac[]
QED
Resume evaluate_finite_frame[tuple_list_error]:
  markerLib.RESUME_TAC >> rpt gen_tac >> rpt strip_tac >>
  gvs[Once evaluate_def, raise_def] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[assert_custom]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s tv t id positional kwargs tops params es. _` (mk_asm "args_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "condition_ih") >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      accesses_assert_reason_def, int_calls_assert_reason_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "condition_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "condition_ih" kall_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, raise_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  asm_x "args_ih" (drule o REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]) >>
  disch_then (mk_asm "args_ih") >>
  gvs[AllCaseEqs()] >> imp_res_tac read_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def]
  >- (gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE))
  >- (qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
       (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
      gvs[] >> rename1 `eval_expr cx e st = (INL x,s1)` >>
      Cases_on `err` >>
      Cases_on `get_module_code cx (FST p)`
      >- (gvs[raise_def] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
      rename1 `get_module_code cx (FST p) = SOME tops` >>
      Cases_on `lookup_custom_error_args_in (SND p) tops`
      >- (gvs[raise_def] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
      rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
      Cases_on `order_custom_error_args params (CustomError p l l0)`
      >- (gvs[raise_def] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
      rename1 `order_custom_error_args params (CustomError p positional kwargs) = SOME es` >>
      `es = custom_error_exprs (CustomError p positional kwargs)` by
        (gvs[vyperASTTheory.order_custom_error_args_def,
             vyperASTTheory.custom_error_exprs_def, AllCaseEqs()] >>
         imp_res_tac vyperASTTheory.order_custom_error_kwargs_SOME >>
         gvs[listTheory.NULL_EQ]) >>
      Cases_on `eval_exprs cx es s1` >> rename1 `eval_exprs cx es s1 = (r2,s2)` >>
      `^frame cx A s1 s2` by
        (BETA_TAC >> asm "args_ih" (irule o BETA_RULE) >> simp[] >>
         qexistsl_tac [`R`,`env`,`r2`] >> simp[] >>
         (conj_tac >- asm "closure" (ACCEPT_TAC o SRULE [])) >>
         gvs[vyperTypeSystemTheory.well_typed_custom_error_def] >>
         metis_tac[]) >>
      qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
      asm_x "args_ih" kall_tac >>
      gvs[bind_def, lift_option_def, raise_def, return_def, AllCaseEqs()] >>
      gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
      irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
      (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
      asm "suffix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)
QED
Resume evaluate_finite_frame[stmt_log]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "args_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      AllCaseEqs()] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "args_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "args_ih" kall_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_def, raise_def, return_def,
       ignore_bind_def, check_not_static_def, check_def, assert_def, push_log_def,
       AllCaseEqs()] >>
  Cases_on `r1` >> simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
  asm "prefix" mp_tac >> simp[oneline get_storage_def]
QED
Resume evaluate_finite_frame[stmt_annassign]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!tenv s0 tyv t. _` (mk_asm "expr_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, raise_def, return_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> simp[raise_def, return_def]
  >- (strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]) >>
  strip_tac >>
  asm_x "expr_ih" (qspecl_then [`get_tenv cx`,`st`,`x`,`st`] mp_tac) >>
  (impl_tac >- simp[lift_option_type_def, return_def]) >>
  disch_then (mk_asm "expr_ih") >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "expr_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "expr_ih" kall_tac >>
  gvs[AllCaseEqs()] >> imp_res_tac read_result_state >> gvs[] >>
  gvs[new_variable_def, bind_apply, ignore_bind_apply, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, set_scopes_def,
      list_CASE_rator, AllCaseEqs()] >>
  asm "prefix" mp_tac >> simp[oneline get_storage_def]
QED
Resume evaluate_finite_frame[stmt_if]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s0 tv t s2 x t2. _ /\ push_scope s2 = (INL x,t2) ==> _`
    (mk_asm "then_ih") >>
  qpat_x_assum `!s0 tv t s2 x t2. _ /\ push_scope s2 = (INL x,t2) ==> _`
    (mk_asm "else_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "condition_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "condition_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "condition_ih" kall_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, push_scope_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    metis_tac[call_evaluation_safe_append_right] >>
  gvs[ignore_bind_def, bind_def, push_scope_def, return_def] >>
  `push_scope s1 = (INL (),s1 with scopes updated_by CONS FEMPTY)` by
    simp[push_scope_def, return_def] >>
  asm_x "then_ih" (drule o REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]) >>
  disch_then drule >> disch_then (mk_asm "then_ih") >>
  asm_x "else_ih" (drule o REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]) >>
  disch_then drule >> disch_then (mk_asm "else_ih") >>
  `^typed_state env cx (s1 with scopes updated_by CONS FEMPTY)` by
    (simp[] >> metis_tac[vyperTypeStatePreservationTheory.push_scope_preserves_state_well_typed,
      vyperTypeEnvPreservationTheory.push_scope_env_consistent]) >>
  `!r s2. eval_stmts cx ss (s1 with scopes updated_by CONS FEMPTY) = (r,s2) ==>
     ^frame cx A (s1 with scopes updated_by CONS FEMPTY) s2` by
    (rpt strip_tac >> BETA_TAC >> asm "else_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `!r s2. eval_stmts cx ss' (s1 with scopes updated_by CONS FEMPTY) = (r,s2) ==>
     ^frame cx A (s1 with scopes updated_by CONS FEMPTY) s2` by
    (rpt strip_tac >> BETA_TAC >> asm "then_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  asm_x "then_ih" kall_tac >> asm_x "else_ih" kall_tac >>
  `(s1 with scopes updated_by CONS FEMPTY) =
   (s1 with scopes := FEMPTY :: s1.scopes)` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  fs[get_storage_scopes] >>
  gvs[finally_def, switch_BoolV_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), ignore_bind_def, bind_def,
      pop_scope_def, return_def, raise_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[get_storage_scopes] >>
  IF (qpat_assum `EVERY _ ws` kall_tac)
    (qexists_tac `ws` >> simp[] >> rpt gen_tac >> first_assum MATCH_ACCEPT_TAC)
    (qexists_tac `[]` >> simp[])
QED
Resume evaluate_finite_frame[stmt_for]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!tenv s0 tyv t. _` (mk_asm "iterator_ih") >>
  qpat_x_assum `!tenv s0 tyv t s1 vs t1 s2 x t2. _` (mk_asm "loop_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) typ`
  >- (gvs[Once evaluate_def, lift_option_type_def, raise_def, bind_def] >>
      qexists_tac `[]` >> simp[]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tyv` >>
  `lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" st =
   (INL tyv,st)` by simp[lift_option_type_def, return_def] >>
  asm_x "iterator_ih" (qspecl_then [`get_tenv cx`, `st`, `tyv`, `st`] mp_tac) >>
  simp[lift_option_type_def, return_def] >> disch_then (mk_asm "iterator_ih") >>
  Cases_on `eval_iterator cx it st` >> rename1 `eval_iterator cx it st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "iterator_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "iterator_ih" kall_tac >>
  qpat_x_assum `eval_stmt cx (For id typ it n body') st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  rename1 `eval_iterator cx it st = (INL vs,s1)` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vs)` >>
  simp[check_def, assert_def, return_def, raise_def, bind_def, ignore_bind_def]
  >- (strip_tac >>
      drule_all (cj 3 eval_scc_type_sound_results_mutual) >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        fs[env_consistent_def, env_context_consistent_def] >>
      gvs[] >>
      asm_x "loop_ih" (qspecl_then [`get_tenv cx`, `st`, `tyv`, `st`] mp_tac) >>
      simp[lift_option_type_def, return_def] >>
      disch_then (drule o REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]) >>
      simp[check_def, assert_def, return_def] >>
      disch_then (mk_asm "loop_ih") >>
      `^frame cx A s1 st'` by
        (BETA_TAC >> asm "loop_ih" irule >>
         (conj_tac >- (qexists_tac `R` >> simp[] >>
           asm "closure" (ACCEPT_TAC o SRULE []))) >>
         simp[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
      irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
      conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE) >>
      first_assum (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)
QED
Resume evaluate_finite_frame[stmt_expr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      Once evaluate_def, bind_def, return_def, type_check_def, assert_def,
      raise_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED
Resume evaluate_finite_frame[stmts_nil]:
  rpt gen_tac >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[stmts_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s0 x t. eval_stmt cx s s0 = (INL x,t) ==> _` (mk_asm "tail_ih") >>
  qpat_x_assum `!A R env ret_ty env' st res st'. _` (mk_asm "head_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      AllCaseEqs()] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_stmt cx s st` >> rename1 `eval_stmt cx s st = (r1,s1)` >>
  `^safe_accesses A R (accesses_stmt s) (int_calls_stmt s)` by
    (simp[] >> metis_tac[]) >>
  `^safe_accesses A R (accesses_stmts ss) (int_calls_stmts ss)` by
    (simp[] >> metis_tac[]) >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "head_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "head_ih" kall_tac >>
  qpat_x_assum `eval_stmts cx (s::ss) st = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  drule_all (cj 1 eval_scc_type_sound_results_mutual) >> strip_tac >>
  `^typed_state env'' cx s1` by fs[] >>
  `^frame cx A s1 st'` by
    (BETA_TAC >> asm_x "tail_ih" (drule_then (irule o BETA_RULE)) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
  conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE) >>
  first_assum (ACCEPT_TAC o BETA_RULE)

QED
Resume evaluate_finite_frame[iterator_array]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.well_typed_iterator_def, accesses_iterator_def,
      int_calls_iterator_def, Once evaluate_def, bind_def, lift_option_type_def,
      raise_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED
Resume evaluate_finite_frame[iterator_range]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s0 tv1 t s2 v t2.
    eval_expr cx e s0 = (INL tv1,t) /\ read_result cx tv1 s2 = (INL v,t2) ==> _`
    (mk_asm "right_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "left_ih") >>
  gvs[vyperTypeSystemTheory.well_typed_iterator_def, accesses_iterator_def,
      int_calls_iterator_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "left_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "left_ih" kall_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  Cases_on `read_result cx x s1` >> rename1 `read_result cx x s1 = (rr,rs)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `rr`)
  >- (gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  gvs[] >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
  asm_x "right_ih" (drule o REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]) >>
  disch_then drule >> disch_then (mk_asm "right_ih") >>
  Cases_on `eval_expr cx e' rs` >> rename1 `eval_expr cx e' rs = (r2,s2)` >>
  `^frame cx A rs s2` by
    (BETA_TAC >> asm "right_ih" (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `^frame cx A rs s2` (mk_asm "suffix") >>
  asm_x "right_ih" kall_tac >>
  gvs[AllCaseEqs(), lift_sum_def, return_def, raise_def] >>
  imp_res_tac read_result_state >>
  gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `rs` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  asm "suffix" (ACCEPT_TAC o BETA_RULE)
QED
Resume evaluate_finite_frame[for_nil]:
  rpt gen_tac >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED
Resume evaluate_finite_frame[for_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s'' x t. push_scope_with_var _ _ _ s'' = _ ==> _`
    (mk_asm "body_ih") >>
  qpat_x_assum `!s'' x t s0 broke t'. _` (mk_asm "tail_ih") >>
  rename1 `type_stmts (extend_local env id ty F) ret_ty loop_stmts = SOME env_after` >>
  qpat_x_assum `^typed_state env cx st` (strip_assume_tac o BETA_RULE) >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `eval_stmts cx loop_stmts stp` >>
  rename1 `eval_stmts cx loop_stmts stp = (rb,sb)` >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr `stp`] >>
  `^typed_state (extend_local env id ty F) cx stp` by
    (BETA_TAC >> rpt conj_tac
     >- (qunabbrev_tac `stp` >>
         irule vyperTypeEnvPreservationTheory.push_scope_with_var_env_consistent >> gvs[])
     >- (qunabbrev_tac `stp` >>
         `well_formed_type_value tyv` by
           metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
         gvs[EVERY_DEF, state_well_typed_def, scope_well_typed_def,
             finite_mapTheory.FLOOKUP_UPDATE])
     >- first_assum ACCEPT_TAC
     >- simp[Abbr `stp`]
     >> first_assum ACCEPT_TAC) >>
  `^frame cx A stp sb` by
    (BETA_TAC >> asm "body_ih" drule >>
     disch_then (irule o BETA_RULE) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >>
       qpat_x_assum `^safe_accesses A R _ _` (mp_tac o BETA_RULE) >> simp[])) >>
     qpat_x_assum `^safe_accesses A R _ _` (strip_assume_tac o BETA_RULE) >>
     qpat_x_assum `^typed_state (extend_local env id ty F) cx stp`
       (strip_assume_tac o BETA_RULE) >> simp[] >>
     qexistsl_tac [`extend_local env id ty F`,`env_after`,`ret_ty`] >> simp[]) >>
  qpat_x_assum `^frame cx A stp sb` (mk_asm "body_frame") >>
  asm_x "body_ih" kall_tac >>
  qpat_assum `^typed_state (extend_local env id ty F) cx stp`
    (strip_assume_tac o BETA_RULE) >>
  drule_all (cj 2 eval_scc_type_sound_results_mutual) >> strip_tac >>
  `state_well_typed (sb with scopes := TL sb.scopes)` by
    (irule vyperTypeScopePopTheory.scope_bracket_preserves_swt >> simp[] >>
     qexistsl_tac [`cx`,`rb`,`FEMPTY |+ (id,
       <|assignable := F; type := tyv; value := v; popped := []|>)`,
       `loop_stmts`,`st`] >> simp[GSYM (markerTheory.Abbrev_def)] >>
     gvs[Abbr `stp`]) >>
  `env_consistent env cx (sb with scopes := TL sb.scopes)` by
    (Cases_on `rb` >> gvs[]
     >- (irule for_body_env_consistent_after_pop >>
         (conj_tac >- metis_tac[vyperTypeEnvExtensionTheory.env_consistent_env_maps_wf]) >>
         gvs[Abbr `stp`] >> goal_assum (drule_at Any) >> metis_tac[]) >>
     irule for_body_env_extends_consistent_after_pop >>
     (conj_tac >- metis_tac[vyperTypeEnvExtensionTheory.env_consistent_env_maps_wf]) >>
     gvs[Abbr `stp`] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `^frame cx A st (sb with scopes := TL sb.scopes)` by
    (asm "body_frame" mp_tac >>
     simp[Abbr `stp`, oneline get_storage_def]) >>
  qpat_x_assum `^frame cx A st (sb with scopes := TL sb.scopes)` (mk_asm "prefix") >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (rl,sl)` >>
  `sb.scopes <> []` by
    (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
     simp[Abbr `stp`] >> strip_tac >> Cases_on `sb.scopes` >> gvs[]) >>
  `sl = sb with scopes := TL sb.scopes` by
    (qpat_x_assum `finally loop_body pop_scope stp = _` mp_tac >>
     simp[Abbr `loop_body`, finally_def, try_def, bind_def, ignore_bind_def] >>
     Cases_on `rb`
     >- (Cases_on `sb.scopes` >>
         simp[pop_scope_def, return_def, raise_def, AllCaseEqs()]) >>
     rename1 `eval_stmts cx loop_stmts stp = (INR ex,sb)` >>
     Cases_on `ex = ContinueException` >>
     Cases_on `ex = BreakException` >>
     Cases_on `sb.scopes` >>
     gvs[handle_loop_exception_def, pop_scope_def, return_def, raise_def,
         AllCaseEqs()]) >>
  reverse (Cases_on `rl`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  rename1 `finally loop_body pop_scope stp = (INL broke,sl)` >>
  Cases_on `broke` >> simp[return_def]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  `^frame cx A sl st'` by
    (BETA_TAC >>
     asm "tail_ih" (qspecl_then [`st`,`()`,`stp`] mp_tac) >>
     disch_then (qspecl_then [`stp`,`F`,`sl`] mp_tac) >>
     (impl_tac >- (qunabbrev_tac `loop_body` >> gvs[ignore_bind_def])) >>
     disch_then (irule o BETA_RULE) >>
     (conj_tac >- (qexists_tac `R` >> simp[] >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >>
       qpat_x_assum `^safe_accesses A R _ _` (mp_tac o BETA_RULE) >> simp[])) >>
     qpat_x_assum `^safe_accesses A R _ _` (strip_assume_tac o BETA_RULE) >>
     fs[EVERY_DEF] >> qexistsl_tac [`env`,`env_after`,`ret_ty`,`ty`] >>
     gvs[]) >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `sl` >>
  conj_tac >- (gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  first_assum (ACCEPT_TAC o BETA_RULE)
QED

Resume evaluate_finite_frame[raise_custom]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!id positional kwargs tops params es. _` (mk_asm "args_ih") >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- (gvs[Once evaluate_def, raise_def] >> qexists_tac `[]` >> simp[]) >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- (gvs[Once evaluate_def, raise_def] >> qexists_tac `[]` >> simp[]) >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- (gvs[Once evaluate_def, raise_def] >> qexists_tac `[]` >> simp[]) >>
  rename1 `order_custom_error_args params (CustomError p positional kwargs) = SOME es` >>
  `es = custom_error_exprs (CustomError p positional kwargs)` by
    (gvs[vyperASTTheory.order_custom_error_args_def,
         vyperASTTheory.custom_error_exprs_def, AllCaseEqs()] >>
     imp_res_tac vyperASTTheory.order_custom_error_kwargs_SOME >>
     gvs[listTheory.NULL_EQ]) >>
  asm_x "args_ih" (qspecl_then [`p`,`positional`,`kwargs`,`tops`,`params`,`es`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (mk_asm "args_ih") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, vyperTypeSystemTheory.well_typed_custom_error_def,
      accesses_stmt_def, accesses_raise_reason_def, int_calls_stmt_def,
      int_calls_raise_reason_def] >>
  Cases_on `eval_exprs cx (custom_error_exprs (CustomError p positional kwargs)) st` >>
  rename1 `eval_exprs cx _ st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >>
     asm "args_ih" (qspecl_then [`A`,`R`,`env`]
       (qspecl_then [`st`,`r1`,`s1`] mp_tac) o BETA_RULE) >>
     simp[] >> (impl_tac >- asm "closure" (ACCEPT_TAC o SRULE [])) >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "args_ih" kall_tac >>
  gvs[Once evaluate_def, bind_def, lift_option_def, raise_def, return_def,
      AllCaseEqs()] >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
  asm "prefix" (ACCEPT_TAC o BETA_RULE)
QED

Resume evaluate_finite_frame[raise_reason]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      accesses_raise_reason_def, int_calls_raise_reason_def,
      Once evaluate_def, bind_def, raise_def, lift_option_type_def,
      return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[assert_bare]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      accesses_assert_reason_def, int_calls_assert_reason_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, raise_def,
       return_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[assert_reason]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s tv t. eval_expr cx e s = (INL tv,t) ==> _` (mk_asm "reason_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "condition_ih") >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.type_stmt_def, accesses_stmt_def, int_calls_stmt_def,
      accesses_assert_reason_def, int_calls_assert_reason_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >>
     asm "condition_ih" (qspecl_then [`A`,`R`,`env`]
       (qspecl_then [`st`,`r1`,`s1`] mp_tac) o BETA_RULE) >>
     simp[] >> (impl_tac >- asm "closure" (ACCEPT_TAC o SRULE [])) >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "condition_ih" kall_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, raise_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >>
  asm_x "reason_ih" drule >> disch_then (mk_asm "reason_ih") >>
  gvs[AllCaseEqs()] >> imp_res_tac read_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  (asm "prefix" (ACCEPT_TAC o BETA_RULE) ORELSE
   (qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
      (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >>
    gvs[] >>
    rename1 `eval_expr cx e st = (INL x,s1)` >>
    Cases_on `eval_expr cx e' s1` >>
    rename1 `eval_expr cx e' s1 = (r2,s2)` >>
    `^frame cx A s1 s2` by
      (BETA_TAC >>
       asm "reason_ih" (qspecl_then [`A`,`R`,`env`]
         (qspecl_then [`s1`,`r2`,`s2`] mp_tac) o BETA_RULE) >>
       simp[] >> (impl_tac >- asm "closure" (ACCEPT_TAC o SRULE [])) >> simp[]) >>
    qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
    asm_x "reason_ih" kall_tac >>
    gvs[bind_def, lift_option_type_def, raise_def, return_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> gvs[] >>
    gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def] >>
    irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
    (conj_tac >- asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
    asm "suffix" (ACCEPT_TAC o BETA_RULE)))
QED

Resume evaluate_finite_frame[risky_Send]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `^safe_accesses A R (accesses_expr _) _` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Resume evaluate_finite_frame[risky_ExtCall]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `^safe_accesses A R (accesses_expr _) _` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Resume evaluate_finite_frame[risky_RawCallTarget]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `^safe_accesses A R (accesses_expr _) _` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Resume evaluate_finite_frame[risky_RawCallCalldataTarget]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `^safe_accesses A R (accesses_expr _) _` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Resume evaluate_finite_frame[risky_CreateTarget]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `^safe_accesses A R (accesses_expr _) _` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Resume evaluate_finite_frame[rawrevert]:
  rpt gen_tac >> disch_then (mk_asm "args_ih") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, risky_call_target_def, int_calls_expr_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, raise_def, AllCaseEqs()] >>
  asm "args_ih" (irule o BETA_RULE) >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[rawlog]:
  rpt gen_tac >> disch_then (mk_asm "args_ih") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, risky_call_target_def, int_calls_expr_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (arg_res,arg_st)` >>
  `^frame cx A st arg_st` by
    (BETA_TAC >> asm "args_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `^frame cx A st arg_st`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac (BETA_RULE th)) >>
  Cases_on `arg_res` >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, raise_def, lift_option_type_def, check_not_static_def,
      push_log_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def, check_def] >>
  rpt strip_tac >> gvs[assert_def, return_def, raise_def, AllCaseEqs()] >>
  qexists_tac `ws` >> gvs[oneline get_storage_def] >> gvs[]
QED

Resume evaluate_finite_frame[selfdestruct]:
  rpt gen_tac >> disch_then (mk_asm "args_ih") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, risky_call_target_def, int_calls_expr_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (arg_res,arg_st)` >>
  `^frame cx A st arg_st` by
    (BETA_TAC >> asm "args_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `^frame cx A st arg_st`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac (BETA_RULE th)) >>
  Cases_on `arg_res` >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, raise_def, lift_option_type_def, check_not_static_def,
      get_accounts_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def, check_def] >>
  rpt strip_tac >> gvs[assert_def, return_def, raise_def, AllCaseEqs()] >>
  qexists_tac `ws` >> simp[] >>
  gvs[transfer_value_def, COND_RATOR, bind_def, ignore_bind_def, get_accounts_def,
      check_def, assert_def, update_accounts_def, return_def, raise_def,
      AllCaseEqs()] >>
  gvs[oneline get_storage_def, vfmStateTheory.update_account_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  gvs[]
QED

Resume evaluate_finite_frame[intcall]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "body_ih")
    (CONJUNCTS_THEN2 (mk_asm "defaults_ih") (mk_asm "arguments_ih"))) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac (srw_ss()) [bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[type_check_def, assert_def, raise_def] >>
      qexists_tac `[]` >> simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[lift_option_type_def, raise_def, return_def, AllCaseEqs()] >>
      qexists_tac `[]` >> simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[lift_option_type_def, raise_def, return_def, AllCaseEqs()] >>
      qexists_tac `[]` >> simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[type_check_def, assert_def, raise_def] >>
      qexists_tac `[]` >> simp[]) >>
  asm_x "arguments_ih" (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `type_check _ "IntCall args length" _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (mk_asm "arguments_frame") >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_mono >> goal_assum (drule_at Any) >>
     simp[int_calls_expr_def]) >>
  gvs[accesses_expr_def, int_calls_expr_def, risky_call_target_def] >>
  Cases_on `eval_expr_results cx es r` >>
  rename1 `eval_expr_results cx es r = (args_res,args_st)` >>
  `^frame cx A r args_st` by
    (BETA_TAC >> rewrite_tac [GSYM AND_IMP_INTRO] >>
     asm "arguments_frame" irule >>
     asm_x "body_ih" kall_tac >> asm_x "defaults_ih" kall_tac >>
     asm_x "arguments_frame" kall_tac >> simp[] >>
     (conj_tac >-
       (qexists_tac `R` >> conj_tac
        >- asm "closure" (ACCEPT_TAC o SRULE [GSYM AND_IMP_INTRO]) >>
        metis_tac[])) >>
     metis_tac[]) >>
  qpat_x_assum `^frame cx A r args_st` (mk_asm "args_prefix") >>
  asm_x "arguments_frame" kall_tac >>
  reverse (Cases_on `args_res`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "args_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  rename1 `eval_expr_results cx es r = (INL results,args_st)` >>
  qspecl_then [`cx`,`es`] (drule_all o CONJUNCT1)
    (cj 11 eval_scc_type_sound_results_mutual) >> strip_tac >>
  qpat_assum `lift_option_type (get_module_code cx src_id_opt) _ _ = _`
    (strip_assume_tac o SRULE [lift_option_type_def, option_CASE_rator, AllCaseEqs(), return_def, raise_def]) >>
  qpat_assum `lift_option_type (lookup_callable_function cx.in_deploy fn _) _ _ = _`
    (strip_assume_tac o SRULE [lift_option_type_def, option_CASE_rator, AllCaseEqs(), return_def, raise_def]) >>
  PairCases_on `x''` >>
  RULE_ASSUM_TAC (BETA_RULE o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) []) >>
  `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by simp[] >>
  drule_all callable_body_typing_from_env_consistent >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
      (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
  simp_tac (srw_ss()) [get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >>
  `get_scopes args_st = (INL args_st.scopes,args_st)` by
    simp[get_scopes_def, return_def] >>
  `set_scopes [FEMPTY] args_st = (INL (),args_st with scopes := [FEMPTY])` by
    simp[set_scopes_def, return_def] >>
  asm_x "defaults_ih" (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  simp_tac (srw_ss()) [] >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (mk_asm "defaults_frame") >>
  drule_all intcall_default_env_side_conditions >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  `env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn))
      (args_st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (args_st with scopes := [FEMPTY])` by
    (qpat_assum `state_well_typed args_st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[state_well_typed_def, scope_well_typed_def]) >>
  `well_typed_exprs (defaults_env env_body)
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)` by
    (irule well_typed_exprs_DROP >> simp[]) >>
  `call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
      (int_calls_exprs (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3))` by
    (irule call_evaluation_safe_push_needed_defaults >>
     asm_x "body_ih" kall_tac >> asm_x "defaults_frame" kall_tac >>
     asm_x "closure" kall_tac >> asm_x "args_prefix" kall_tac >>
     conj_tac >- metis_tac[] >> metis_tac[]) >>
  `MEM (src_id_opt,fn) R` by simp[] >>
  asm "closure" (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  disch_then (mk_asm "callee_accesses") >>
  `^safe_accesses A R
      (accesses_exprs (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3))
      (int_calls_exprs (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3))` by
    (asm "callee_accesses" mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     qsuff_tac `!n ds. (^safe_accesses A R (accesses_exprs ds)
         (int_calls_exprs ds)) ==> ^safe_accesses A R
         (accesses_exprs (DROP n ds)) (int_calls_exprs (DROP n ds))`
     >- (simp[function_int_calls_def, MEM_APPEND] >> metis_tac[]) >>
     Induct >> Cases_on `ds` >>
     simp[accesses_expr_def, int_calls_expr_def, MEM_APPEND] >> metis_tac[]) >>
  Cases_on `eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)
      (args_st with scopes := [FEMPTY])` >>
  rename1 `eval_exprs _ _ (args_st with scopes := [FEMPTY]) = (dres,dst)` >>
  `^frame cx A (args_st with scopes := [FEMPTY]) dst` by
    (asm "defaults_frame" (qspecl_then [`A`,`R`,`defaults_env env_body`]
       (qspecl_then [`args_st with scopes := [FEMPTY]`,`dres`,`dst`] mp_tac)) >>
     (impl_tac >-
       (asm_x "body_ih" kall_tac >> asm_x "defaults_frame" kall_tac >>
        asm_x "args_prefix" kall_tac >> asm_x "callee_accesses" kall_tac >>
        fs[] >>
        asm "closure" (mp_tac o SRULE [GSYM AND_IMP_INTRO, MEM_APPEND]) >>
        simp[get_module_code_def])) >>
     simp[oneline get_storage_def, GSYM AND_IMP_INTRO]) >>
  qpat_x_assum `^frame cx A (args_st with scopes := [FEMPTY]) dst`
    (mk_asm "defaults_prefix") >>
  asm_x "defaults_frame" kall_tac >>
  qpat_x_assum `finally _ (set_scopes args_st.scopes) args_st = _` mp_tac >>
  simp[finally_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  reverse (Cases_on `dres`) >> simp[raise_def, return_def]
  >- (strip_tac >> gnvs[] >> strip_tac >> gnvs[] >>
      irule (BETA_RULE finite_frame_trans) >> qexists_tac `args_st` >>
      (conj_tac >- asm "args_prefix" (ACCEPT_TAC o BETA_RULE)) >>
      asm "defaults_prefix" mp_tac >>
      simp[oneline get_storage_def]) >>
  strip_tac >>
  gnvs[] >>
  `^frame cx A r (dst with scopes := args_st.scopes)` by
    (BETA_TAC >> irule (BETA_RULE finite_frame_trans) >> qexists_tac `args_st` >>
     (conj_tac >- asm "args_prefix" (ACCEPT_TAC o BETA_RULE)) >>
     asm "defaults_prefix" mp_tac >> simp[oneline get_storage_def]) >>
  qpat_x_assum `^frame cx A r (dst with scopes := args_st.scopes)`
    (mk_asm "call_prefix") >>
  `accounts_well_typed (args_st with scopes := [FEMPTY]).accounts` by simp[] >>
  drule_all (CONJUNCT1 (SPEC_ALL (cj 6 eval_scc_type_sound_results_mutual))) >>
  strip_tac >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac read_results_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gnvs[] >> asm "call_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gnvs[] >> asm "call_prefix" (ACCEPT_TAC o BETA_RULE)) >>
  rename1 `lift_option_type (bind_arguments _ _ _) _ _ = (INL call_env,_)` >>
  qpat_assum `lift_option_type (bind_arguments _ _ _) _ _ = _`
    (strip_assume_tac o SRULE [lift_option_type_def, option_CASE_rator,
      AllCaseEqs(), return_def, raise_def]) >>
  `scope_well_typed call_env` by
    (drule vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success >>
     simp[]) >>
  `state_well_typed (dst with scopes := args_st.scopes)` by
    (fs[state_well_typed_def]) >>
  `env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dst with scopes := [call_env])` by
    (irule vyperTypeBindArgumentsTheory.bind_arguments_env_scopes_consistent >>
     qexistsl_tac [`x''2`,`get_tenv cx`,`x'' ++ x`] >>
     simp[get_tenv_def] >> rpt strip_tac >>
     qpat_x_assum `!id typ. MEM (id,typ) x''2 ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dst with scopes := args_st.scopes)` by
    (qpat_assum `env_consistent (defaults_env env_body) _ dst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[env_consistent_def, vyperTypeSystemTheory.defaults_env_def,
          env_immutables_consistent_def] >> metis_tac[]) >>
  once_rewrite_tac [GSYM is_view_mut_def] >>
  once_rewrite_tac [GSYM ignore_bind_def] >>
  once_rewrite_tac [GSYM lock_if_nr_def] >>
  BasicProvers.TOP_CASE_TAC >>
  rename1 `lock_if_nr cx _ _ _ = (lock_res,lock_st)` >>
  `^frame cx A (dst with scopes := args_st.scopes) lock_st` by
    (BETA_TAC >> qexists_tac `[]` >> simp[] >> rpt strip_tac >>
     qpat_assum `lock_if_nr cx _ _ _ = (lock_res,lock_st)`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lock_if_nr_word_frame)) >>
     simp[]) >>
  `^frame cx A r lock_st` by
    (BETA_TAC >> irule (BETA_RULE finite_frame_trans) >>
     qexists_tac `dst with scopes := args_st.scopes` >>
     conj_tac >- asm "call_prefix" (ACCEPT_TAC o BETA_RULE) >>
     first_assum (ACCEPT_TAC o BETA_RULE)) >>
  reverse (Cases_on `lock_res`) >> simp[raise_def, return_def]
  >- (strip_tac >> gnvs[] >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
  rename1 `lock_if_nr cx _ _ _ = (INL lock_value,lock_st)` >>
  Cases_on `lock_value` >>
  `accounts_well_typed (dst with scopes := args_st.scopes).accounts` by simp[] >>
  `env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      ((dst with scopes := args_st.scopes) with scopes := [call_env])` by simp[] >>
  qpat_assum `lock_if_nr cx _ _ _ = (INL _,lock_st)`
    (assume_tac o REWRITE_RULE [lock_if_nr_def]) >>
  drule_all intcall_live_pushed_body_preconditions >> strip_tac >>
  simp_tac (srw_ss()) [push_function_def, return_def] >>
  `lift_option_type (get_module_code cx env_body.current_src)
     "IntCall get_module_code" r = (INL x',r)` by
    simp[lift_option_type_def, return_def] >>
  `lift_option_type (lookup_callable_function cx.in_deploy fn x')
     "IntCall lookup_function" r =
       (INL (x''0,x''1,x''2,x''3,x''4,x''5),r)` by
    simp[lift_option_type_def, return_def] >>
  asm_x "body_ih" (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  simp_tac (srw_ss()) [] >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  `finally (ignore_bind (set_scopes [FEMPTY])
      (eval_exprs (cx with stk updated_by CONS (env_body.current_src,fn))
        (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)))
      (set_scopes args_st.scopes) args_st =
      (INL x,dst with scopes := args_st.scopes)` by
    simp[finally_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  `lift_option_type (evaluate_type (get_tenv cx) x''4)
      "IntCall eval ret" r = (INL ret_tv,r)` by
    simp[lift_option_type_def, return_def] >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  pure_once_rewrite_tac [GSYM is_view_mut_def] >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  `push_function (env_body.current_src,fn) call_env cx lock_st =
      (INL (cx with stk updated_by CONS (env_body.current_src,fn)),
       lock_st with scopes := [call_env])` by
    simp[push_function_def, return_def] >>
  disch_then (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (mk_asm "body_frame" o REWRITE_RULE [AND_IMP_INTRO] o BETA_RULE) >>
  `call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts x''5)` by
    (irule call_evaluation_safe_push_body >>
     asm_x "body_frame" kall_tac >> asm_x "closure" kall_tac >>
     asm_x "callee_accesses" kall_tac >> asm_x "args_prefix" kall_tac >>
     metis_tac[]) >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn))
      x''5 (lock_st with scopes := [call_env])` >>
  rename1 `eval_stmts _ x''5 _ = (body_res,body_st)` >>
  `^frame cx A (lock_st with scopes := [call_env]) body_st` by
    (asm "body_frame" (qspecl_then [`A`,`R`,`env_body`,`x''4`]
       (qspecl_then [`env_after`,`lock_st with scopes := [call_env]`,
                    `body_res`,`body_st`] mp_tac)) >>
     (impl_tac >-
       (asm_x "body_frame" kall_tac >> asm_x "args_prefix" kall_tac >>
        asm_x "defaults_prefix" kall_tac >> asm_x "call_prefix" kall_tac >>
        fs[] >>
        asm "closure" (mp_tac o SRULE [GSYM AND_IMP_INTRO, MEM_APPEND]) >>
        asm "callee_accesses" mp_tac >>
        simp[get_module_code_def, function_int_calls_def] >> metis_tac[])) >>
     simp[oneline get_storage_def, CONJ_ASSOC]) >>
  `^frame cx A r body_st` by
    (BETA_TAC >> irule (BETA_RULE finite_frame_trans) >>
     qexists_tac `lock_st with scopes := [call_env]` >> conj_tac
     >- (qpat_assum `^frame cx A r lock_st` (mp_tac o BETA_RULE) >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[oneline get_storage_def]) >>
     first_assum (ACCEPT_TAC o BETA_RULE)) >>
  qpat_x_assum `^frame cx A r body_st` (mk_asm "body_prefix") >>
  simp[try_def, ignore_bind_def, bind_def] >>
  Cases_on `body_res` >> simp[return_def] >>
  TRY (rename1 `handle_function ex body_st` >> Cases_on `ex`) >>
  simp[handle_function_def, return_def, raise_def, pop_function_def,
       set_scopes_def] >>
  once_rewrite_tac [GSYM DE_MORGAN_THM] >>
  once_rewrite_tac [GSYM is_view_mut_def] >>
  once_rewrite_tac [GSYM unlock_if_nr_def] >>
  Cases_on `unlock_if_nr cx x''1 (is_view_mut x''0)
      (body_st with scopes := args_st.scopes)` >>
  rename1 `unlock_if_nr cx _ _ _ = (unlock_res,unlock_st)` >>
  `^frame cx A (body_st with scopes := args_st.scopes) unlock_st` by
    (BETA_TAC >> qexists_tac `[]` >> simp[] >> rpt strip_tac >>
     qpat_assum `unlock_if_nr cx _ _ _ = (unlock_res,unlock_st)`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] unlock_if_nr_word_frame)) >>
     simp[]) >>
  `^frame cx A r unlock_st` by
    (BETA_TAC >> irule (BETA_RULE finite_frame_trans) >>
     qexists_tac `body_st with scopes := args_st.scopes` >> conj_tac
     >- (asm "body_prefix" (mp_tac o BETA_RULE) >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[oneline get_storage_def]) >>
     first_assum (ACCEPT_TAC o BETA_RULE)) >>
  simp[] >>
  qpat_assum `^frame cx A r unlock_st`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac (BETA_RULE th)) >>
  Cases_on `unlock_res` >> simp[] >>
  simp[lift_option_type_def, option_CASE_rator, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qexists_tac `ws` >> simp[] >> gvs[]
QED

Resume evaluate_finite_frame[results_nil]:
  rpt gen_tac >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[results_cons]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_ih") (mk_asm "head_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def, accesses_expr_def, int_calls_expr_def,
      safe_accesses_append] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "head_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "head_ih" kall_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o BETA_RULE)) >>
  strip_tac >> asm_x "tail_ih" drule >> disch_then (mk_asm "tail_ih") >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
  Cases_on `eval_expr_results cx es s1` >>
  rename1 `eval_expr_results cx es s1 = (r2,s2)` >>
  `^frame cx A s1 s2` by
    (BETA_TAC >> asm "tail_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
  gvs[AllCaseEqs()] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  asm "suffix" (ACCEPT_TAC o SRULE [])
QED

Resume evaluate_finite_frame[target_place]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.well_typed_target_def,
      Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[exprs_nil]:
  rpt gen_tac >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[exprs_cons]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_ih") (mk_asm "head_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def, accesses_expr_def, int_calls_expr_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "head_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "head_ih" kall_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  strip_tac >>
  Cases_on `read_result cx x s1` >> rename1 `read_result cx x s1 = (rr,sr)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `rr`) >> gvs[bind_def]
  >- asm "prefix" (ACCEPT_TAC o SRULE []) >>
  asm_x "tail_ih" drule >> disch_then drule >> disch_then (mk_asm "tail_ih") >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
  Cases_on `eval_exprs cx es s1` >> rename1 `eval_exprs cx es s1 = (r2,s2)` >>
  `^frame cx A s1 s2` by
    (BETA_TAC >> asm "tail_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
  gvs[AllCaseEqs(), return_def] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  asm "suffix" (ACCEPT_TAC o SRULE [])
QED

Resume evaluate_finite_frame[base_name]:
  rpt gen_tac >> simp[Once evaluate_def, get_scopes_def, bind_def,
      type_check_def, ignore_bind_def, assert_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[base_global]:
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def] >>
  drule lookup_global_state >> strip_tac >> gvs[] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[base_attr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def,
      Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[base_subscript]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "index_ih") (mk_asm "base_ih")) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def, safe_accesses_append, AllCaseEqs()] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "base_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "base_ih" kall_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  strip_tac >>
  asm_x "index_ih" drule >> disch_then (mk_asm "index_ih") >>
  qspecl_then [`cx`,`bt`] (drule_all o CONJUNCT1)
    (cj 7 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
  Cases_on `eval_expr cx e s1` >> rename1 `eval_expr cx e s1 = (r2,s2)` >>
  `^frame cx A s1 s2` by
    (BETA_TAC >> asm "index_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> conj_tac
       >- asm "closure" (ACCEPT_TAC o SRULE []) >> simp[])) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
  irule (BETA_RULE finite_frame_trans) >> qexists_tac `s1` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  asm "suffix" (ACCEPT_TAC o SRULE [])
QED

Resume evaluate_finite_frame[expr_name]:
  rpt gen_tac >> simp[Once evaluate_def, get_scopes_def, bind_def,
      type_check_def, ignore_bind_def, assert_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_global]:
  rpt gen_tac >> strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_global_state >> strip_tac >> gvs[] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_flag]:
  rpt gen_tac >> strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_flag_mem_state >> strip_tac >> gvs[] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_literal]:
  rpt gen_tac >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_attr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def,
      Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[expr_struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes /\
   accesses_exprs (MAP SND kes) = accesses_named_exprs kes` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `kes` >>
     simp[int_calls_expr_def, accesses_expr_def] >>
     gen_tac >> PairCases_on `h` >> simp[int_calls_expr_def, accesses_expr_def]) >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def,
      Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  drule well_typed_named_exprs_MAP_SND_stmt >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  (conj_tac >- (qexists_tac `R` >> conj_tac
    >- first_assum ACCEPT_TAC >> simp[])) >>
  qexists_tac `env` >> simp[]
QED

Resume evaluate_finite_frame[expr_typebuiltin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s'' x t. _` (mk_asm "args_ih") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def] >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)`
  >- (Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (r1,s1)` >>
      `^frame cx A st s1` by
        (BETA_TAC >>
         asm "args_ih" (qspecl_then [`st`,`()`,`st`] mp_tac) >>
         simp[type_check_def, assert_def, return_def] >>
         disch_then (irule o BETA_RULE) >> goal_assum (drule_at Any) >> simp[] >>
         (conj_tac >- (qexists_tac `R` >> simp[] >>
           asm "closure" (ACCEPT_TAC o SRULE []))) >>
         qexists_tac `env` >> simp[]) >>
      qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
      asm_x "args_ih" kall_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, return_def,
          ignore_bind_def, bind_def, raise_def, AllCaseEqs()] >>
      Cases_on `evaluate_type_builtin cx tb typ (MAP expr_type es) vs` >>
      gvs[lift_sum_def, return_def, raise_def] >>
      asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  gvs[Once evaluate_def, type_check_def, assert_def, raise_def,
      ignore_bind_def, bind_def] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s'' x t. _ /\ bt <> Len /\ _ ==> _` (mk_asm "args_ih") >>
  qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _` (mk_asm "len_ih") >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def, accesses_expr_def, int_calls_expr_def] >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len`
      >- suspend "builtin_len" >>
      Cases_on `bt = Env MsgGas`
      >- suspend "builtin_gas" >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (r1,s1)` >>
      `^frame cx A st s1` by
        (BETA_TAC >>
         asm "args_ih" (qspecl_then [`st`,`()`,`st`] mp_tac) >>
         simp[type_check_def, assert_def, return_def] >>
         disch_then (irule o BETA_RULE) >> goal_assum (drule_at Any) >> simp[] >>
         (conj_tac >- (qexists_tac `R` >> simp[] >>
           asm "closure" (ACCEPT_TAC o SRULE []))) >>
         qexists_tac `env` >> simp[]) >>
      qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
      asm_x "args_ih" kall_tac >> asm_x "len_ih" kall_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, return_def,
          ignore_bind_def, bind_def, raise_def, get_accounts_def, AllCaseEqs()] >>
      imp_res_tac precompile_call_success_state >>
      imp_res_tac lift_sum_state >>
      gvs[return_def, raise_def, bind_def, oneline get_storage_def] >>
      asm "prefix" (ACCEPT_TAC o SRULE [oneline get_storage_def])) >>
  gvs[Once evaluate_def, type_check_def, assert_def, raise_def,
      ignore_bind_def, bind_def] >> qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[builtin_len]:
  asm_x "args_ih" kall_tac >>
  Cases_on `es` >>
  gvs[vyperTypeSystemTheory.well_typed_builtin_app_def,
      vyperTypeSystemTheory.well_typed_expr_def,
      accesses_expr_def, int_calls_expr_def] >>
  Cases_on `eval_expr cx h st` >>
  rename1 `eval_expr cx h st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >>
     asm "len_ih" (qspecl_then [`st`,`()`,`st`] mp_tac) >>
     simp[type_check_def, assert_def, return_def] >>
     disch_then (irule o BETA_RULE) >> goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "len_ih" kall_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, return_def,
      ignore_bind_def, bind_def, raise_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  gvs[return_def, raise_def] >>
  asm "prefix" (ACCEPT_TAC o SRULE [])
QED

Resume evaluate_finite_frame[builtin_gas]:
  asm_x "args_ih" kall_tac >> asm_x "len_ih" kall_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, return_def,
      ignore_bind_def, bind_def, raise_def, AllCaseEqs()] >>
  imp_res_tac next_gas_reading_state >>
  gvs[return_def, raise_def, oneline get_storage_def] >>
  qexists_tac `[]` >> simp[]
QED

Resume evaluate_finite_frame[expr_ifexp]:
  (* Diagnostic attempt: global gvs[well_typed_expr_def] timed out.
     Targeted well_typed_expr rewriting reaches only one of the two
     RESUME_TAC goals; the other has a type_place_expr premise.
     rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
     qpat_x_assum `well_typed_expr env (IfExp _ _ _ _)` mp_tac >>
     simp_tac (srw_ss()) [Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[accesses_expr_def, int_calls_expr_def]
  *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s tv t. _ ==> !A R env st res st'. (well_typed_expr env e' \/ _) /\ _ ==> _`
    (mk_asm "then_ih") >>
  qpat_x_assum `!s tv t. _ ==> !A R env st res st'. (well_typed_expr env e'' \/ _) /\ _ ==> _`
    (mk_asm "else_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "cond_ih") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[accesses_expr_def, int_calls_expr_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_left] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "cond_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "cond_ih" kall_tac >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[switch_BoolV_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  FIRST [asm "prefix" (ACCEPT_TAC o SRULE []),
    (qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
       (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
     FIRST [
       (qpat_assum `eval_expr cx e' _ = _` kall_tac >>
        asm_x "else_ih" kall_tac >>
        asm_x "then_ih" drule >> disch_then (mk_asm "branch_ih")),
       (qpat_assum `eval_expr cx e'' _ = _` kall_tac >>
        asm_x "then_ih" kall_tac >>
        asm_x "else_ih" drule >> disch_then (mk_asm "branch_ih"))] >>
     rename1 `eval_expr cx e st = (INL tv,s1)` >>
     irule (SRULE [] finite_frame_trans) >> qexists_tac `s1` >>
     (conj_tac >- asm "prefix" (ACCEPT_TAC o SRULE [])) >>
     asm "branch_ih" (irule o SRULE []) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     qexists_tac `env` >> simp[])]
QED

Resume evaluate_finite_frame[expr_subscript]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `^callable_closed cx A R` (mk_asm "closure") >>
  qpat_x_assum `!s tv t. _ ==> _` (mk_asm "index_ih") >>
  qpat_x_assum `!A R env st res st'. _` (mk_asm "base_ih") >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[accesses_expr_def, int_calls_expr_def] >>
  gvs[Once vyperTypeSystemTheory.well_typed_expr_def, AllCaseEqs()] >>
  (drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (r1,s1)` >>
  `^frame cx A st s1` by
    (BETA_TAC >> asm "base_ih" (irule o BETA_RULE) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A st s1` (mk_asm "prefix") >>
  asm_x "base_ih" kall_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  reverse (Cases_on `r1`) >> simp[]
  >- (strip_tac >> gvs[] >> asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  strip_tac >>
  rename1 `eval_expr cx e st = (INL pv,s1)` >>
  asm_x "index_ih" (qspecl_then [`st`,`pv`,`s1`] mp_tac) >>
  simp[] >> disch_then (mk_asm "index_ih") >>
  qspecl_then [`cx`,`e`] (drule_all o CONJUNCT1)
    (cj 5 eval_scc_type_sound_results_mutual) >> strip_tac >> gvs[] >>
  Cases_on `eval_expr cx e' s1` >> rename1 `eval_expr cx e' s1 = (r2,s2)` >>
  `^frame cx A s1 s2` by
    (BETA_TAC >> asm "index_ih" (irule o SRULE []) >>
     goal_assum (drule_at Any) >> simp[] >>
     (conj_tac >- (qexists_tac `R` >> simp[] >>
       asm "closure" (ACCEPT_TAC o SRULE []))) >>
     qexists_tac `env` >> simp[]) >>
  qpat_x_assum `^frame cx A s1 s2` (mk_asm "suffix") >>
  asm_x "index_ih" kall_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  irule (SRULE [] finite_frame_trans) >> qexists_tac `s1` >>
  (conj_tac >- asm "prefix" (ACCEPT_TAC o SRULE [])) >>
  asm "suffix" (ACCEPT_TAC o SRULE []))
QED

Finalise evaluate_finite_frame

Theorem eval_expr_unwritten_storage:
  !cx e st res st' env mods.
    eval_expr cx e st = (res,st') /\
    well_typed_expr env e /\ env_consistent env cx st /\
    state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (!src fn ts mut nr args dflts ret body.
       MEM (src,fn) (reached_functions mods e) /\
       get_module_code cx src = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts =
         SOME (mut,nr,args,dflts,ret,body) ==>
       ALOOKUP mods src = SOME ts /\
       (find_function fn ts = SOME (dflts,body) \/
        (dflts = [] /\ body = []))) /\
    ~MEM RiskyAcc (expr_accesses mods e) ==>
    ?ws.
      EVERY (\(mid,n,subs).
               MEM (WriteAcc (StateRef (mid,n))) (expr_accesses mods e)) ws /\
      !tr k.
        (!mid n subs slot tv i.
           MEM (mid,n,subs) ws /\
           declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
           i < type_slot_size tv ==>
           k <> slot + n2w i) /\
        (tr ==> !lock. cx.nonreentrant_slot = SOME lock ==> k <> n2w lock) ==>
        lookup_storage k (get_storage cx st' tr) =
        lookup_storage k (get_storage cx st tr)
Proof
  rpt strip_tac >>
  drule_all callable_closed_initial >> strip_tac >>
  drule safe_accesses_expr_initial >> strip_tac >>
  qspecl_then [`cx`,`e`] (irule o BETA_RULE) (cj 5 evaluate_finite_frame) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `reached_functions mods e` >>
  qexistsl_tac [`e`,`env`,`res`] >> gvs[] >> first_assum ACCEPT_TAC
QED
