(* Storage preservation for the mutually recursive evaluator. *)

Theory vyperTypeEvalStoragePreservation
Ancestors
  pair list vyperAST vyperCreate vyperInterpreter vyperState vyperStorageBackend vyperStorageLayoutSafety
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperTypeValues vyperTypeCallGraph
  vyperEvalMisc vyperStatePreservation vyperScopePreservation
  vyperTypeCallStackSoundness vyperValue
  vyperTypeBuiltins vyperTypeExprResult vyperTypeExprSoundness vyperTypeEvalSoundness
  vyperTypeExtCallSoundness vyperTypeABI vyperTypeEnvPreservation vyperTypeStatePreservation
  vyperTypeStmtSoundness vyperTypeAssignContext vyperTypeStoragePreservation
  vyperTypeBindArguments vyperEvalOutcomeSuffix vyperCallOutcomeStorage vyperTypeArgFits
  vyperPlaceStoragePreservation vyperPlaceFrames vyperPlaceTyping
  vyperStoragePlaceProvenance
  vyperPlaceResultTyping vyperTargetPlaceWrite vyperAugAssignWriteSoundness
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperCallOutcome[ignore_grammar]
  vyperSourceSupplyDefs vyperSourceSupplyFields vyperEvalSupply
Libs
  wordsLib markerLib BasicProvers vyperSourceSupplyLib

(* Storage proofs use the same explicit physical domain as evaluator typing.
   Forward it through actual evaluation equations without changing the
   established storage/runtime consistency predicates or conclusions. *)
val storage_gvs = gvs;
val storage_fs = fs;
val storage_drule_all = drule_all;
val storage_impl_tac = impl_tac;
fun gvs thms = vyperSourceSupplyLib.forward >> storage_gvs thms >>
  vyperSourceSupplyLib.forward;
fun fs thms = vyperSourceSupplyLib.forward >> storage_fs thms >>
  vyperSourceSupplyLib.forward;
fun drule_all th = vyperSourceSupplyLib.forward >> storage_drule_all th;
val impl_tac = vyperSourceSupplyLib.forward >> storage_impl_tac;

fun ORACLE_STORAGE_TAC (asl,w) =
  let
    fun head tm = fst (dest_const (fst (strip_comb tm))) handle HOL_ERR _ => "";
    val names = ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
      "eval_expr", "eval_exprs", "eval_base_place", "eval_target_place",
      "assign_tuple_targets", "assign_tuple_target_list", "eval_expr_results"];
    fun position n [] = 12
      | position n (h::t) = if n = h then 1 else 1 + position n t;
    fun suffix tm =
      let val (lhs,_) = dest_eq tm
          val i = position (head lhs) names
      in if i = 11 then SOME
           (MATCH_MP eval_expr_results_outcome_suffix (ASSUME tm))
         else if i > 11 then NONE
         else SOME (MATCH_MP (cj i eval_outcome_suffix_mutual) (ASSUME tm))
      end handle HOL_ERR _ => NONE;
    val state_ty = ``:evaluation_state``;
    val outcomes_ty = type_of ``(s:evaluation_state).outcomes``;
    fun state_eq tm = is_eq tm andalso
      (type_of (lhs tm) = state_ty orelse type_of (lhs tm) = outcomes_ty);
    fun uniq ts = List.foldl (fn (t,acc) =>
      if List.exists (aconv t) acc then acc else t::acc) [] ts;
    val eqs = List.map ASSUME (List.filter state_eq asl);
    val suffixes = List.map (SIMP_RULE (srw_ss()) eqs)
      (List.map ASSUME (List.filter (fn tm => head tm = "outcome_suffix") asl) @
       List.mapPartial suffix asl);
    val parents = List.filter (fn tm => head tm = "oracle_storage_ok") asl;
    fun states tm =
      if head tm = "runtime_storage_consistent" then [List.last (snd (strip_comb tm))]
      else if is_eq tm then
        let val (l,r) = dest_eq tm val (_,s) = pairSyntax.dest_pair r
        in if type_of s = state_ty then [rand l,s] else [] end
        handle HOL_ERR _ => []
      else [];
    val needed = List.map (List.last o snd o strip_comb)
      (find_terms (fn tm => head tm = "oracle_storage_ok" andalso
        List.length (snd (strip_comb tm)) = 2) w);
    val candidates = uniq
      (if null needed then List.concat (List.map states asl) else needed);
    fun transport p target =
      let val [cx,st] = snd (strip_comb p)
          val selector = rator ``(s:evaluation_state).outcomes``
          val goal = list_mk_icomb (``outcome_suffix``,
            [mk_comb (selector,st), mk_comb (selector,target)])
          val proof = EQT_ELIM (SIMP_CONV (srw_ss()) (eqs @ suffixes) goal)
      in SOME (MATCH_MP oracle_storage_ok_suffix (CONJ (ASSUME p) proof)) end
      handle HOL_ERR _ => NONE | Match => NONE | UNCHANGED => NONE;
    val facts = List.concat (List.map (fn p => List.mapPartial (transport p) candidates) parents);
  in MAP_EVERY (fn th => fn g =>
       if List.exists (aconv (concl th)) (fst g) then ALL_TAC g else ASSUME_TAC th g)
       facts (asl,w) end;

(* Primitive nonreentrant-lock boundary facts.  These expose the exact
   transient write before the evaluator proof uses layout separation. *)

Theorem acquire_nonreentrant_lock_eq:
  acquire_nonreentrant_lock addr slot is_view st =
    if lookup_storage (n2w slot)
         (lookup_transient_storage addr st.tStorage) = 1w then
      (INR (Error (RuntimeError "nonreentrant lock")),st)
    else if is_view then (INL (),st)
    else
      (INL (),
       st with tStorage updated_by
         update_transient_storage addr
           (update_storage (n2w slot) 1w
             (lookup_transient_storage addr st.tStorage)))
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def, raise_def]
QED

Theorem release_nonreentrant_lock_eq:
  release_nonreentrant_lock addr slot st =
    (INL (),
     st with tStorage updated_by
       update_transient_storage addr
         (update_storage (n2w slot) 0w
           (lookup_transient_storage addr st.tStorage)))
Proof
  simp[release_nonreentrant_lock_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def]
QED

Theorem acquire_nonreentrant_lock_frame:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.accounts = st.accounts /\
  (!read_addr read_slot.
     read_addr <> addr \/ read_slot <> n2w slot ==>
     lookup_storage read_slot
       (lookup_transient_storage read_addr st'.tStorage) =
     lookup_storage read_slot
       (lookup_transient_storage read_addr st.tStorage))
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = read_addr` >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem release_nonreentrant_lock_frame:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  st'.accounts = st.accounts /\
  (!read_addr read_slot.
     read_addr <> addr \/ read_slot <> n2w slot ==>
     lookup_storage read_slot
       (lookup_transient_storage read_addr st'.tStorage) =
     lookup_storage read_slot
       (lookup_transient_storage read_addr st.tStorage))
Proof
  simp[release_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = read_addr` >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem acquire_nonreentrant_lock_result:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  ((?err. res = INR err) ==>
     res = INR (Error (RuntimeError "nonreentrant lock")) /\ st' = st) /\
  (res = INL () /\ is_view ==> st' = st) /\
  (res = INL () /\ ~is_view ==>
     lookup_storage (n2w slot)
       (lookup_transient_storage addr st'.tStorage) = 1w)
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem release_nonreentrant_lock_result:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  res = INL () /\
  lookup_storage (n2w slot)
    (lookup_transient_storage addr st'.tStorage) = 0w
Proof
  simp[release_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem reserved_transient_write_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock ==>
  contract_storage_well_formed cx
    (st with tStorage updated_by
       update_transient_storage cx.txn.target
         (update_storage (n2w lock) value
           (lookup_transient_storage cx.txn.target st.tStorage)))
Proof
  rpt strip_tac >>
  simp[contract_storage_well_formed_def] >> conj_tac
  >- (simp[vyperLookupStorageTheory.well_formed_storage_def,
           vyperLookupStorageTheory.storage_var_in_range_def] >>
      rpt strip_tac >>
      `declared_storage_region cx mid n [] =
         SOME (is_transient,n2w off,tv)` by
        metis_tac[declared_storage_region_ordinary] >>
      `slots_in_range (get_storage cx st is_transient) off tv` by
        metis_tac[contract_storage_well_formed_storage,
                  vyperLookupStorageTheory.well_formed_storage_def,
                  vyperLookupStorageTheory.storage_var_in_range_def,
                  vyperStorageBackendTheory.get_storage_backend_eq] >>
      Cases_on `is_transient` >>
      gvs[vyperStorageBackendTheory.get_storage_backend_eq,
          vyperStorageBackendTheory.get_storage_def,
          vfmExecutionTheory.lookup_transient_storage_def,
          vfmExecutionTheory.update_transient_storage_def,
          combinTheory.APPLY_UPDATE_THM] >>
      `lock + 1 <= dimword(:256)` by
        metis_tac[storage_layout_safe_nonreentrant_slot_nonoverflow] >>
      `lock < dimword(:256)` by decide_tac >>
      `off + type_slot_size tv <= dimword(:256)` by (
        drule storage_layout_safe_layout >>
        simp[vyperLookupStorageTheory.well_formed_layout_def] >>
        metis_tac[]) >>
      Cases_on `off < dimword(:256)`
      >- (`ranges_disjoint lock 1 off (type_slot_size tv)` by (
            drule_all storage_layout_safe_nonreentrant_slot_separation >>
            simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
          `update_storage (n2w lock) value (st.tStorage cx.txn.target) =
           apply_writes (n2w lock) [(0,value)] (st.tStorage cx.txn.target)` by
            simp[vyperStorageTheory.apply_writes_def,
                 arithmeticTheory.MOD_LESS] >>
          pop_assum SUBST1_TAC >>
          irule vyperLookupStorageTheory.slots_in_range_disjoint_apply_writes >>
          simp[] >>
          qexists `1` >> simp[] >>
          conj_tac
          >- (qpat_assum `lock + 1 <= dimword(:256)` mp_tac >> EVAL_TAC) >>
          qpat_x_assum `ranges_disjoint lock 1 off (type_slot_size tv)` mp_tac >>
          simp[vyperStorageFrameTheory.ranges_disjoint_def]) >>
      `off = dimword(:256) /\ type_slot_size tv = 0` by decide_tac >>
      irule (CONJUNCT1
        vyperStorageWritePreservationTheory.zero_slot_size_slots_in_range) >>
      simp[]) >>
  qpat_x_assum `contract_storage_well_formed cx st` mp_tac >>
  simp[contract_storage_well_formed_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `slots_in_range (get_storage cx st b) (w2n slot) tv` by (
    qpat_assum `!mid n subs b slot tv storage st'. _`
      (qspecl_then
        [`mid`, `n`, `subs`, `b`, `slot`, `tv`, `get_storage cx st b`, `st`]
        mp_tac) >>
    simp[vyperStorageBackendTheory.get_storage_backend_eq]) >>
  Cases_on `b` >>
  gvs[vyperStorageBackendTheory.get_storage_backend_eq,
      vyperStorageBackendTheory.get_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmExecutionTheory.update_transient_storage_def,
      combinTheory.APPLY_UPDATE_THM] >>
  `lock + 1 <= dimword(:256)` by
    metis_tac[storage_layout_safe_nonreentrant_slot_nonoverflow] >>
  `lock < dimword(:256)` by decide_tac >>
  `ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)` by
    metis_tac[storage_layout_safe_nonreentrant_slot_separation] >>
  `update_storage (n2w lock) value (st.tStorage cx.txn.target) =
   apply_writes (n2w lock) [(0,value)] (st.tStorage cx.txn.target)` by
    simp[vyperStorageTheory.apply_writes_def, arithmeticTheory.MOD_LESS] >>
  pop_assum SUBST1_TAC >>
  irule vyperLookupStorageTheory.slots_in_range_disjoint_apply_writes >>
  simp[] >>
  conj_tac
  >- (drule_all storage_layout_safe_region_nonoverflow >>
      simp[arithmeticTheory.ADD_COMM]) >>
  qexists `1` >> simp[] >>
  conj_tac
  >- (qpat_assum `lock + 1 <= dimword(:256)` mp_tac >> EVAL_TAC) >>
  qpat_x_assum
    `ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)` mp_tac >>
  simp[vyperStorageFrameTheory.ranges_disjoint_def]
QED

Theorem acquire_nonreentrant_lock_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock /\
  acquire_nonreentrant_lock cx.txn.target lock is_view st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `lookup_storage (n2w lock)
    (lookup_transient_storage cx.txn.target st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  gvs[acquire_nonreentrant_lock_eq] >>
  metis_tac[reserved_transient_write_preserves_contract_storage_well_formed]
QED

Theorem release_nonreentrant_lock_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock /\
  release_nonreentrant_lock cx.txn.target lock st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  gvs[release_nonreentrant_lock_eq] >>
  metis_tac[reserved_transient_write_preserves_contract_storage_well_formed]
QED

Theorem get_storage_stk_scopes[local]:
  get_storage (cx with stk updated_by f) (st with scopes := scopes) b =
  get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_stk_scopes[local]:
  contract_storage_well_formed
    (cx with stk updated_by f) (st with scopes := scopes) <=>
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       vyperStorageBackendTheory.get_storage_def,
       get_storage_stk_scopes]
QED

Theorem push_function_preserves_storage_context:
  push_function src_fn sc cx st = (INL cx',st') ==>
  cx'.txn.target = cx.txn.target /\
  cx'.nonreentrant_slot = cx.nonreentrant_slot /\
  (storage_layout_safe cx' <=> storage_layout_safe cx) /\
  (contract_storage_well_formed cx' st' <=>
   contract_storage_well_formed cx st)
Proof
  simp[push_function_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[contract_storage_well_formed_stk_scopes]
QED

Theorem push_function_preserves_runtime_storage_boundaries:
  storage_layout_safe cx /\
  contract_storage_well_formed cx st /\
  push_function src_fn sc cx st = (INL cx',st') ==>
  storage_layout_safe cx' /\
  contract_storage_well_formed cx' st' /\
  cx'.txn.target = cx.txn.target /\
  cx'.nonreentrant_slot = cx.nonreentrant_slot
Proof
  metis_tac[push_function_preserves_storage_context]
QED

Theorem eval_iterator_preserves_runtime_consistent[local]:
  well_typed_iterator env ty it /\ runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_iterator it) /\
  eval_iterator cx it st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 3 eval_scc_type_sound_mutual]
QED

Theorem eval_expr_preserves_runtime_consistent[local]:
  well_typed_expr env e /\ runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_exprs_success_runtime_typed[local]:
  well_typed_exprs env es /\
  runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_exprs cx es st = (INL vs,st') ==>
  exprs_runtime_typed env es vs
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >> simp[]
QED
Theorem eval_exprs_success_runtime_typed_from_eval[local]:
  eval_exprs cx es st = (INL vs,st') /\
  well_typed_exprs env es /\
  runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  exprs_runtime_typed env es vs
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`, `cx` |-> `cx`,
                  `st` |-> `st`, `vs` |-> `vs`, `st'` |-> `st'`]
            eval_exprs_success_runtime_typed) >>
  (impl_tac >- simp[]) >> simp[]
QED


Theorem eval_expr_success_result_typed[local]:
  well_typed_expr env e /\
  runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL tv,st') ==>
  eval_result_typed (env,cx,st') tv (Type (expr_type e))
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_exprs_preserves_runtime_consistent[local]:
  well_typed_exprs env es /\ runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_exprs cx es st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >> simp[]
QED
Theorem eval_exprs_preserves_runtime_consistent_from_eval[local]:
  eval_exprs cx es st = (res,st') /\
  well_typed_exprs env es /\ runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  runtime_consistent env cx st'
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`, `cx` |-> `cx`,
                  `st` |-> `st`, `res` |-> `res`, `st'` |-> `st'`]
            eval_exprs_preserves_runtime_consistent) >>
  simp[]
QED


Theorem eval_expr_results_preserves_runtime_consistent_from_eval[local]:
  eval_expr_results cx es st = (res,st') /\
  well_typed_exprs env es /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >> simp[]
QED

Theorem eval_expr_results_success_typed[local]:
  eval_expr_results cx es st = (INL results,st') /\
  well_typed_exprs env es /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  expr_results_typed (env,cx,st') es results
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >> simp[]
QED

Theorem eval_for_preserves_runtime_consistent[local]:
  evaluate_type env.type_defs ty = SOME tyv /\
  EVERY (value_has_type tyv) vs /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts body_stmts) /\
  eval_for cx tyv id body_stmts vs st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 4 eval_scc_type_sound_mutual]
QED

Theorem get_storage_logs[local]:
  get_storage cx (st with logs updated_by f) b = get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_logs[local]:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx (st with logs updated_by f)
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       get_storage_logs]
QED

Theorem contract_storage_well_formed_accounts_transient_frame[local]:
  contract_storage_well_formed cx st /\
  st.accounts = st'.accounts /\ st.tStorage = st'.tStorage ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >>
  conj_tac >- (gen_tac >> Cases_on `b` >>
                 simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[]
QED

Theorem contract_storage_well_formed_pending_deletions[local]:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with pending_deletions := pending)
Proof
  strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  gen_tac >> Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_scopes[local]:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx (st with scopes := scopes)
Proof
  strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[get_storage_scopes]
QED

Theorem push_scope_preserves_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\
  push_scope st = (res,st') ==>
  runtime_storage_consistent env cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `push_scope _ = _` mp_tac >>
  simp[push_scope_def, return_def] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx
     (st with scopes updated_by CONS FEMPTY)` by (
    simp[runtime_consistent_def] >>
    conj_tac
    >- (irule push_scope_env_consistent >>
        metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
    conj_tac
    >- (irule push_scope_preserves_state_well_typed >>
        qexistsl_tac [`st`, `()`] >> simp[push_scope_def, return_def] >>
        metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
    metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
  `contract_storage_well_formed cx
     (st with scopes updated_by CONS FEMPTY)` by (
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st` >>
    conj_tac
    >- (gen_tac >> Cases_on `b` >>
        simp[vyperStorageBackendTheory.get_storage_def]) >>
    metis_tac[runtime_storage_consistent_storage]) >>
  metis_tac[runtime_storage_consistent_intro,
            runtime_storage_consistent_layout]
QED
Theorem pop_scope_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  pop_scope st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `pop_scope _ = _` mp_tac >>
  Cases_on `st.scopes` >>
  simp[pop_scope_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >>
  conj_tac
  >- (gen_tac >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[]
QED


Theorem new_variable_storage_frame[local]:
  new_variable id tv v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_apply, ignore_bind_apply, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def, set_scopes_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `st.scopes` >>
  gvs[raise_def, set_scopes_def, return_def] >>
  simp[get_storage_scopes]
QED

Theorem new_variable_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  new_variable id tv v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[new_variable_storage_frame]
QED

Theorem finally_preserves_state_predicate[local]:
  !P f g st res st'.
  (!r s. f st = (r,s) ==> P s) /\
  (!s r s'. P s /\ g s = (r,s') ==> P s') /\
  finally f g st = (res,st') ==>
  P st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >> rename1 `f st = (main_res,main_st)` >>
  Cases_on `main_res` >>
  Cases_on `g main_st` >>
  rename1 `g main_st = (cleanup_res,cleanup_st)` >>
  Cases_on `cleanup_res` >>
  gvs[finally_def, ignore_bind_apply, return_def, raise_def] >>
  metis_tac[]
QED

Theorem default_scope_finally_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  (!r s.
     m (st with scopes := [FEMPTY]) = (r,s) ==>
     contract_storage_well_formed cx s) /\
  finally (do set_scopes [FEMPTY]; m od) (set_scopes prev) st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `!r s.
     (do set_scopes [FEMPTY]; m od) st = (r,s) ==>
     contract_storage_well_formed cx s` by (
    rpt strip_tac >>
    qpat_x_assum `(do set_scopes [FEMPTY]; m od) st = _` mp_tac >>
    simp[ignore_bind_apply, set_scopes_def, return_def] >>
    metis_tac[]) >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     set_scopes prev s = (r,s') ==>
     contract_storage_well_formed cx s'` by (
    rpt strip_tac >>
    qpat_x_assum `set_scopes prev _ = _` mp_tac >>
    simp[set_scopes_def, return_def] >>
    rpt strip_tac >> gvs[] >>
    irule contract_storage_well_formed_scopes >> simp[]) >>
  qspecl_then
    [`contract_storage_well_formed cx`,
     `ignore_bind (set_scopes [FEMPTY]) m`, `set_scopes prev`,
     `st`, `res`, `st'`] mp_tac finally_preserves_state_predicate >>
  simp[] >> metis_tac[]
QED

Theorem default_eval_exprs_finally_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  (!r s.
     eval_exprs cxd needed (st with scopes := [FEMPTY]) = (r,s) ==>
     contract_storage_well_formed cx s) /\
  finally
    (do set_scopes [FEMPTY]; eval_exprs cxd needed od)
    (set_scopes prev) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[default_scope_finally_preserves_contract_storage_well_formed]
QED

Theorem default_eval_exprs_finally_success[local]:
  finally
    (do set_scopes [FEMPTY]; eval_exprs cxd needed od)
    (set_scopes prev) st = (INL vs,st') ==>
  ?pre.
    eval_exprs cxd needed (st with scopes := [FEMPTY]) = (INL vs,pre) /\
    st' = pre with scopes := prev
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, bind_apply, ignore_bind_apply, set_scopes_def,
       return_def, raise_def] >>
  Cases_on `eval_exprs cxd needed (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `r` >> simp[]
QED

Theorem try_eval_stmts_handle_function_preserves_contract_storage_well_formed[local]:
  !cx cxf stmts st res st'.
  (!r s.
     eval_stmts cxf stmts st = (r,s) ==>
     contract_storage_well_formed cx s) /\
  try (do eval_stmts cxf stmts; return NoneV od) handle_function st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `eval_stmts cxf stmts st` >>
  rename1 `eval_stmts cxf stmts st = (body_res,body_st)` >>
  `contract_storage_well_formed cx body_st` by metis_tac[] >>
  Cases_on `body_res` >>
  gvs[try_def, ignore_bind_apply, return_def, raise_def] >>
  Cases_on `y` >>
  gvs[handle_function_def, return_def, raise_def]
QED

Theorem intcall_lock_state_preserves_runtime_frame_storage[local]:
  !cx nr is_view st lock_st.
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) st = (INL (),lock_st) ==>
    lock_st.scopes = st.scopes /\
    lock_st.immutables = st.immutables /\
    lock_st.accounts = st.accounts /\
    lock_st.outcomes = st.outcomes
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  imp_res_tac lock_outcomes_preserved >>
  drule acquire_nonreentrant_lock_scopes >>
  drule acquire_nonreentrant_lock_immutables >>
  drule acquire_nonreentrant_lock_frame >>
  simp[]
QED

Theorem env_scopes_consistent_stk_irrelevant_storage[local]:
  !env cx f st.
    env_scopes_consistent env (cx with stk updated_by f) st <=>
    env_scopes_consistent env cx st
Proof
  simp[env_scopes_consistent_def, vyperContextTheory.get_tenv_def]
QED

Theorem runtime_consistent_env_immutables_storage[local]:
  runtime_consistent env cx st ==>
  env_immutables_consistent env cx st
Proof
  simp[runtime_consistent_def, env_consistent_def]
QED

Theorem runtime_consistent_scopes_well_typed_storage[local]:
  runtime_consistent env cx st ==> EVERY scope_well_typed st.scopes
Proof
  simp[runtime_consistent_def, state_well_typed_def]
QED

Theorem runtime_consistent_context_storage[local]:
  runtime_consistent env cx st ==> context_well_typed cx
Proof
  simp[runtime_consistent_def]
QED

Theorem runtime_consistent_state_accounts_storage[local]:
  runtime_consistent env cx st ==>
  state_well_typed st /\ accounts_well_typed st.accounts
Proof
  simp[runtime_consistent_def]
QED

Theorem state_accounts_scopes_storage[local]:
  state_well_typed st /\ accounts_well_typed st.accounts /\
  EVERY scope_well_typed scopes ==>
  state_well_typed (st with scopes := scopes) /\
  accounts_well_typed (st with scopes := scopes).accounts
Proof
  simp[state_well_typed_def]
QED

Theorem env_immutables_consistent_defaults_scopes_storage[local]:
  env_immutables_consistent (defaults_env env) cx st ==>
  env_immutables_consistent env cx (st with scopes := scopes)
Proof
  simp[env_immutables_consistent_def, defaults_env_def] >> metis_tac[]
QED

Theorem intcall_cleanup_preserves_contract_storage_well_formed[local]:
  !cx prev nr is_view st res st'.
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  (do
     pop_function prev;
     if nr /\ ~is_view then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `nr /\ ~is_view` >>
  gvs[pop_function_def, ignore_bind_apply, set_scopes_def, return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> gvs[return_def]
      >- (irule contract_storage_well_formed_scopes >> simp[]) >>
      `contract_storage_well_formed cx (st with scopes := prev)` by
        metis_tac[contract_storage_well_formed_scopes] >>
      metis_tac[
        release_nonreentrant_lock_preserves_contract_storage_well_formed]) >>
  irule contract_storage_well_formed_scopes >> simp[]
QED

Theorem intcall_post_push_suffix_preserves_contract_storage_well_formed[local]:
  !cx cxf fn_stmts body_st prev nr is_view rtv res st'.
    contract_storage_well_formed cx body_st /\
    storage_layout_safe cx /\
    (!bres bst.
       eval_stmts cxf fn_stmts body_st = (bres,bst) ==>
       contract_storage_well_formed cx bst) /\
    (do
       rv <- finally
         (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr /\ ~is_view then
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) body_st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on
    `finally
       (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
       (do
          pop_function prev;
          if nr /\ ~is_view then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
        od)
       body_st` >>
  rename1 `_ = (body_final_res,body_final_st)` >>
  `!r s.
     try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function body_st =
       (r,s) ==>
     contract_storage_well_formed cx s` by
    metis_tac[
      try_eval_stmts_handle_function_preserves_contract_storage_well_formed] >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     (do
        pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
      od) s = (r,s') ==>
     contract_storage_well_formed cx s'` by
    metis_tac[intcall_cleanup_preserves_contract_storage_well_formed] >>
  `contract_storage_well_formed cx body_final_st` by (
    qspecl_then
      [`contract_storage_well_formed cx`,
       `try (ignore_bind (eval_stmts cxf fn_stmts) (return NoneV))
          handle_function`,
       `ignore_bind (pop_function prev)
          (if nr /\ ~is_view then
             case cx.nonreentrant_slot of
               NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ())`,
       `body_st`, `body_final_res`, `body_final_st`]
      mp_tac finally_preserves_state_predicate >>
    simp[] >> metis_tac[]) >>
  Cases_on `body_final_res` >>
  gvs[bind_apply, lift_option_type_def, return_def, raise_def] >>
  Cases_on `safe_cast rtv x` >>
  gvs[lift_option_type_def, return_def, raise_def]
QED

Theorem intcall_post_push_expanded_suffix_preserves_contract_storage_well_formed[local]:
  !cx cxf fn_stmts body_st prev nr is_view rtv res st'.
    contract_storage_well_formed cx body_st /\
    storage_layout_safe cx /\
    (!bres bst.
       eval_stmts cxf fn_stmts body_st = (bres,bst) ==>
       contract_storage_well_formed cx bst) /\
    (case
       finally
         (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr /\ ~is_view then
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od)
         body_st
     of
       (INL rv,s) =>
         (case
            (case safe_cast rtv rv of
               NONE => raise (Error (TypeError "IntCall cast ret"))
             | SOME v => return v) s
          of
            (INL crv,s') => (INL (Value crv),s')
          | (INR e,s') => (INR e,s'))
     | (INR e,s) => (INR e,s)) = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qspecl_then
    [`cx`, `cxf`, `fn_stmts`, `body_st`, `prev`, `nr`, `is_view`,
     `rtv`, `res`, `st'`]
    mp_tac intcall_post_push_suffix_preserves_contract_storage_well_formed >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on
       `finally
          (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
          (do
             pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
                 NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
           od)
          body_st` >>
     rename1 `_ = (body_final_res,body_final_st)` >>
     Cases_on `body_final_res` >>
     gvs[bind_apply, lift_option_type_def, return_def, raise_def] >>
     Cases_on `safe_cast rtv x` >>
     gvs[lift_option_type_def, return_def, raise_def]) >>
  simp[]
QED

Theorem intcall_post_defaults_preserves_contract_storage_well_formed[local]:
  !cx src_id_opt fn args vs dflt_vs ret mut nr fn_stmts prev st res st'.
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  (!cxf s r s'.
     contract_storage_well_formed cx s /\
     eval_stmts cxf fn_stmts s = (r,s') ==>
     contract_storage_well_formed cx s') /\
  (do
     env <- lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments";
     rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret";
     is_view <<- (mut = View \/ mut = Pure);
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot =>
            acquire_nonreentrant_lock cx.txn.target slot is_view
      else return ());
     cxf <- push_function (src_id_opt,fn) env cx;
     rv <- finally
       (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
       (do
          pop_function prev;
          if nr /\ ~is_view then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot =>
                release_nonreentrant_lock cx.txn.target slot
          else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `bind_arguments (get_tenv cx) args (vs ++ dflt_vs)` >>
  gvs[lift_option_type_def, bind_apply, return_def, raise_def] >>
  rename1 `bind_arguments (get_tenv cx) args (vs ++ dflt_vs) = SOME env` >>
  Cases_on `evaluate_type (get_tenv cx) ret` >>
  gvs[lift_option_type_def, bind_apply, return_def, raise_def] >>
  rename1 `evaluate_type (get_tenv cx) ret = SOME rtv` >>
  `!lock_res lock_st.
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
            (mut = View \/ mut = Pure)
      else return ()) st = (lock_res,lock_st) ==>
     contract_storage_well_formed cx lock_st` by (
    rpt strip_tac >>
    Cases_on `nr` >> gvs[return_def, raise_def] >>
    Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
    metis_tac[
      acquire_nonreentrant_lock_preserves_contract_storage_well_formed]) >>
  Cases_on
    `(if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
            (mut = View \/ mut = Pure)
      else return ()) st` >>
  rename1 `_ st = (lock_res,lock_st)` >>
  `contract_storage_well_formed cx lock_st` by metis_tac[] >>
  Cases_on `lock_res` >>
  gvs[ignore_bind_apply, bind_apply, push_function_def, return_def, raise_def] >>
  `contract_storage_well_formed cx (lock_st with scopes := [env])` by
    metis_tac[contract_storage_well_formed_scopes] >>
  Cases_on
    `finally
       (try
          (do
             eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts;
             return NoneV
           od)
          handle_function)
       (do
          pop_function prev;
          if nr /\ ~(mut = View \/ mut = Pure) then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot =>
                release_nonreentrant_lock cx.txn.target slot
          else return ()
        od)
       (lock_st with scopes := [env])` >>
  rename1 `_ = (body_final_res,body_final_st)` >>
  `!r s.
     try
       (do
          eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts;
          return NoneV
        od)
       handle_function (lock_st with scopes := [env]) = (r,s) ==>
     contract_storage_well_formed cx s` by
    metis_tac[
      try_eval_stmts_handle_function_preserves_contract_storage_well_formed] >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     (do
        pop_function prev;
        if nr /\ ~(mut = View \/ mut = Pure) then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
      od) s = (r,s') ==>
     contract_storage_well_formed cx s'` by
    metis_tac[intcall_cleanup_preserves_contract_storage_well_formed] >>
  `contract_storage_well_formed cx body_final_st` by (
    qspecl_then
      [`contract_storage_well_formed cx`,
       `try
          (ignore_bind
             (eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts)
             (return NoneV))
          handle_function`,
       `ignore_bind (pop_function prev)
          (if nr /\ ~(mut = View \/ mut = Pure) then
             case cx.nonreentrant_slot of
               NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ())`,
       `lock_st with scopes := [env]`, `body_final_res`, `body_final_st`]
      mp_tac finally_preserves_state_predicate >>
    simp[] >> strip_tac >>
    qpat_x_assum `_ ==> contract_storage_well_formed cx body_final_st` irule >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum
      `!s r s'. contract_storage_well_formed cx s /\
         do pop_function prev; _ od s = (r,s') ==>
         contract_storage_well_formed cx s'`
      (qspecl_then [`s`, `r`, `s'`] mp_tac) >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    qpat_x_assum `_ ==> contract_storage_well_formed cx s'` irule >>
    simp[]) >>
  Cases_on `body_final_res` >>
  gvs[] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >>
  gvs[lift_option_type_def, return_def, raise_def]
QED

Theorem eval_expr_place_preserves_runtime_consistent[local]:
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  runtime_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))]
QED

Theorem eval_base_place_preserves_runtime_consistent[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 1 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))]
QED

Theorem eval_target_place_preserves_runtime_consistent[local]:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))]
QED

Theorem eval_target_place_success_storage_type[local]:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,st') ==>
  eval_result_typed (env,cx,st') (PlaceR p) (Type ty)
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem typed_write_place_preserves_storage[local]:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  storage_place_region cx p /\
  eval_result_typed (env,cx,st) (PlaceR p) (Type ty) /\
  value_runtime_typed env ty v /\ write_place cx p v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[eval_result_typed_def, value_runtime_typed_def] >> strip_tac >> gvs[] >>
  drule_all write_place_preserves_contract_storage >> simp[]
QED

Theorem assign_tuple_targets_preserves_runtime_consistent[local]:
  well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
  runtime_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_atarget tgt) /\
  assign_tuple_targets cx tgt v st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >> metis_tac[cj 9 eval_scc_type_sound_mutual]
QED

Theorem eval_expr_success_storage_facts[local]:
  well_typed_expr env e /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL pv,st') ==>
  runtime_consistent env cx st' /\
  eval_result_typed (env,cx,st') pv (Type (expr_type e)) /\
  live_memory_result st' pv
Proof
  strip_tac >>
  `runtime_consistent env cx st'` by
    (drule_all eval_expr_preserves_runtime_consistent >> simp[]) >>
  `eval_result_typed (env,cx,st') pv (Type (expr_type e))` by
    (drule_all eval_expr_success_result_typed >> simp[]) >>
  simp[] >> fs[runtime_consistent_def] >>
  drule_at (Pat `eval_expr _ _ _ = _`)
    (cj 3 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >>
  disch_then (qspec_then `env` mp_tac) >> simp[]
QED

Theorem eval_target_place_storage_trace[local]:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (res,st') ==>
  typed_scope_transition st st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 2 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))]
QED

Theorem eval_target_place_success_storage_facts[local]:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,st') ==>
  eval_result_typed (env,cx,st') (PlaceR p) (Type ty) /\
  live_memory_result st' (PlaceR p)
Proof
  strip_tac >> conj_tac
  >- (drule_all eval_target_place_success_storage_type >> simp[]) >>
  fs[runtime_consistent_def] >>
  qspecl_then [`cx`,`bt`] strip_assume_tac (cj 8 eval_scc_type_sound_mutual) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => live_memory_result _ _ | INR _ => T)`
    (qspecl_then [`env`,`ty`,`st`,`INL p`,`st'`] mp_tac) >> simp[]
QED

Theorem eval_expr_storage_trace[local]:
  well_typed_expr env e /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  typed_scope_transition st st'
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  qspecl_then [`cx`,`e`] strip_assume_tac (cj 5 eval_scc_type_sound_mutual) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspecl_then [`env`,`st`,`res`,`st'`] mp_tac) >> simp[]
QED

Theorem eval_expr_place_success_result_typed[local]:
  type_place_expr env e = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL pv,st') ==>
  eval_result_typed (env,cx,st') pv vt
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_base_place_success_storage_type[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL pv,st') ==>
  eval_result_typed (env,cx,st') pv vt
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_base_place_storage_trace[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (res,st') ==>
  typed_scope_transition st st'
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 2 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_base_place_success_live[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL pv,st') ==>
  live_memory_result st' pv
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 3 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_base_place_success_writable[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL pv,st') ==>
  writable_place_result cx st' pv
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 4 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_target_place_success_writable[local]:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  source_supply st /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,st') ==>
  writable_place_result cx st' (PlaceR p)
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 4 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem update_place_tail_preserves_storage[local]:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  storage_place_region cx p /\ runtime_place_typed cx st p ptv /\
  evaluate_type env.type_defs ty = SOME ptv /\ value_has_type ptv cur /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  state_well_typed st /\ live_memory_result st rhs /\
  eval_result_typed (env,cx,st) rhs (Type (expr_type e)) /\
  (do
    v <- read_result cx rhs;
    result <- lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur v);
    write_place cx p result
  od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `do _ od _ = _` mp_tac >>
  simp_tac(srw_ss())[bind_def] >> Cases_on `read_result cx rhs st` >>
  rename1 `read_result cx rhs st = (answer,middle)` >>
  imp_res_tac read_result_state >> gvs[] >>
  reverse (Cases_on `answer`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `read_result cx rhs st = (INL right,st)` >>
  `value_runtime_typed env (expr_type e) right` by
    (drule_all read_live_result_success_type >> simp[]) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `read_result cx rhs input = (INL right,input)` >>
  fs[value_runtime_typed_def] >>
  qmatch_assum_rename_tac `evaluate_type env.type_defs (expr_type e) = SOME rhs_tv` >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp_tac(srw_ss())[bind_def, lift_sum_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right` >>
  simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `evaluate_binop _ ptv bop cur right = INL result` >>
  `value_has_type ptv result` by
    (irule well_typed_binop_success_type >>
     qexistsl_tac [`bop`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`ptv`,`rhs_tv`,`ty`,
       `case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0`,
       `cur`,`right`] >> simp[]) >>
  drule_all write_place_preserves_contract_storage >> simp[]
QED

Theorem eval_scc_storage_preservation_results_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_stmts cx ss st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_iterator cx it st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_for cx tyv id body vs st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx e. !env st res st'.
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==> contract_storage_well_formed cx st') /\
     (!vt. type_place_expr env e = SOME vt ==>
       contract_storage_well_formed cx st'))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgt v. !env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    assign_tuple_targets cx tgt v st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgts vs. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    protected_storage_calls_preserve cx /\ protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\ eval_expr_results cx es st = (res,st') ==>
    contract_storage_well_formed cx st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  (fn (g as (asms,w)) =>
    let
      fun head tm = #Name (dest_thy_const (#1 (strip_comb tm)))
      fun app tm =
        let val (h,args) = strip_comb tm
            val n = #Name (dest_thy_const h)
        in (List.exists (fn s => s = n)
              ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
               "eval_expr", "eval_exprs", "eval_expr_results", "eval_base_place", "eval_target_place"]
            andalso length args = (if n = "eval_for" then 6 else 3)) orelse
           (List.exists (fn s => s = n)
              ["assign_tuple_targets", "assign_tuple_target_list"] andalso length args = 4)
        end handle HOL_ERR _ => false
      val body = #2 (strip_forall w)
      val equations = if is_imp body then strip_conj (fst (dest_imp body)) else asms
      val outer = List.filter (fn a => is_eq a andalso app (lhs a)) equations
      val tm = case outer of [equation] => lhs equation
             | _ => raise Fail "Expected one outer evaluator equation"
      val (h,args) = strip_comb tm
      val n = head h
      val arg = el 2 args
      fun shape t = if listSyntax.is_nil t then "nil" else "cons"
      fun expr_label e =
        let val (_,xs) = strip_comb e
        in if head e = "Call" then "Expr_Call_" ^ head (el 2 xs)
           else "Expr_" ^ head e end
      fun stmt_label s =
        let val (_,xs) = strip_comb s
            val c = head s
        in if c = "Return" then "Return_" ^ head (hd xs)
           else if c = "Raise" then head (hd xs)
           else if c = "Assert" then head (el 2 xs)
           else if c = "Assign" then
             (if head (hd xs) = "BaseTarget" then "Assign_Base" else "Assign_Tuple")
           else c end
      val label =
        if n = "eval_stmt" then stmt_label arg
        else if n = "eval_stmts" then "Stmts_" ^ shape arg
        else if n = "eval_iterator" then "Iterator_" ^ head arg
        else if n = "eval_for" then "For_" ^ shape (el 5 args)
        else if n = "eval_expr" then expr_label arg
        else if n = "eval_exprs" then "Exprs_" ^ shape arg
        else if n = "eval_expr_results" then "Results_" ^ shape arg
        else if n = "eval_base_place" then "BasePlaceRoot_" ^ head arg
        else if n = "eval_target_place" then "TargetPlace"
        else if n = "assign_tuple_targets" then "TupleStore_" ^ head arg
        else if n = "assign_tuple_target_list" then
          "TupleStores_" ^ shape arg ^ "_" ^ shape (el 3 args)
        else raise Fail ("Unknown storage evaluator: " ^ n)
    in suspend label g end)
QED

Resume eval_scc_storage_preservation_results_mutual[For_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx s1` by metis_tac[] >>
  Cases_on `er` >> gvs[]
  >- (
    Cases_on `read_result cx x s1` >>
    `r = s1` by metis_tac[read_result_state] >> gvs[] >>
    Cases_on `q` >> gvs[raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Pass]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Continue]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Break]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Stmts_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED


Resume eval_scc_storage_preservation_results_mutual[Exprs_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Results_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Results_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs es` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `runtime_consistent env cx head_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx head_st` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `head_res` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `eval_expr_results cx es head_st` >>
  ORACLE_STORAGE_TAC >> first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_flag_mem_state >>
  gvs[runtime_storage_consistent_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
    simp[runtime_storage_consistent_def, runtime_consistent_def] >>
    strip_tac >>
    drule_all eval_stmt_type_preservation_success >> strip_tac >>
    `runtime_storage_consistent env'' cx st1` by
      simp[runtime_storage_consistent_def, runtime_consistent_def] >>
    Cases_on `eval_stmts cx ss st1` >>
    ORACLE_STORAGE_TAC >>
    first_x_assum drule_all >> strip_tac >>
    gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
  gvs[bind_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs es` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (mr,stm)` >>
    `stm = st1` by metis_tac[read_result_state] >> gvs[] >>
    Cases_on `mr` >> gvs[]
    >- (
      Cases_on `eval_exprs cx es st1` >>
      ORACLE_STORAGE_TAC >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED


Resume eval_scc_storage_preservation_results_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    Cases_on `read_result cx x st1` >>
    imp_res_tac read_result_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    Cases_on `lift_option_type (dest_StringV x') "not StringV" r` >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    Cases_on `q` >> gvs[return_def, raise_def] >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def,
    listTheory.APPEND_NIL] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_result cx x st1` >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `st' = r` by
    (drule_at (Pat `switch_BoolV _ _ _ _ _ = _`) switch_BoolV_state >>
     simp[return_def, raise_def]) >>
  qpat_x_assum `st' = r` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume eval_scc_storage_preservation_results_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def,
    listTheory.APPEND_NIL] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_result cx x st1` >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `st' = r` by
    (drule_at (Pat `switch_BoolV _ _ _ _ _ = _`) switch_BoolV_state >>
     simp[return_def, raise_def]) >>
  qpat_x_assum `st' = r` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume eval_scc_storage_preservation_results_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[bind_def, return_def, push_log_def] >>
  Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
  gvs[lift_option_def, raise_def, return_def, push_log_def] >>
  rpt strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >>
  metis_tac[contract_storage_well_formed_logs]
QED

Resume eval_scc_storage_preservation_results_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def]
  >- (
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (mat_res,stm)` >>
    imp_res_tac read_result_state >> gvs[] >>
    Cases_on `mat_res` >> gvs[bind_def, return_def] >>
    strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac lift_option_type_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `base_res` >> gvs[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (TypeBuiltin ty tb typ es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `well_typed_exprs env es` by
      (qpat_x_assum `well_typed_expr env (TypeBuiltin ty tb typ es)` mp_tac >>
       simp_tac(srw_ss())[Once well_typed_expr_def]) >>
    `type_builtin_args_length_ok tb (LENGTH es)` by
      (qpat_assum `well_typed_expr env (TypeBuiltin v11 tb typ es)` mp_tac >>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
       strip_tac >> drule well_typed_type_builtin_args_length >> simp[]) >>
    qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      return_def, raise_def, type_check_def, assert_def] >>
    qpat_assum `type_builtin_args_length_ok tb (LENGTH es)`
      (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
      type_check_def, assert_def] >>
    qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def, return_def]) >> strip_tac >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `exprs_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `lift_sum (evaluate_type_builtin cx tb typ (MAP expr_type es) x) st1` >>
      imp_res_tac lift_sum_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (TypeBuiltin ty tb typ es) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call ty RawRevert es extra))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call ty RawRevert es extra)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def]
    >- (Cases_on `LENGTH x = 1` >> gvs[] >>
        Cases_on `dest_BytesV (HD x)` >>
        gvs[lift_option_type_def, raise_def, return_def] >>
        rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call ty RawLog es extra))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call ty RawLog es extra)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, push_log_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, push_log_def]
    >- (
      strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      metis_tac[contract_storage_well_formed_logs]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_scc_storage_preservation_results_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Pop v11 bt) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (gvs[int_calls_expr_def]) >>
  conj_tac
  >- (strip_tac >>
      drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
      `well_typed_target env bt (ArrayT v11 (Dynamic n))` by
        simp[well_typed_target_def] >>
      `runtime_consistent env cx st` by
        metis_tac[runtime_storage_consistent_runtime] >>
      qpat_x_assum `eval_expr cx (Pop _ bt) st = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_target_place cx bt st` >>
      rename1 `eval_target_place cx bt st = (target_res,st1)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `target_res` >> gvs[bind_def] >> strip_tac >> gvs[] >>
      drule_all eval_target_place_success_storage_type >> strip_tac >>
      drule eval_target_place_region >> strip_tac >>
      gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
      `storage_layout_safe cx` by
        metis_tac[runtime_storage_consistent_layout] >>
      drule_all pop_place_preserves_contract_storage >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED


Theorem eval_raw_call_preserves_contract_storage:
  protected_storage_calls_preserve cx /\ contract_storage_well_formed cx st /\
  eval_raw_call cx flags target_addr calldata amount st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_raw_call _ _ _ _ _ _ = _` mp_tac >>
  reverse (Cases_on `~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)`) >>
  simp[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, get_transient_storage_def]
  >- (strip_tac >> gvs[]) >>
  fs[] >>
  (* Integration repair: the previous `(Cases_on` opened an unmatched
     tactic parenthesis extending through QED. *)
  Cases_on `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage` >>
  simp[lift_option_def, bind_def, return_def, raise_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  rename1 `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage = SOME payload` >>
  PairCases_on `payload` >>
  rename1 `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage =
      SOME (success,return_data,call_accounts,call_transient,emitted_logs,deletions)` >>
  simp[] >>
  `contract_storage_well_formed cx (st with <|accounts := call_accounts; tStorage := call_transient|>)` by
    (drule_all protected_storage_calls_preserve_run_raw_call >> simp[]) >>
  `contract_storage_well_formed cx
     ((st with <|accounts := call_accounts; tStorage := call_transient|>) with logs := st.logs ++ emitted_logs)` by
    metis_tac[contract_storage_well_formed_logs] >>
  Cases_on `success` >> Cases_on `flags.rcf_revert_on_failure` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[update_accounts_def, update_transient_def, append_logs_def, update_pending_deletions_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  irule contract_storage_well_formed_accounts_transient_frame >>
  qexists_tac `st with <|accounts := call_accounts; tStorage := call_transient|>` >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx
      (int_calls_expr (Call _ (RawCallTarget _) es _))` mp_tac >>
    simp[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def,
      lift_option_type_def] >> simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx args_st` by
      metis_tac[eval_exprs_preserves_runtime_consistent,
                runtime_storage_consistent_runtime] >>
    `runtime_storage_consistent env cx args_st` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `args_res` >> gvs[]
    >> FIRST [(
      rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      `exprs_runtime_typed env es vs` by (
        irule eval_exprs_success_runtime_typed >> simp[] >>
        metis_tac[runtime_storage_consistent_runtime]) >>
      `LENGTH vs = 3` by (
        gvs[exprs_runtime_typed_def] >>
        metis_tac[listTheory.LIST_REL_LENGTH]) >>
      mp_tac raw_call_args_runtime_typed_dest >>
      impl_tac >- simp[] >> strip_tac >> gvs[] >>
      simp[bind_def, return_def] >> strip_tac >>
      drule_all eval_raw_call_preserves_contract_storage >> simp[]),
      rpt strip_tac >> gvs[]])) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_scc_storage_preservation_results_mutual[Expr_Call_RawCallCalldataTarget]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx
      (int_calls_expr (Call _ (RawCallCalldataTarget _) es _))` mp_tac >>
    simp[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallCalldataTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, lift_option_type_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[]
    >> FIRST [(
      rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      `exprs_runtime_typed env es vs` by (
        irule eval_exprs_success_runtime_typed >> simp[] >>
        metis_tac[runtime_storage_consistent_runtime]) >>
      drule_all raw_call_calldata_args_runtime_typed_dest >> strip_tac >>
      gvs[bind_def, return_def] >> strip_tac >>
      drule_all eval_raw_call_preserves_contract_storage >> simp[]),
      rpt strip_tac >> gvs[]])) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `get_tenv cx = env.type_defs` by
    fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by (
    drule assignable_type_well_formed >>
    simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
  simp[lift_option_type_def, return_def] >>
  disch_then drule_all >> strip_tac >>
  simp[bind_apply, return_def] >>
  Cases_on `expr_res` >> gvs[raise_def]
  >- (
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (mat_res,stm)` >>
    imp_res_tac read_result_state >> gvs[] >>
    Cases_on `mat_res` >> gvs[return_def, raise_def]
    >- (
      strip_tac >>
      metis_tac[new_variable_preserves_contract_storage_well_formed]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED


Resume eval_scc_storage_preservation_results_mutual[Assign_Base]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[atarget_accepts_well_typed_atarget] >>
  qpat_x_assum `well_typed_atarget env (BaseTarget bt) tty`
    (assume_tac o REWRITE_RULE [well_typed_atarget_def]) >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_all_then strip_assume_tac) >>
  `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx rhs_st` by
    (drule_all eval_expr_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx rhs_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  reverse (Cases_on `rhs_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  qpat_x_assum `!s pv t. eval_expr _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac(srw_ss())[] >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  ORACLE_STORAGE_TAC >> first_x_assum drule_all >> strip_tac >>
  reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  simp_tac(srw_ss())[] >> suspend "Assign_Base_write"
QED

Resume eval_scc_storage_preservation_results_mutual[Assign_Base_write]:
  RESUME_TAC >> strip_tac >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qmatch_assum_rename_tac `eval_expr cx e st = (INL pv,rhs_st)` >>
  qmatch_assum_rename_tac `eval_target_place cx bt rhs_st = (INL p,target_st)` >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule_all eval_target_place_storage_trace >> strip_tac >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame rhs_st target_st` by
    (drule (cj 8 eval_metadata_frame_mutual) >> simp[]) >>
  `eval_result_typed (env,cx,target_st) pv (Type (expr_type e))` by
    (Cases_on `pv` >> gvs[eval_result_typed_def] >>
     metis_tac[runtime_place_typed_transport]) >>
  `live_memory_result target_st pv` by
    (irule live_result_transport >> qexists_tac `rhs_st` >> simp[]) >>
  `runtime_consistent env cx target_st` by
    (drule_all eval_target_place_preserves_runtime_consistent >> simp[]) >>
  `state_well_typed target_st` by gvs[runtime_consistent_def] >>
  Cases_on `read_result cx pv target_st` >>
  rename1 `read_result cx pv target_st = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `read_res` >> gvs[] >>
  qmatch_assum_rename_tac `read_result cx pv target_st = (INL v,target_st)` >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env tty v` by
    (fs[value_runtime_typed_def] >>
     drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  `eval_result_typed (env,cx,target_st) (PlaceR p) (Type tty)` by
    simp[eval_result_typed_def] >>
  drule_all typed_write_place_preserves_storage >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[Assign_Tuple]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, atarget_accepts_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx s1` by metis_tac[] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx s1` by
    (drule_all eval_expr_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx s1` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  reverse (Cases_on `er`) >- (simp[] >> strip_tac >> gvs[]) >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  Cases_on `read_result cx x s1` >>
  rename1 `read_result cx x s1 = (mr,s2)` >>
  imp_res_tac read_result_state >> gvs[] >>
  reverse (Cases_on `mr`) >- (simp[] >> strip_tac >> gvs[]) >>
  `value_runtime_typed env (expr_type e) x'` by
    (fs[runtime_consistent_def] >>
     drule_all read_live_result_success_type >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  ORACLE_STORAGE_TAC >>
  qpat_x_assum `!s0 tv t s1 v t1. _` drule_all >> simp[]
QED


Resume eval_scc_storage_preservation_results_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Append bt e) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >>
  qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    (drule_all eval_target_place_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `eval_target_place cx bt st = (INL p,st1)` >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule eval_target_place_region >> strip_tac >>
  qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  ORACLE_STORAGE_TAC >>
  simp_tac(srw_ss())[] >>
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
  first_x_assum drule_all >> strip_tac >>
  reverse (Cases_on `expr_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `eval_expr cx e st1 = (INL pv,st2)` >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `typed_scope_transition st1 st2` by
    (drule_all eval_expr_storage_trace >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
    (drule (cj 5 eval_metadata_frame_mutual) >> simp[]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st1 p (ArrayTV elem_tv (Dynamic n))` by
    gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  `runtime_place_typed cx st2 p (ArrayTV elem_tv (Dynamic n))` by
    (drule_all runtime_place_typed_transport >> simp[]) >>
  Cases_on `read_result cx pv st2` >>
  rename1 `read_result cx pv st2 = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >>
  reverse (Cases_on `read_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `read_result cx pv read_st = (INL v,read_st)` >>
  `eval_result_typed (env,cx,read_st) pv (Type (expr_type e))` by
    simp[eval_result_typed_def] >>
  `value_runtime_typed env (expr_type e) v` by
    (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env elem_ty v` by
    (gvs[value_runtime_typed_def] >>
     drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `value_has_type elem_tv v` by gvs[value_runtime_typed_def] >>
  strip_tac >> gvs[] >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  drule_all append_place_preserves_contract_storage >> simp[]
QED


Resume eval_scc_storage_preservation_results_mutual[AugAssign]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (AugAssign ty bt bop e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx target_st` by
    (drule_all eval_target_place_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx target_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  drule_all eval_target_place_success_storage_facts >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [eval_result_typed_def]) >>
  qpat_x_assum `?tv. evaluate_type _ _ = SOME tv /\ _` strip_assume_tac >>
  qmatch_assum_rename_tac `runtime_place_typed cx target_st p ptv` >>
  `place_type_value cx p target_st = (INL ptv,target_st)` by
    (qpat_assum `runtime_place_typed cx target_st p ptv`
      (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [runtime_place_typed_def])) >>
  `state_well_typed target_st` by gvs[runtime_consistent_def] >>
  simp_tac(srw_ss())[] >> Cases_on `read_place cx p target_st` >>
  rename1 `read_place cx p target_st = (read_res,read_st)` >>
  drule_all live_place_read_sound >> strip_tac >>
  qpat_x_assum `read_st = target_st` SUBST_ALL_TAC >>
  reverse (Cases_on `read_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  simp_tac(srw_ss())[] >> suspend "AugAssign_rhs"
QED

Resume eval_scc_storage_preservation_results_mutual[AugAssign_rhs]:
  RESUME_TAC >>
  qmatch_assum_rename_tac `read_place cx p target_st = (INL cur,target_st)` >>
  first_x_assum (fn th =>
    if length (#1 (strip_forall (concl th))) = 9 then
      mp_tac (Q.SPECL [`st`,`p`,`target_st`,`target_st`,`cur`,`target_st`,
                      `target_st`,`ptv`,`target_st`] th)
    else NO_TAC) >> simp[] >> strip_tac >>
  simp_tac(srw_ss())[] >> Cases_on `eval_expr cx e target_st` >>
  rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
  ORACLE_STORAGE_TAC >> first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
  `runtime_consistent env cx rhs_st` by
    (drule_all eval_expr_preserves_runtime_consistent >> simp[]) >>
  reverse (Cases_on `rhs_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  qmatch_assum_rename_tac `eval_expr cx e target_st = (INL rhs,rhs_st)` >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  drule_all eval_expr_storage_trace >> strip_tac >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame target_st rhs_st` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `runtime_place_typed cx rhs_st p ptv` by
    (irule runtime_place_typed_transport >> qexists_tac `target_st` >> simp[]) >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  simp_tac(srw_ss())[] >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `state_well_typed rhs_st` by gvs[runtime_consistent_def] >>
  drule_all (SIMP_RULE (srw_ss()) [Once bind_def] update_place_tail_preserves_storage) >>
  simp[]
QED


Resume eval_scc_storage_preservation_results_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[] >>
  rpt strip_tac >> gvs[]
QED


Resume eval_scc_storage_preservation_results_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss ss'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `cond_res`
  >- (
    rename1 `eval_expr cx e st = (INL tv,st1)` >>
    `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
    drule_all eval_expr_success_storage_facts >> strip_tac >>
    `st1 with scopes updated_by CONS FEMPTY =
       st1 with scopes := FEMPTY::st1.scopes` by
      (Cases_on `st1` >> simp[evaluation_state_fn_updates]) >>
    Cases_on `read_result cx tv st1` >>
    rename1 `read_result cx tv st1 = (rr,rs)` >>
    imp_res_tac read_result_state >> gvs[] >>
    reverse (Cases_on `rr`)
    >- (simp[bind_apply, bind_def, push_scope_def, return_def,
             switch_BoolV_def, read_result_empty_scope, finally_def,
             ignore_bind_def, pop_scope_def, raise_def] >>
        strip_tac >> gvs[] >>
        metis_tac[runtime_storage_consistent_storage, contract_storage_well_formed_scopes]) >>
    `value_runtime_typed env (expr_type e) x` by
      (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    rename1 `read_result cx tv st1 = (INL (BoolV b),st1)` >>
    `runtime_storage_consistent env cx
       (st1 with scopes updated_by CONS FEMPTY)` by (
      irule push_scope_preserves_runtime_storage_consistent >>
      qexistsl_tac [`INL ()`, `st1`] >>
      simp[push_scope_def, return_def]) >>
    Cases_on `b` >>
    simp[bind_apply, push_scope_def, return_def, switch_BoolV_def,
         read_result_empty_scope, bind_def]
    >- (
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)` mp_tac >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss (st1 with scopes updated_by CONS FEMPTY)` >>
      rename1 `eval_stmts cx ss (st1 with scopes updated_by CONS FEMPTY) =
                 (body_res,stb)` >>
      `push_scope st1 =
         (INL (),st1 with scopes updated_by CONS FEMPTY)` by
        simp[push_scope_def, return_def] >>
      ORACLE_STORAGE_TAC >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx stb` by simp[] >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, push_scope_def, return_def, finally_def,
           ignore_bind_apply] >>
      Cases_on `body_res` >> gvs[] >>
      Cases_on `pop_scope stb` >>
      rename1 `pop_scope stb = (pop_res,stpop)` >>
      `contract_storage_well_formed cx stpop` by (
        irule pop_scope_preserves_contract_storage_well_formed >>
        qexistsl_tac [`pop_res`, `stb`] >> simp[]) >>
      Cases_on `pop_res` >> gvs[] >>
      rpt strip_tac >> gvs[raise_def, read_result_empty_scope]) >>
    qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')` mp_tac >>
    simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
    Cases_on `eval_stmts cx ss' (st1 with scopes updated_by CONS FEMPTY)` >>
    rename1 `eval_stmts cx ss' (st1 with scopes updated_by CONS FEMPTY) =
               (body_res,stb)` >>
    `push_scope st1 =
       (INL (),st1 with scopes updated_by CONS FEMPTY)` by
      simp[push_scope_def, return_def] >>
    ORACLE_STORAGE_TAC >>
    first_x_assum drule_all >> strip_tac >>
    `contract_storage_well_formed cx stb` by simp[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, push_scope_def, return_def, finally_def,
         ignore_bind_apply] >>
    Cases_on `body_res` >> gvs[] >>
    Cases_on `pop_scope stb` >>
    rename1 `pop_scope stb = (pop_res,stpop)` >>
    `contract_storage_well_formed cx stpop` by (
      irule pop_scope_preserves_contract_storage_well_formed >>
      qexistsl_tac [`pop_res`, `stb`] >> simp[]) >>
    Cases_on `pop_res` >> gvs[] >>
    rpt strip_tac >> gvs[raise_def, read_result_empty_scope]) >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_apply, bind_def] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
    drule_all eval_expr_success_storage_facts >> strip_tac >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (rr,rs)` >>
    imp_res_tac read_result_state >> gvs[] >>
    reverse (Cases_on `rr`)
    >- (simp[switch_BoolV_def, bind_def] >> strip_tac >> gvs[]) >>
    rename1 `read_result cx x st1 = (INL cv,st1)` >>
    `value_runtime_typed env (expr_type e) cv` by
      (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b`
    >- (simp[switch_BoolV_def, bind_def, return_def, raise_def] >>
        strip_tac >> gvs[]) >>
    gvs[switch_BoolV_def, bind_def, return_def, raise_def] >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res,st2)` >>
    ORACLE_STORAGE_TAC >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[bind_def, return_def, raise_def] >>
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
    rpt strip_tac >> imp_res_tac read_result_state >>
    gvs[AllCaseEqs(), return_def, raise_def] >>
    Cases_on `dest_StringV sv` >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res,st1)` >>
  last_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  ORACLE_STORAGE_TAC >>
  Cases_on `expr1_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    Cases_on `read_result cx x st1` >>
    imp_res_tac read_result_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    qpat_x_assum `∀s'' tv1 t s''' s t'. _`
      (qspecl_then [`st`, `x`, `r`, `r`, `x'`, `r`] mp_tac) >>
    simp[] >> strip_tac >>
    pop_assum mp_tac >>
    Cases_on `eval_expr cx e' r` >>
    rename1 `eval_expr cx e' r = (expr2_res,st2)` >>
    simp[] >> strip_tac >>
    Cases_on `expr2_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `read_result cx x'' st2` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `lift_sum (get_range_limits x' x''') r'` >>
      imp_res_tac lift_sum_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> metis_tac[]) >>
    rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e'')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `cond_res`
  >- (
    rename1 `eval_expr cx e st = (INL tv,st1)` >>
    `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
    drule_all eval_expr_success_storage_facts >> strip_tac >>
    Cases_on `read_result cx tv st1` >>
    rename1 `read_result cx tv st1 = (rr,rs)` >>
    imp_res_tac read_result_state >> gvs[] >>
    reverse (Cases_on `rr`)
    >- (simp[switch_BoolV_def, bind_def, raise_def] >> strip_tac >> gvs[]) >>
    rename1 `read_result cx tv st1 = (INL cv,st1)` >>
    `value_runtime_typed env (expr_type e) cv` by
      (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    ORACLE_STORAGE_TAC >>
    Cases_on `b` >> simp[switch_BoolV_def, bind_def] >>
    first_x_assum drule >> strip_tac >>
    rename1 `eval_expr cx selected st1` >>
    Cases_on `eval_expr cx selected st1` >>
    rename1 `eval_expr cx selected st1 = (selected_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `selected_res` >> gvs[bind_def, return_def, raise_def] >>
    rpt strip_tac >> imp_res_tac conditional_result_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem int_calls_exprs_MAP_SND_storage[local]:
  !kes. int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes
Proof
  Induct >> simp[int_calls_expr_def] >> gen_tac >> PairCases_on `h` >>
  simp[int_calls_expr_def]
QED

Theorem well_typed_named_exprs_MAP_SND_storage[local]:
  !env kes. well_typed_named_exprs env kes ==>
            well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_expr (StructLit ty callee kes))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND_storage] >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_storage >> simp[]) >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `∀ks. ks = MAP FST kes ⇒ _`
    (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[bind_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem call_evaluation_safe_int_calls_exprs_HD_storage[local]:
  es <> [] /\ call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_expr (HD es))
Proof
  Cases_on `es` >> simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
    type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (
    `es <> []` by (
      Cases_on `es` >> simp[] >>
      qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
      qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp[well_typed_builtin_app_def]) >>
    `call_evaluation_safe cx (int_calls_expr (HD es))` by
      metis_tac[call_evaluation_safe_int_calls_exprs_HD_storage] >>
    `well_typed_expr env (HD es)` by
      (Cases_on `es` >> gvs[well_typed_expr_def]) >>
    qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
    qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
      type_check_def, assert_def] >>
    Cases_on `eval_expr cx (HD es) st` >>
    rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
    qpat_x_assum `∀s'' x t. _ ∧ bt = Len ⇒ _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    simp[type_check_def, assert_def] >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `arg_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `result_array_length cx x arg_st` >>
      imp_res_tac result_array_length_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `∀s'' x t. _ ∧ bt ≠ Len ⇒ _`
    (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  (impl_tac >- (simp[type_check_def, assert_def] >> metis_tac[])) >>
  strip_tac >> first_x_assum drule_all >> strip_tac >>
  Cases_on `args_res` >> gvs[bind_def, return_def, raise_def,
    get_accounts_def, lift_sum_def]
  >- (Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) x` >>
      gvs[return_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem transfer_value_storage_frame[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  Cases_on `amount = 0 ∨ fromAddr = toAddr`
  >- gvs[transfer_value_def, return_def] >>
  simp[transfer_value_def, bind_apply, ignore_bind_apply,
       get_accounts_def, check_def, assert_def, update_accounts_def,
       return_def, raise_def] >>
  rpt IF_CASES_TAC >> gvs[return_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem transfer_value_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[transfer_value_storage_frame]
QED

Theorem adopt_call_outcome_INR_storage[local]:
  (adopt_call_outcome rq co s = (INR e,s')) <=> F
Proof
  rw[vyperCallOutcomeTheory.adopt_call_outcome_def] >> pairarg_tac >>
  gvs[return_def]
QED

Theorem run_ext_call_storage_frame[local]:
  protected_storage_calls_preserve cx /\ contract_storage_well_formed cx st /\
  run_ext_call cx.txn.target callee calldata value_opt gas st.accounts
    st.tStorage txp = SOME result /\
  st'.accounts = FST (SND (SND result)) /\
  st'.tStorage = FST (SND (SND (SND result))) ==>
  contract_storage_well_formed cx st'
Proof
  PairCases_on `result` >> rpt strip_tac >> gvs[] >>
  drule_all protected_storage_calls_preserve_run_ext_call >> strip_tac >>
  irule contract_storage_well_formed_accounts_transient_frame >>
  first_x_assum (irule_at Any) >> gvs[]
QED

Theorem eval_send_preserves_contract_storage:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  protected_storage_calls_preserve cx /\
  eval_send cx has_gas vs st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `vs` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  Cases_on `t` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       check_def, lift_option_type_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def,
       append_logs_def, update_pending_deletions_def, return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, assert_def, adopt_call_outcome_INR_storage] >>~-
  ([`run_ext_call _ _ _ _ _ _ _ _ = SOME _`],
   irule run_ext_call_storage_frame >> simp[] >> metis_tac[]) >>
  metis_tac[take_call_outcome_storage_suffix,
            take_adopt_call_outcome_storage_suffix]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call _ (Send _) es _))`
         mp_tac >> simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env (Call _ (Send _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    `LENGTH es = if has_gas then 3 else 2` by
      (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
       rw[]) >>
    qpat_x_assum `!s'' x t. type_check _ _ s'' = (INL x,t) ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
         assert_def, return_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[]
    >- (ORACLE_STORAGE_TAC >> metis_tac[eval_send_preserves_contract_storage]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ (Send _) _ _) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def]
QED

(* Balance transfer/burning and deferred deletion leave protected storage
   unchanged even though the message halts successfully. *)
Theorem selfdestruct_tail_preserves_contract_storage[local]:
  contract_storage_well_formed cx st /\
  (do
     update_accounts
       (vfmExecution$transfer_value cx.txn.target target
         (lookup_account cx.txn.target st.accounts).balance);
     (if cx.txn.created_in_tx then do
        update_accounts (\acc. update_account cx.txn.target
          (lookup_account cx.txn.target acc with balance := 0) acc);
        update_pending_deletions (CONS cx.txn.target)
      od else return ());
     raise HaltException
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `cx.txn.created_in_tx` >>
  simp[bind_def, ignore_bind_def, update_accounts_def,
       update_pending_deletions_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  gen_tac >> Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmExecutionTheory.transfer_value_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[combinTheory.APPLY_UPDATE_THM]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx
          (int_calls_expr (Call _ SelfDestructTarget es _))` mp_tac >>
       simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env (Call _ SelfDestructTarget _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[]
    >- (
      Cases_on `LENGTH x = 1` >>
      gvs[type_check_def, assert_def, return_def, raise_def]
      >- (
        Cases_on `dest_AddressV (HD x)` >> gvs[return_def, raise_def]
        >- (rpt strip_tac >> gvs[]) >>
        rpt strip_tac >>
        qpat_assum `_ = (res,st')`
          (assume_tac o SRULE [bind_def, ignore_bind_def, return_def, raise_def]) >>
        drule_all (selfdestruct_tail_preserves_contract_storage |>
          SRULE [bind_def, ignore_bind_def, return_def, raise_def]) >> simp[]) >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Theorem increment_nonce_storage_frame[local]:
  update_accounts (vfmExecution$increment_nonce addr) st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `update_accounts _ _ = _` mp_tac >>
  simp[update_accounts_def, return_def] >> strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem increment_nonce_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  update_accounts (vfmExecution$increment_nonce addr) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[increment_nonce_storage_frame]
QED

(* An address collision bumps only the sender's nonce, which leaves both
   protected storage backends alone. *)
Theorem increment_nonce_update_frame[local]:
  !b. get_storage cx
        (s with accounts updated_by (vfmExecution$increment_nonce sender)) b =
      get_storage cx s b
Proof
  gen_tac >> Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def,
       vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

(* The address-collision branch of eval_create, in the shape the interpreter's
   body has once the pre-conditions are resolved. *)
Theorem create_collision_contract_storage[local]:
  contract_storage_well_formed cx s /\
  create_soft_failure rof "create address collision"
    (s with accounts updated_by (vfmExecution$increment_nonce sender)) = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  Cases_on `rof` >>
  gvs[create_soft_failure_def, return_def, raise_def] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `s` >>
  simp[increment_nonce_update_frame]
QED

(* The EVM-backed tail of eval_create: the interpreter applies the prelude to
   its state, while the adapter receives the original accounts and computes
   its own prelude.  NONE restores the rollback accounts; SOME installs the
   adapter's final accounts, transient storage, and pending deletions.  Both
   outcomes are covered by the protected-storage adapter-boundary postulate. *)
Theorem create_evm_tail_contract_storage[local]:
  protected_storage_creates_preserve cx /\
  contract_storage_well_formed cx s /\
  (case run_create_evm sender address initcode value s.accounts
          s.tStorage s.pending_deletions txp of
     NONE => do
       x <- update_accounts (K (create_rollback_accounts sender s.accounts));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt,accounts',tStorage',logs',revertData,pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
            SOME v => do
              x <- append_logs logs';
              return (Value (AddressV new_addr))
            od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
          od)
     (s with accounts updated_by
             (create_prelude_accounts sender address value)) = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  (* The case expression is under-applied, so split the adapter result first. *)
  Cases_on `run_create_evm sender address initcode value s.accounts
              s.tStorage s.pending_deletions txp`
  >| [(* adapter NONE: rollback the interpreter's prelude *)
      (gs[] >>
       Cases_on `rof` >>
       gvs[bind_apply, ignore_bind_apply, update_accounts_def,
           create_soft_failure_def, return_def, raise_def,
           evaluation_state_accfupds] >>
       drule_all protected_storage_creates_preserve_run_create_evm_NONE >>
       metis_tac[]),
      (* adapter SOME: install its accounts, transient storage and deletions *)
      (PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
       gvs[bind_apply, ignore_bind_apply, update_accounts_def,
           update_transient_def, update_pending_deletions_def, append_logs_def, update_pending_deletions_def,
           return_def, raise_def, AllCaseEqs(),
           evaluation_state_accfupds] >>
       drule_all protected_storage_creates_preserve_run_create_evm >>
       strip_tac >>
       rename1 `contract_storage_well_formed cx
         (s with <|accounts := new_accounts; tStorage := new_tStorage|>)` >>
       irule contract_storage_well_formed_accounts_transient_frame >>
       qexists_tac `s with <|accounts := new_accounts;
                             tStorage := new_tStorage|>` >>
       simp[evaluation_state_accfupds])]
QED

Theorem eval_create_contract_storage_postulate[local]:
  protected_storage_creates_preserve cx /\
  contract_storage_well_formed cx st /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs` >-
    gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys` >-
    gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, check_def, return_def, raise_def, AllCaseEqs()] >>
  rename1 `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
            SOME code_info` >>
  (* Rejecting oversized initcode cannot alter protected storage. *)
  Cases_on `code_info.cc_size_ok` >>
  (* COND_RATOR eta-expands the two pre-conditions, so the following gvs splits
     them into (balance, collision) = (T,T), (T,F), (F,T), (F,F) *)
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      get_pending_deletions_def, update_transient_def, check_def, assert_def,
      return_def, raise_def,
      AllCaseEqs(), COND_RATOR] >|
  [(* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* address collision: only the sender nonce is bumped *)
   (drule_all create_collision_contract_storage >> metis_tac[]),
   (* the EVM-backed tail *)
   (drule_all create_evm_tail_contract_storage >> metis_tac[])]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx
          (int_calls_expr (Call _ (CreateTarget _ _ _) es _))` mp_tac >>
       simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env
        (Call _ (CreateTarget _ _ _) es _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    Cases_on `kind` >>
    rule_assum_tac (REWRITE_RULE [create_kind_11, create_kind_distinct]) >>
    rpt BasicProvers.VAR_EQ_TAC
    >~ [`RawCreate`] >- suspend "StorageRawCreate"
    >~ [`CreateFromBlueprint raw_args`] >- (
      rename1 `CreateFromBlueprint raw_args` >>
      full_simp_tac bool_ss [create_kind_11, create_kind_distinct] >>
      `well_typed_exprs env (TAKE (if has_salt then 4 else 3) es)` by
        metis_tac[well_typed_exprs_TAKE] >>
      `well_typed_exprs env (DROP (if has_salt then 4 else 3) es)` by
        metis_tac[well_typed_exprs_DROP] >>
      `call_evaluation_safe cx
         (int_calls_exprs (TAKE (if has_salt then 4 else 3) es))` by
        metis_tac[call_evaluation_safe_exprs_TAKE] >>
      `call_evaluation_safe cx
         (int_calls_exprs (DROP (if has_salt then 4 else 3) es))` by
        metis_tac[call_evaluation_safe_exprs_DROP] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st` >>
      rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st =
                 (prefix_res,prefix_st)` >>
      first_x_assum drule_all >> strip_tac >>
      `runtime_consistent env cx prefix_st` by
        metis_tac[eval_exprs_preserves_runtime_consistent,
                  runtime_storage_consistent_runtime] >>
      `runtime_storage_consistent env cx prefix_st` by
        metis_tac[runtime_storage_consistent_intro,
                  runtime_storage_consistent_layout] >>
      Cases_on `prefix_res` >> gvs[]
      >- (
        rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st =
                   (INL prefix,prefix_st)` >>
        Cases_on `check_create_blueprint has_salt prefix prefix_st` >>
        rename1 `check_create_blueprint has_salt prefix prefix_st =
                   (gate_res,gate_st)` >>
        `gate_st = prefix_st` by (
          qpat_x_assum `check_create_blueprint has_salt prefix prefix_st = _`
            (mp_tac o Q.AP_TERM `SND`) >> simp[]) >>
        gvs[] >>
        rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st =
                   (INL prefix,prefix_st)` >>
        Cases_on `gate_res` >> gvs[]
        >- (
          Cases_on `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st` >>
          rename1 `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st =
                     (suffix_res,suffix_st)` >>
          ORACLE_STORAGE_TAC >>
          first_x_assum drule_all >> strip_tac >>
          Cases_on `suffix_res` >> gvs[]
          >- (rename1 `read_results cx results suffix_st` >>
              Cases_on `read_results cx results suffix_st` >>
              drule read_results_state >> strip_tac >> gvs[] >>
              rename1 `read_results cx results suffix_st = (read_res,suffix_st)` >>
              Cases_on `read_res` >> gvs[] >> strip_tac >> gvs[] >>
              metis_tac[eval_create_contract_storage_postulate]) >>
          strip_tac >> gvs[]) >>
        strip_tac >> gvs[]) >>
      strip_tac >> gvs[]) >>
    full_simp_tac bool_ss [create_kind_11, create_kind_distinct] >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[] >> strip_tac >>
    (* A constructor runs arbitrary EVM code, so it may write the protected
       target's own storage.  This is discharged by the adapter-boundary
       postulate, exactly as external calls use protected_storage_calls_preserve
       above. *)
    metis_tac[eval_create_contract_storage_postulate]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ _ _ _) = SOME _` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[StorageRawCreate]:
  RESUME_TAC >>
  rule_assum_tac (REWRITE_RULE [create_kind_11, create_kind_distinct]) >>
  rpt (qpat_x_assum `T` kall_tac) >>
  `well_typed_exprs env (TAKE 2 es) /\
   well_typed_exprs env (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)) /\
   well_typed_exprs env (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 2 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 2 es) st` >>
  rename1 `eval_exprs cx (TAKE 2 es) st = (prefix_res,prefix_st)` >>
  qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE 2 es) /\ _ ==> _`
    drule_all >> strip_tac >>
  `runtime_consistent env cx prefix_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx prefix_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  Cases_on `prefix_res`
  >- (qpat_assum `eval_exprs cx (TAKE 2 es) st = _`
        (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
      qpat_x_assum `!s prefix t ctor_es nargs. eval_exprs cx (TAKE 2 es) s = (INL prefix,t) /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      rule_assum_tac (REWRITE_RULE [LENGTH_DROP]) >>
      Cases_on `eval_expr_results cx
        (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) prefix_st` >>
      rename1 `eval_expr_results _ _ prefix_st = (capture_res,capture_st)` >>
      ORACLE_STORAGE_TAC >>
      qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> _`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_assum `eval_expr_results _ _ prefix_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `read_results cx x' capture_st` >>
          rename1 `read_results cx x' capture_st = (read_res,read_st)` >>
          drule read_results_state >> strip_tac >>
          Cases_on `read_res`
          >- (qpat_x_assum `!s prefix t ctor_es nargs s1 rs t1 s2 args t2. _ ==> _`
                (drule o SIMP_RULE (srw_ss()) []) >>
              disch_then drule >> disch_then drule >> strip_tac >>
              qpat_x_assum `read_st = capture_st` (SUBST_ALL_TAC o SYM) >>
              `runtime_consistent env cx read_st` by
                (qpat_x_assum `runtime_consistent env cx prefix_st` mp_tac >>
                 simp[runtime_consistent_def] >> strip_tac >>
                 drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
                 simp[runtime_consistent_def]) >>
              `runtime_storage_consistent env cx read_st` by
                metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
              qpat_assum `read_results cx _ capture_st = _`
                (fn th => simp_tac(srw_ss())[th, bind_apply]) >>
              Cases_on `eval_exprs cx
                (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) read_st` >>
              rename1 `eval_exprs _ _ read_st = (salt_res,salt_st)` >>
              ORACLE_STORAGE_TAC >>
              first_x_assum drule_all >> strip_tac >>
              Cases_on `salt_res` >> gvs[] >> strip_tac >> gvs[] >>
              metis_tac[eval_create_contract_storage_postulate]) >>
          gvs[] >> strip_tac >> gvs[]) >>
      gvs[LET_THM, bind_apply] >> strip_tac >> gvs[]) >>
  gvs[] >> strip_tac >> gvs[]
QED

Theorem eval_iterator_success_values_typed[local]:
  well_typed_iterator env ty it /\ runtime_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_iterator it) /\
  eval_iterator cx it st = (INL vs,st') ==>
  ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
        EVERY (value_has_type tyv) vs
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 3 eval_scc_type_sound_mutual) >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
      (int_calls_stmt (For id typ it n body'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts body'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_iterator it` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
     simp[runtime_storage_consistent_def, runtime_consistent_def,
          env_consistent_def, env_context_consistent_def]) >>
  `?env_after. type_stmts (extend_local env id typ F)
       ret_ty body' = SOME env_after` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[]
  >- (rpt strip_tac >>
      gvs[bind_apply, return_def, raise_def, runtime_storage_consistent_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res,st1)` >>
  strip_tac >>
  qpat_x_assum `!env' ty' st' res' st''. _` drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_iterator_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  ORACLE_STORAGE_TAC >>
  Cases_on `iter_res` >> gvs[bind_apply, return_def, raise_def]
  >- (
    drule_all eval_iterator_success_values_typed >> strip_tac >> gvs[] >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH x)` >>
    gvs[bind_apply, check_def, assert_def, return_def, raise_def]
    >- (
      qpat_x_assum `!s'' vs t. _`
        (qspecl_then [`st`, `x`, `st1`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then
        [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `res`, `st'`] mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum irule >>
      qpat_x_assum `do assert T _; eval_for _ _ _ _ _ od _ = _` mp_tac >>
      rw[bind_def, ignore_bind_def, assert_def, return_def] ) >>
    rpt strip_tac >>
    gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem for_body_decompose_storage[local]:
  stp.scopes <> [] /\
  finally (try do x <- eval_stmts cx body_stmts; return F od handle_loop_exception)
    pop_scope stp = (res,st') ==>
  ?res_body st_body.
    eval_stmts cx body_stmts stp = (res_body,st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    ((?x. res_body = INL x) ==> res = INL F) /\
    (res_body = INR ContinueException ==> res = INL F) /\
    (res_body = INR BreakException ==> res = INL T) /\
    (!e. res_body = INR e /\ e <> ContinueException /\ e <> BreakException ==>
         res = INR e) /\
    (!e. res = INR e ==> res_body = INR e)
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `?hd tl. r.scopes = hd::tl` by (
    imp_res_tac vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem push_scope_with_var_preserves_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tyv /\
  value_has_type tyv v /\ well_formed_type_value tyv /\
  id NOTIN FDOM env.var_types /\
  push_scope_with_var id tyv v st = (INL (),st') ==>
  runtime_storage_consistent (extend_local env id ty F) cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `env_consistent env cx st` by gvs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `env_consistent (extend_local env id ty F) cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))` by (
    irule push_scope_with_var_env_consistent >>
    metis_tac[]) >>
  `state_well_typed
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))` by (
    gvs[runtime_storage_consistent_def, runtime_consistent_def,
        state_well_typed_def, scope_well_typed_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
  `runtime_consistent (extend_local env id ty F) cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))` by
    (simp[runtime_consistent_def] >> metis_tac[runtime_consistent_def]) >>
  `contract_storage_well_formed cx st` by
    metis_tac[runtime_storage_consistent_storage] >>
  `contract_storage_well_formed cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))` by (
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st` >> simp[] >>
    gen_tac >> Cases_on `b` >>
    simp[vyperStorageBackendTheory.get_storage_def]) >>
  metis_tac[runtime_storage_consistent_intro,
            runtime_storage_consistent_layout]
QED


Resume eval_scc_storage_preservation_results_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))` by
    simp[Abbr`stp`] >>
  `stp.scopes <> []` by simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  rewrite_tac[ignore_bind_def] >>
  drule for_body_decompose_storage >>
  disch_then (qspecl_then [`st_after`, `loop_res`, `cx`, `body'`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tyv v` by fs[] >>
  `runtime_storage_consistent (extend_local env id ty F) cx stp` by (
    irule push_scope_with_var_preserves_runtime_storage_consistent >>
    conj_tac >- (qpat_assum `id NOTIN FDOM env.var_types` ACCEPT_TAC) >>
    qexistsl_tac [`st`, `tyv`, `v`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  ORACLE_STORAGE_TAC >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `contract_storage_well_formed cx st_after` by (
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st_body` >> simp[] >>
    gen_tac >> Cases_on `b` >>
    simp[vyperStorageBackendTheory.get_storage_def]) >>
  `eval_for cx tyv id body' [v] st =
     ((case loop_res of INL broke => INL () | INR e => INR e), st_after)` by (
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         push_scope_with_var_def, return_def, Abbr`stp`] >>
    qpat_assum `finally _ _ stp = (loop_res,st_after)`
      (fn th => rewrite_tac[th]) >>
    Cases_on `loop_res` >>
    simp[Once evaluate_def, return_def]) >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st_after` by (
    irule eval_for_preserves_runtime_consistent >>
    conj_tac >- (qpat_assum `functions_well_typed cx` ACCEPT_TAC) >>
    qexistsl_tac [`body'`, `env_after`, `id`,
      `case loop_res of INL broke => INL () | INR e => INR e`,
      `ret_ty`, `st`, `ty`, `tyv`, `[v]`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  `runtime_storage_consistent env cx st_after` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  ORACLE_STORAGE_TAC >>
  Cases_on `loop_res`
  >- (Cases_on `x`
      >- (`st' = st_after` by (
            qpat_x_assum `(case (INL T,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
            simp[return_def]) >>
          qpat_x_assum `st' = st_after` SUBST_ALL_TAC >>
          qpat_assum `contract_storage_well_formed cx st_after` ACCEPT_TAC)
      >- (
        `eval_for cx tyv id body' vs st_after = (res,st')` by (
          qpat_x_assum `(case (INL F,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
          simp[return_def]) >>
        qpat_x_assum `!s'' x t s''' broke t'. _`
          (qspecl_then [`st`, `()`, `stp`, `stp`, `F`, `st_after`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_assum `push_scope_with_var id tyv v st = (INL (),stp)` ACCEPT_TAC) >>
          conj_tac >- (rewrite_tac[ignore_bind_def] >> first_assum ACCEPT_TAC) >>
          simp[]) >>
        disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                                 `st_after`, `res`, `st'`] mp_tac) >>
        impl_tac >-
          (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
        simp[]))
  >- (`st' = st_after` by (
        qpat_x_assum `(case (INR y,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
        simp[]) >>
      qpat_x_assum `st' = st_after` SUBST_ALL_TAC >>
      qpat_assum `contract_storage_well_formed cx st_after` ACCEPT_TAC)
QED




Resume eval_scc_storage_preservation_results_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v8 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v8 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- (strip_tac >>
      `well_typed_expr env e' /\
       (well_typed_expr env e \/ ?base_vt. type_place_expr env e = SOME base_vt)` by (
        qpat_x_assum `well_typed_expr env (Subscript v8 e e')` mp_tac >>
        simp_tac(srw_ss())[Once well_typed_expr_def] >> metis_tac[]) >>
      (qpat_x_assum `eval_expr cx (Subscript v8 e e') st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_expr cx e st` >>
      rename1 `eval_expr cx e st = (base_res,st1)` >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st1` by metis_tac[] >>
      `runtime_consistent env cx st` by
        metis_tac[runtime_storage_consistent_runtime] >>
      `runtime_consistent env cx st1` by
        metis_tac[eval_expr_preserves_runtime_consistent,
                  eval_expr_place_preserves_runtime_consistent] >>
      `runtime_storage_consistent env cx st1` by
        metis_tac[runtime_storage_consistent_intro,
                  runtime_storage_consistent_layout] >>
      Cases_on `base_res` >> gvs[return_def, raise_def]
      >- (rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
          Cases_on `eval_expr cx e' st1` >>
          rename1 `eval_expr cx e' st1 = (index_res,st2)` >>
          ORACLE_STORAGE_TAC >>
          first_x_assum drule_all >> strip_tac >>
          `contract_storage_well_formed cx st2` by metis_tac[] >>
          `runtime_consistent env cx st2` by
            metis_tac[eval_expr_preserves_runtime_consistent] >>
          `runtime_storage_consistent env cx st2` by
            metis_tac[runtime_storage_consistent_intro,
                      runtime_storage_consistent_layout] >>
          Cases_on `index_res` >> gvs[return_def, raise_def] >>
          Cases_on `read_result cx x st2` >>
          rename1 `read_result cx x st2 = (value_res,st3)` >>
          `st3 = st2` by metis_tac[read_result_state] >>
          gvs[] >>
          Cases_on `value_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> imp_res_tac select_result_state >> gvs[]) >>
      (strip_tac >> gvs[]))) >>
  gen_tac >> strip_tac >>
  `well_typed_expr env e' /\ ?base_vt. type_place_expr env e = SOME base_vt` by (
    qpat_x_assum `type_place_expr env (Subscript v8 e e') = SOME vt` mp_tac >>
    simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript v8 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_place_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `base_res` >> gvs[return_def, raise_def]
  >- (rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (index_res,st2)` >>
      ORACLE_STORAGE_TAC >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st2` by metis_tac[] >>
      `runtime_consistent env cx st2` by
        metis_tac[eval_expr_preserves_runtime_consistent] >>
      `runtime_storage_consistent env cx st2` by
        metis_tac[runtime_storage_consistent_intro,
                  runtime_storage_consistent_layout] >>
      Cases_on `index_res` >> gvs[return_def, raise_def] >>
      Cases_on `read_result cx x st2` >>
      rename1 `read_result cx x st2 = (value_res,st3)` >>
      `st3 = st2` by metis_tac[read_result_state] >>
      gvs[] >>
      Cases_on `value_res` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac select_result_state >> gvs[]) >>
  (strip_tac >> gvs[])
QED


(* Formerly local; saved under the same name for the assigned T6.2 boundary
   and direct Hyp0/no-admission certification. No compatibility alias. *)
Theorem extcall_return_tail_preserves_contract_storage:
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  protected_storage_calls_preserve cx /\
  oracle_storage_ok cx st /\
  well_typed_opt env drv /\
  (returnData = [] /\ IS_SOME drv ==>
    call_evaluation_safe cx (int_calls_expr (THE drv))) /\
  (returnData = [] /\ IS_SOME drv ==>
    !env0 st0 res0 st0'.
      runtime_storage_consistent env0 cx st0 /\ source_supply st0 /\
      functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr (THE drv)) /\
      protected_storage_calls_preserve cx /\
      oracle_storage_ok cx st0 /\
      eval_expr cx (THE drv) st0 = (res0,st0') ==>
      (well_typed_expr env0 (THE drv) ==>
       contract_storage_well_formed cx st0') /\
      (!vt. type_place_expr env0 (THE drv) = SOME vt ==>
       contract_storage_well_formed cx st0')) /\
  (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
   else do
     ret_val <- lift_sum_runtime
       (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
     return (Value ret_val)
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `returnData = [] /\ IS_SOME drv` >> gvs[]
  >- (Cases_on `drv` >> gvs[Once well_typed_expr_def] >>
      first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `(do _ od) st = (res,st')` mp_tac >>
  simp[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData` >>
  gvs[return_def, raise_def] >>
  metis_tac[runtime_storage_consistent_storage]
QED

Theorem extcall_pending_storage_frame[local,simp]:
  contract_storage_well_formed cx
    (st with <|logs := logs; accounts := accounts; tStorage := transient;
               pending_deletions updated_by deletions|>) <=>
  contract_storage_well_formed cx
    (st with <|logs := logs; accounts := accounts; tStorage := transient|>)
Proof
  eq_tac >> strip_tac
  >- (irule contract_storage_well_formed_accounts_transient_frame >>
      qexists_tac `st with <|accounts := accounts; tStorage := transient;
                           logs := logs; pending_deletions updated_by deletions|>` >>
      simp[]) >>
  irule contract_storage_well_formed_accounts_transient_frame >>
  qexists_tac `st with <|accounts := accounts; tStorage := transient; logs := logs|>` >>
  simp[]
QED

Theorem extcall_pending_runtime_storage_frame[local,simp]:
  runtime_storage_consistent env cx
    (st with <|logs := logs; accounts := accounts; tStorage := transient;
               pending_deletions updated_by deletions|>) <=>
  runtime_storage_consistent env cx
    (st with <|logs := logs; accounts := accounts; tStorage := transient|>)
Proof
  simp[extcall_pending_storage_frame,
       runtime_storage_consistent_def, runtime_consistent_def,
       env_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def, state_well_typed_def]
QED

Theorem eval_ext_call_effects_storage_preserved[local]:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  protected_storage_calls_preserve cx /\
  eval_ext_call_effects cx target calldata value_opt gas st.accounts st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       lift_option_def, get_transient_storage_def, update_accounts_def,
       update_transient_def, append_logs_def, update_pending_deletions_def,
       return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, adopt_call_outcome_INR_storage] >>~-
  ([`run_ext_call _ _ _ _ _ _ _ _ = SOME _`],
   irule run_ext_call_storage_frame >> simp[] >> metis_tac[]) >>
  metis_tac[take_call_outcome_storage_suffix,
            take_adopt_call_outcome_storage_suffix]
QED

Theorem eval_ext_call_storage_preserved[local]:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  protected_storage_calls_preserve cx /\
  eval_ext_call cx static skip_check sig opts vs st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  PairCases_on `sig` >>
  Cases_on `vs` >- (simp[eval_ext_call_def, raise_def] >> rw[] >> gvs[]) >>
  Cases_on `static` >> Cases_on `st.outcomes` >>
  asm_simp_tac (srw_ss())
      [eval_ext_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, lift_option_type_def, lift_option_def,
       lift_sum_runtime_def, get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def, append_logs_def,
       update_pending_deletions_def, return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  (* Previous composition attempted drule_all directly while the effects
     evaluation was still beneath the calldata/precheck monadic binds:
     drule_all eval_ext_call_effects_storage_preserved >> simp[] *)
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      get_accounts_def, assert_def, AllCaseEqs()] >>
  gvs[COND_RATOR, vfmTypesTheory.option_CASE_rator,
      vfmTypesTheory.sum_CASE_rator, bind_def, ignore_bind_def,
      return_def, raise_def, get_accounts_def, assert_def, AllCaseEqs()] >>
  drule_all eval_ext_call_effects_storage_preserved >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_ExtCall]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by (
      qpat_x_assum `call_evaluation_safe cx
          (int_calls_expr (Call _ (ExtCall _ _ _ _) es _))`
        mp_tac >> pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
      irule call_evaluation_safe_append_left >>
      goal_assum (drule_at Any)) >>
    `well_typed_exprs env es` by metis_tac[ext_call_args_typed] >>
    PairCases_on `sig` >>
    `well_typed_exprs env (TAKE 1 es) /\
     well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
     well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
      metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
    `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
     call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
     call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
      metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
    Cases_on `eval_exprs cx (TAKE 1 es) st` >>
    rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE 1 es) /\ _ ==> _`
      drule_all >> strip_tac >>
    `runtime_consistent env cx target_st` by
      metis_tac[eval_exprs_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
    `runtime_storage_consistent env cx target_st` by
      metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
    Cases_on `target_res`
    >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
          (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
        qpat_x_assum `!s target t nargs. eval_exprs cx (TAKE 1 es) s = (INL target,t) /\ _ ==> _`
          (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
        Cases_on `eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
        rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
        ORACLE_STORAGE_TAC >>
        qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> _`
          drule_all >> strip_tac >>
        Cases_on `capture_res`
        >- (qpat_x_assum `!s target t nargs s1 rs t1. _ ==> _`
              (drule o SIMP_RULE (srw_ss()) []) >> disch_then drule >> strip_tac >>
            `runtime_consistent env cx capture_st` by
              (qpat_x_assum `runtime_consistent env cx target_st` mp_tac >>
               simp[runtime_consistent_def] >> strip_tac >>
               drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
               simp[runtime_consistent_def]) >>
            `runtime_storage_consistent env cx capture_st` by
              metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
            qpat_assum `eval_expr_results _ _ target_st = _`
              (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
            Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
            rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
            ORACLE_STORAGE_TAC >>
            first_x_assum drule_all >> strip_tac >>
            `runtime_consistent env cx kw_st` by
              metis_tac[eval_exprs_preserves_runtime_consistent] >>
            `runtime_storage_consistent env cx kw_st` by
              metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
            rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
            Cases_on `kw_res` >> gvs[]
            >- (Cases_on `read_results cx x' kw_st` >>
                drule read_results_state >> strip_tac >> gvs[] >>
                rename1 `read_results cx _ kw_st = (read_res,kw_st)` >>
                Cases_on `read_res` >> gvs[]
                >- (ORACLE_STORAGE_TAC >> metis_tac[eval_ext_call_storage_preserved]) >>
                strip_tac >> gvs[]) >>
            strip_tac >> gvs[]) >>
        rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
        gvs[LET_THM, bind_apply] >> strip_tac >> gvs[]) >>
    rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
    gvs[] >> strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp_tac (srw_ss()) [Once well_typed_expr_def]
QED

Theorem lift_option_type_INL_eq_storage[local]:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt` >> simp[lift_option_type_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem fn_sigs_consistent_FLOOKUP_storage[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt,fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    sig.param_types = MAP SND params /\
    sig.num_defaults = LENGTH dflts
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem intcall_call_evaluation_safe_args_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall callee) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr (Call loc (IntCall callee) es extra)` >>
  simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_needed_defaults_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_exprs (DROP n dflts))
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_needed_defaults >>
  conj_tac
  >- (qexistsl_tac [`args`, `fn_body`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_body_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_stmts fn_body)
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_body >>
  conj_tac
  >- (qexistsl_tac [`args`, `dflts`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED

Theorem contract_storage_well_formed_stk[local]:
  contract_storage_well_formed (cx with stk updated_by f) st <=>
  contract_storage_well_formed cx st
Proof
  `st with scopes := st.scopes = st` by
    gvs[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`scopes` |-> `st.scopes`]
    contract_storage_well_formed_stk_scopes) >>
  asm_rewrite_tac[]
QED


Theorem oracle_storage_ok_stk[simp]:
  oracle_storage_ok (cx with stk updated_by f) st <=> oracle_storage_ok cx st
Proof
  simp[oracle_storage_ok_def, contract_storage_well_formed_stk]
QED

Theorem protected_storage_calls_preserve_stk[local]:
  protected_storage_calls_preserve (cx with stk updated_by f) <=>
  protected_storage_calls_preserve cx
Proof
  simp[protected_storage_calls_preserve_def,
       contract_storage_well_formed_stk,
       run_delegate_call_def, make_delegate_call_state_def]
QED


Theorem protected_storage_creates_preserve_stk[local]:
  protected_storage_creates_preserve (cx with stk updated_by f) <=>
  protected_storage_creates_preserve cx
Proof
  simp[protected_storage_creates_preserve_def,
       contract_storage_well_formed_stk]
QED


Theorem intcall_defaults_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  env_body.current_src = src_id_opt /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members ==>
  runtime_storage_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src_id_opt,fn))
    (st with scopes := [FEMPTY]) /\
  functions_well_typed (cx with stk updated_by CONS (src_id_opt,fn))
Proof
  rpt strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  qpat_assum `runtime_consistent env cx st` (fn th =>
    map_every assume_tac
      (CONJUNCTS (REWRITE_RULE [runtime_consistent_def] th))) >>
  qspecl_then [`env`, `env_body`, `cx`, `st`, `src_id_opt`, `fn`] mp_tac
    intcall_default_env_side_conditions >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `env_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src_id_opt,fn))
     (st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (st with scopes := [FEMPTY])` by
    gvs[state_well_typed_def, scope_well_typed_def] >>
  `contract_storage_well_formed cx st` by
    qpat_assum `runtime_storage_consistent env cx st` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th)) >>
  `contract_storage_well_formed
     (cx with stk updated_by CONS (src_id_opt,fn))
     (st with scopes := [FEMPTY])` by
    simp[contract_storage_well_formed_stk_scopes] >>
  `storage_layout_safe cx` by
    qpat_assum `runtime_storage_consistent env cx st` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_layout th)) >>
  `storage_layout_safe (cx with stk updated_by CONS (src_id_opt,fn))` by
    simp[] >>
  simp[runtime_storage_consistent_def, runtime_consistent_def]
QED



Theorem type_place_expr_Call_IntCall_NONE_storage[local]:
  !env ty src_id_opt fn es drv.
    type_place_expr env (Call ty (IntCall (src_id_opt,fn)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_storage_preservation_results_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >> all_tac >>
  reverse conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
    simp[type_place_expr_Call_IntCall_NONE_storage]) >>
  strip_tac >>
  PRED_ASSUM (fn tm =>
    is_forall tm andalso is_imp (snd (strip_forall tm)) andalso
    can (find_term (fn t => is_const t andalso same_const ``eval_expr_results`` t))
      (snd (dest_imp (snd (strip_forall tm)))))
    (mk_asm "actual_ih") >>
  PRED_ASSUM (fn tm =>
    is_forall tm andalso is_imp (snd (strip_forall tm)) andalso
    can (find_term (fn t => is_const t andalso same_const ``eval_exprs`` t))
      (snd (dest_imp (snd (strip_forall tm)))))
    (mk_asm "default_ih") >>
  PRED_ASSUM (fn tm =>
    is_forall tm andalso is_imp (snd (strip_forall tm)) andalso
    can (find_term (fn t => is_const t andalso same_const ``eval_stmts`` t))
      (snd (dest_imp (snd (strip_forall tm)))))
    (mk_asm "body_ih") >>
  suspend "intcall_storage"
QED

Theorem finally_unless_halt_preserves_state_predicate[local]:
  !P f g st res st'.
  (!r s. f st = (r,s) ==> P s) /\
  (!s r s'. P s /\ g s = (r,s') ==> P s') /\
  finally_unless_halt f g st = (res,st') ==>
  P st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >> rename1 `f st = (main_res,main_st)` >>
  `P main_st` by metis_tac[] >>
  Cases_on `main_res` >> TRY (rename1 `INR exc` >> Cases_on `exc`) >>
  gvs[finally_unless_halt_def, ignore_bind_def, bind_def, return_def, raise_def] >>
  Cases_on `g main_st` >> rename1 `g main_st = (cleanup_res,cleanup_st)` >>
  Cases_on `cleanup_res` >> gvs[] >> metis_tac[]
QED

Theorem intcall_halt_cleanup_preserves_contract_storage[local]:
  !cx f st prev nr is_view res st'.
  (!r s. f st = (r,s) ==> contract_storage_well_formed cx s) /\
  storage_layout_safe cx /\
  finally_unless_halt (finally f (pop_function prev))
    (if nr /\ ~is_view then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `!s r s'. contract_storage_well_formed cx s /\
     pop_function prev s = (r,s') ==> contract_storage_well_formed cx s'` by
    (rw[pop_function_def, set_scopes_def, return_def] >>
     irule contract_storage_well_formed_scopes >> simp[]) >>
  `!s r s'. contract_storage_well_formed cx s /\
     (if nr /\ ~is_view then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()) s = (r,s') ==> contract_storage_well_formed cx s'` by
    (rpt strip_tac >> Cases_on `nr /\ ~is_view` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     drule_all release_nonreentrant_lock_preserves_contract_storage_well_formed >>
     simp[]) >>
  `!r s. finally f (pop_function prev) st = (r,s) ==>
     contract_storage_well_formed cx s` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`contract_storage_well_formed cx`, `f`, `pop_function prev`,
                  `st`, `r`, `s`] mp_tac finally_preserves_state_predicate >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`contract_storage_well_formed cx`, `finally f (pop_function prev)`,
    `if nr /\ ~is_view then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()`, `st`, `res`, `st'`]
    mp_tac finally_unless_halt_preserves_state_predicate >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem intcall_post_push_storage[local]:
  !cx cxf fn_stmts body_st prev nr is_view rtv res st'.
    contract_storage_well_formed cx body_st /\
    storage_layout_safe cx /\
    (!bres bst.
       eval_stmts cxf fn_stmts body_st = (bres,bst) ==>
       contract_storage_well_formed cx bst) /\
    (case
       finally_unless_halt
          (finally (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function) (pop_function prev))
          (if nr /\ ~is_view then
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ())
         body_st
     of
       (INL rv,s) =>
         (case
            (case safe_cast rtv rv of
               NONE => raise (Error (TypeError "IntCall cast ret"))
             | SOME v => return v) s
          of
            (INL crv,s') => (INL (Value crv),s')
          | (INR e,s') => (INR e,s'))
     | (INR e,s) => (INR e,s)) = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `finally_unless_halt
    (finally (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
      (pop_function prev))
    (if nr /\ ~is_view then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) body_st` >>
  rename1 `_ = (cleanup_res,cleanup_st)` >>
  `contract_storage_well_formed cx cleanup_st` by
    (qspecl_then
       [`cx`, `try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function`,
        `body_st`, `prev`, `nr`, `is_view`, `cleanup_res`, `cleanup_st`]
       mp_tac intcall_halt_cleanup_preserves_contract_storage >>
     simp[] >> impl_tac
     >- metis_tac[
          try_eval_stmts_handle_function_preserves_contract_storage_well_formed] >>
     simp[]) >>
  Cases_on `cleanup_res` >> gvs[AllCaseEqs(), return_def, raise_def] >>
  qmatch_asmsub_rename_tac `safe_cast rtv cast_value` >>
  Cases_on `safe_cast rtv cast_value` >> gvs[return_def, raise_def]
QED


Resume eval_scc_storage_preservation_results_mutual[intcall_storage]:
  qhdtm_assum `call_evaluation_safe` (mk_asm "call_safe") >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    asm "call_safe" (fn th =>
      ACCEPT_TAC (MATCH_MP intcall_call_evaluation_safe_args_storage th)) >>
  qpat_assum `runtime_storage_consistent env cx st` (fn th => (
    assume_tac (MATCH_MP runtime_storage_consistent_runtime th);
    mk_asm "wf0" (MATCH_MP runtime_storage_consistent_storage th);
    mk_asm "runtime0"
      (MATCH_MP runtime_storage_consistent_runtime th))) >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[type_check_def, assert_def] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_expr_results cx es r = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by (
    asm_x "actual_ih" irule >>
    asm_x "default_ih" kall_tac >> asm_x "body_ih" kall_tac >>
    gvs[type_check_def, assert_def, return_def, lift_option_type_def,
        AllCaseEqs()] >>
    rpt conj_tac >> metis_tac[]) >>
  Cases_on `args_res` >> gvs[]
  >- (
    rename1 `eval_expr_results cx es r = (INL actual_results,args_st)` >>
    qpat_assum
      `lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" r = (INL x',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq_storage) th)) >>
    strip_tac >>
    qpat_assum
      `lift_option_type (lookup_callable_function cx.in_deploy fn x')
         "IntCall lookup_function" r = (INL x'',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq_storage) th)) >>
    strip_tac >>
    PairCases_on `x''` >> gvs[] >>
    qpat_assum `get_module_code cx src_id_opt = SOME x'`
      (mk_asm "module_ok") >>
    qpat_assum `lookup_callable_function cx.in_deploy fn x' =
                  SOME (x''0,x''1,x''2,x''3,x''4,x''5)`
      (mk_asm "lookup_ok") >>
    asm "runtime0" assume_tac >>
    `runtime_consistent env cx args_st` by (
      drule_all eval_expr_results_preserves_runtime_consistent_from_eval >> simp[]) >>
    `expr_results_typed (env,cx,args_st) es actual_results` by (
      drule_all eval_expr_results_success_typed >> simp[]) >>
    `env_consistent env cx args_st` by
      qpat_assum `runtime_consistent env cx args_st` (fn th =>
        ACCEPT_TAC (cj 1 (REWRITE_RULE [runtime_consistent_def] th))) >>
    `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by
      (qpat_x_assum `FLOOKUP env.fn_sigs (src_id_opt,fn) = SOME _`
         (fn th => simp[th])) >>
    mp_tac (Q.INST [`st` |-> `args_st`, `ts` |-> `x'`,
                    `fm` |-> `x''0`, `nr` |-> `x''1`,
                    `args` |-> `x''2`, `dflts` |-> `x''3`,
                    `ret` |-> `x''4`, `fn_body` |-> `x''5`]
             callable_body_typing_from_env_consistent) >>
    simp[] >>
    disch_then (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `env_body` (qx_choose_then `ret_tv`
        (qx_choose_then `env_after`
          (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
    qpat_x_assum `!id typ. MEM (id,typ) x''2 ==> _`
      (mk_asm "args_forward") >>
    qpat_x_assum `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> _`
      (mk_asm "args_var_types") >>
    qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
      (mk_asm "args_var_assignable") >>
    `env.type_defs = get_tenv cx` by (
      qpat_x_assum `env_consistent env cx args_st` mp_tac >>
      simp[env_consistent_def, env_context_consistent_def]) >>
    `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3` by (
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      drule_all fn_sigs_consistent_FLOOKUP_storage >> strip_tac >> gvs[]) >>
    `storage_layout_safe cx` by
      qpat_assum `runtime_storage_consistent env cx r` (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_storage_consistent_layout th)) >>
    `runtime_storage_consistent env cx args_st` by
      simp[runtime_storage_consistent_def] >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (Q.INST
            [`n` |-> `LENGTH x''3 - (LENGTH x''2 - LENGTH es)`]
            (MATCH_MP intcall_call_evaluation_safe_needed_defaults_storage
              (LIST_CONJ [call_th,module_th,lookup_th])))))) >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (MATCH_MP intcall_call_evaluation_safe_body_storage
            (LIST_CONJ [call_th,module_th,lookup_th]))))) >>
    simp[get_scopes_def, return_def] >>
    BasicProvers.TOP_CASE_TAC >>
    qmatch_asmsub_rename_tac
      `finally _ _ args_st = (default_res,default_st)` >>

    `well_typed_exprs (defaults_env env_body)
       (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)` by
      (irule well_typed_exprs_DROP >> first_assum ACCEPT_TAC) >>
    `runtime_storage_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src_id_opt,fn))
       (args_st with scopes := [FEMPTY]) /\
     functions_well_typed
       (cx with stk updated_by CONS (src_id_opt,fn))` by
      (irule (Q.INST [`env` |-> `env`, `cx` |-> `cx`,
                      `st` |-> `args_st`, `env_body` |-> `env_body`,
                      `src_id_opt` |-> `src_id_opt`, `fn` |-> `fn`]
               intcall_defaults_runtime_storage_consistent) >>
       simp[] >> qexists_tac `env` >> simp[]) >>
    `protected_storage_calls_preserve
       (cx with stk updated_by CONS (src_id_opt,fn))` by
      simp[protected_storage_calls_preserve_stk] >>
    ORACLE_STORAGE_TAC >>
    `!r1 s1.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)
         (args_st with scopes := [FEMPTY]) = (r1,s1) ==>
       contract_storage_well_formed cx s1` by (
      rpt strip_tac >>
      qsuff_tac `contract_storage_well_formed
        (cx with stk updated_by CONS (env_body.current_src,fn)) s1`
      >- simp[contract_storage_well_formed_stk] >>
      asm_x "default_ih" irule >>
      asm_x "actual_ih" kall_tac >> asm_x "body_ih" kall_tac >>
      gvs[type_check_def, assert_def, return_def, lift_option_type_def,
          get_scopes_def, set_scopes_def, AllCaseEqs(),
          protected_storage_creates_preserve_stk] >>
      rpt conj_tac >> metis_tac[]) >>
    `contract_storage_well_formed cx default_st` by (
      qpat_assum `contract_storage_well_formed cx args_st` (fn wf_th =>
        qpat_assum `!r1 s1. eval_exprs _ _ _ = (r1,s1) ==> _`
          (fn step_th =>
            qpat_assum `finally _ _ args_st = (default_res,default_st)`
              (fn fin_th =>
                ACCEPT_TAC (MATCH_MP
                  default_eval_exprs_finally_preserves_contract_storage_well_formed
                  (LIST_CONJ [wf_th,step_th,fin_th])))))) >>
    reverse (Cases_on `default_res`) >- (rpt strip_tac >> gvs[]) >>
    rename1 `_ = (INL dflt_vs,default_st)` >>
    gvs[] >> strip_tac >>
    drule default_eval_exprs_finally_success >> strip_tac >>

    `runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (args_st with scopes := [FEMPTY])` by
      first_assum (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_storage_consistent_runtime th)) >>
    `exprs_runtime_typed (defaults_env env_body)
       (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)
       dflt_vs` by (
      drule eval_exprs_success_runtime_typed_from_eval >> simp[]) >>
    `runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (env_body.current_src,fn)) pre` by (
      drule_all eval_exprs_preserves_runtime_consistent_from_eval >> simp[]) >>
    `state_well_typed pre /\ accounts_well_typed pre.accounts` by
      (drule runtime_consistent_state_accounts_storage >> simp[]) >>
    `EVERY scope_well_typed args_st.scopes` by
      (irule runtime_consistent_scopes_well_typed_storage >>
       goal_assum (drule_at Any)) >>
    `state_well_typed (pre with scopes := args_st.scopes)` by
      (drule_all state_accounts_scopes_storage >> simp[]) >>
    `vyperImmutableMetadataFrame$immutable_metadata_frame
       (args_st with scopes := [FEMPTY]) pre` by (
      irule (cj 6 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >>
      goal_assum (drule_at Any)) >>
    `vyperImmutableMetadataFrame$immutable_metadata_frame
       args_st (pre with scopes := args_st.scopes)` by
      (qpat_x_assum `vyperImmutableMetadataFrame$immutable_metadata_frame
          (args_st with scopes := [FEMPTY]) pre` mp_tac >>
       rpt (pop_assum kall_tac) >>
       simp[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
       metis_tac[]) >>
    Cases_on `read_results cx actual_results default_st` >>
    rename1 `read_results cx actual_results default_st = (read_res,read_st)` >>
    drule read_results_state >> strip_tac >> gvs[] >>
    namedCases_on `read_res` ["actual_vs", "read_ex"] >> gvs[] >>
    `exprs_runtime_typed env es actual_vs` by (
      irule (cj 2 read_results_restored_runtime_typed) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
    gvs[] >>
    Cases_on
      `bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs)` >>
    gvs[Excl "evaluate_type_def", lift_option_type_def, bind_apply,
        return_def, raise_def] >>
    `LENGTH x''2 - LENGTH es <= LENGTH x''3 /\ LENGTH es <= LENGTH x''2` by (
      qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
      simp[type_check_def, assert_def] >>
      IF_CASES_TAC >> gvs[] >> decide_tac) >>
    qspecl_then
      [`cx`, `env`, `env_body`, `x''2`, `x''3`, `es`, `actual_vs`,
       `dflt_vs`, `DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3`,
       `pre`]
      mp_tac intcall_bind_arguments_from_runtime_typed >>
    (impl_tac >- (
      simp[L "args_forward", L "args_var_types", L "args_var_assignable",
           env_consistent_def, env_context_consistent_def] >>
      map_every (fn label => asm label mp_tac)
        ["args_forward", "args_var_types", "args_var_assignable"] >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
    disch_then (qx_choose_then `call_env` strip_assume_tac) >>
    qpat_assum `bind_arguments (get_tenv cx) x''2
                    (actual_vs ++ dflt_vs) = SOME call_env`
      (mk_asm "bind_call_env") >>
    `call_env = x` by (
      asm "bind_call_env" mp_tac >>
      qpat_x_assum `bind_arguments (get_tenv cx) x''2
                       (actual_vs ++ dflt_vs) = SOME x` mp_tac >>
      simp[]) >>
    gvs[] >>
    `!lock_res lock_st.
       (if x''1 then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
              (x''0 = View \/ x''0 = Pure)
        else return ()) (pre with scopes := args_st.scopes) = (lock_res,lock_st) ==>
       contract_storage_well_formed cx lock_st` by (
      rpt strip_tac >>
      Cases_on `x''1` >> gvs[return_def, raise_def] >>
      Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
      drule_all acquire_nonreentrant_lock_preserves_contract_storage_well_formed >>
      simp[]) >>
    Cases_on
      `(if x''1 then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
              (x''0 = View \/ x''0 = Pure)
        else return ()) (pre with scopes := args_st.scopes)` >>
    rename1 `_ (pre with scopes := args_st.scopes) = (lock_res,lock_st)` >>
    `contract_storage_well_formed cx lock_st` by (
      qpat_assum `!lock_res lock_st. _`
        (qspecl_then [`lock_res`, `lock_st`] irule) >>
      simp[]) >>
    Cases_on `lock_res` >>
    gvs[ignore_bind_apply, bind_apply, return_def, raise_def] >>
    `runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (env_body.current_src,fn)) pre` by (
      drule eval_exprs_preserves_runtime_consistent_from_eval >> simp[]) >>
    `lock_st.scopes = args_st.scopes /\
     lock_st.immutables = pre.immutables /\
     lock_st.accounts = pre.accounts /\
     lock_st.outcomes = pre.outcomes` by (
      drule intcall_lock_state_preserves_runtime_frame_storage >>
      simp[]) >>
    `env_immutables_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (pre with scopes := args_st.scopes)` by (
      irule env_immutables_consistent_defaults_scopes_storage >>
      irule runtime_consistent_env_immutables_storage >>
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` ACCEPT_TAC) >>
    `env_scopes_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (pre with scopes := [call_env])` by (
      qpat_assum
        `env_scopes_consistent env_body cx (pre with scopes := [call_env])`
        mp_tac >>
      simp[env_scopes_consistent_stk_irrelevant_storage]) >>
    `state_well_typed pre /\ accounts_well_typed pre.accounts` by (
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` (fn th =>
          ACCEPT_TAC (MATCH_MP runtime_consistent_state_accounts_storage th))) >>
    `EVERY scope_well_typed args_st.scopes` by (
      qpat_assum `runtime_consistent env cx args_st` (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_consistent_scopes_well_typed_storage th))) >>
    `state_well_typed (pre with scopes := args_st.scopes) /\
     accounts_well_typed (pre with scopes := args_st.scopes).accounts` by (
      irule state_accounts_scopes_storage >> simp[]) >>
    `env_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env]) /\
     state_well_typed (lock_st with scopes := [call_env]) /\
     accounts_well_typed (lock_st with scopes := [call_env]).accounts` by (
      qspecl_then
        [`env`, `env_body`, `cx`, `args_st`,
         `pre with scopes := args_st.scopes`, `lock_st`, `call_env`,
         `fn`, `x''1`, `x''0 = View \/ x''0 = Pure`]
        mp_tac intcall_live_pushed_body_preconditions >>
      (impl_tac >- simp[]) >> simp[]) >>
    `context_well_typed
       (cx with stk updated_by CONS (env_body.current_src,fn))` by (
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` (fn th =>
          ACCEPT_TAC (MATCH_MP runtime_consistent_context_storage th))) >>
    `runtime_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env])` by (
      simp[runtime_consistent_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    Cases_on
      `push_function (env_body.current_src,fn) call_env cx lock_st` >>
    rename1 `_ lock_st = (push_res,push_st)` >>
    Cases_on `push_res` >>
    gvs[ignore_bind_apply, bind_apply, push_function_def,
        return_def, raise_def] >>
    `runtime_storage_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env])` by
      simp[runtime_storage_consistent_def,
           contract_storage_well_formed_stk_scopes] >>

    (* The frame the body IH supplies, stated over the caller's cx directly.
       Nothing here is specialised to the prelude's shape. *)
    `!body_res body_st.
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn))
         x''5 (lock_st with scopes := [call_env]) = (body_res,body_st) ==>
       contract_storage_well_formed cx body_st` by (
      rpt strip_tac >>
      ORACLE_STORAGE_TAC >>
      qsuff_tac `contract_storage_well_formed
        (cx with stk updated_by CONS (env_body.current_src,fn)) body_st`
      >- simp[contract_storage_well_formed_stk] >>
      asm_x "body_ih" irule >>
      asm_x "actual_ih" kall_tac >> asm_x "default_ih" kall_tac >>
      asm "bind_call_env" assume_tac >>
      gvs[type_check_def, assert_def, get_scopes_def, set_scopes_def,
          lift_option_type_def, push_function_def, return_def,
          protected_storage_creates_preserve_stk, AllCaseEqs()] >>
      rpt (goal_assum (drule_at Any)) >>
      simp[return_def] >> metis_tac[]) >>
    (qpat_assum `_ = (res,st')` (mk_asm "suffix_eq") >>
     qmatch_asmsub_abbrev_tac `safe_cast actual_rtv _` >>
     qspecl_then
       [`cx`, `cx with stk updated_by CONS (env_body.current_src,fn)`, `x''5`,
        `lock_st with scopes := [call_env]`, `args_st.scopes`, `x''1`,
        `x''0 = View \/ x''0 = Pure`, `actual_rtv`, `res`, `st'`]
       mp_tac
       intcall_post_push_storage >>
     (impl_tac >-
       (conj_tac >-
          (irule contract_storage_well_formed_scopes >>
           first_assum ACCEPT_TAC) >>
        conj_tac >-
          (qpat_assum `storage_layout_safe cx` ACCEPT_TAC) >>
        conj_tac >-
          simp[contract_storage_well_formed_stk] >>
        asm "suffix_eq" mp_tac >> simp[])) >>
     simp[])) >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED



Resume eval_scc_storage_preservation_results_mutual[BasePlaceRoot_NameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[BasePlaceRoot_TopLevelNameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume eval_scc_storage_preservation_results_mutual[BasePlaceRoot_AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[type_place_target_AttributeTarget] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[BasePlaceRoot_SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (bt_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_place_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `bt_res` >> gvs[return_def]
  >- (
    gvs[bind_def, return_def] >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
    ORACLE_STORAGE_TAC >>
    first_x_assum drule_all >> strip_tac >>
    `contract_storage_well_formed cx st2` by metis_tac[] >>
    Cases_on `expr_res` >> gvs[bind_def, return_def]
    >- (
      qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx_value,st2)` >>
      Cases_on `read_result cx idx_value st2` >>
      rename1 `read_result cx idx_value st2 = (value_res,value_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `value_res` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac extend_place_state >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_storage_preservation_results_mutual[TargetPlace]:
  rpt gen_tac >> strip_tac >> gvs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac get_place_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[TupleStores_nil_nil]:
  gvs[Once evaluate_def, return_def, runtime_storage_consistent_def]
QED
Resume eval_scc_storage_preservation_results_mutual[TupleStores_cons_nil]:
  gvs[Once evaluate_def, raise_def, runtime_storage_consistent_def]
QED
Resume eval_scc_storage_preservation_results_mutual[TupleStores_nil_cons]:
  gvs[Once evaluate_def, raise_def, runtime_storage_consistent_def]
QED



Resume eval_scc_storage_preservation_results_mutual[TupleStore_BaseTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_targets cx (BaseTarget bt) v st = (res,st')` >>
  qpat_x_assum `well_typed_atarget _ _ _` mp_tac >>
  simp_tac(srw_ss())[well_typed_atarget_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atarget _)` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  first_x_assum drule_all >> strip_tac >>
  reverse (Cases_on `answer`)
  >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  drule_all typed_write_place_preserves_storage >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[TupleStore_TupleTarget]:
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, int_calls_atarget_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_scc_storage_preservation_results_mutual[TupleStores_cons_cons]:
  rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st')` >>
  Cases_on `tys` >- gvs[] >>
  rename1 `LIST_REL _ (g::gs) (head_ty::tail_tys)` >>
  fs[LIST_REL_CONS1] >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atargets (g::gs))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  qpat_x_assum `!env ty st res st'. _ ==> contract_storage_well_formed _ _`
    (drule_all_then strip_assume_tac) >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx middle` by
    (drule_all assign_tuple_targets_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx middle` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  reverse (Cases_on `answer`) >- (simp[] >> strip_tac >> gvs[]) >>
  qmatch_assum_rename_tac `assign_tuple_targets cx g v st = (INL unit_result,middle)` >>
  Cases_on `unit_result` >> gvs[] >>
  qpat_x_assum `!s'' t. assign_tuple_targets _ _ _ s'' = (INL (),t) ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  ORACLE_STORAGE_TAC >> first_x_assum drule_all >> simp[]
QED


Resume eval_scc_storage_preservation_results_mutual[RaiseCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Raise (RaiseCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >>
  strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def,
         runtime_storage_consistent_def] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def,
         runtime_storage_consistent_def] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def,
         runtime_storage_consistent_def] >>
  rename1
    `order_custom_error_args params
       (CustomError p positional kwargs) = SOME es` >>
  (fn g as (asl,_) =>
     let
       val ih_tm = valOf (List.find
         (fn tm => can dest_forall tm andalso
           String.isSubstring "order_custom_error_args" (term_to_string tm))
         asl)
       val ih = Q.SPECL
         [`p`, `positional`, `kwargs`, `tops`, `params`, `es`]
         (ASSUME ih_tm)
     in
       mp_tac ih g
     end) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
    (drule order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by
    (drule well_typed_exprs_perm >>
     disch_then (qspec_then `env` mp_tac) >>
     simp[custom_error_exprs_def]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qspecl_then
       [`cx`, `custom_error_exprs (CustomError p positional kwargs)`, `es`]
       mp_tac call_evaluation_safe_exprs_perm >>
     simp[custom_error_exprs_def]) >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,st1)` >>
  ORACLE_STORAGE_TAC >>
  (fn g as (asl,_) =>
     let
       val ih_tm = valOf (List.find
         (fn tm => can dest_forall tm andalso
           String.isSubstring "eval_exprs cx es st" (term_to_string tm) andalso
           not (String.isSubstring "order_custom_error_args"
             (term_to_string tm)))
         asl)
       val ih = Q.SPECL [`env`, `st`, `args_res`, `st1`] (ASSUME ih_tm)
     in
       mp_tac ih g
     end) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  Cases_on `args_res`
  >- (
    Cases_on
      `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x` >>
    gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
    imp_res_tac lift_option_state >> gvs[]) >>
  gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def]
QED


Resume eval_scc_storage_preservation_results_mutual[AssertCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Assert e (AssertCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs (custom_error_exprs err)` >> simp[]) >>
  `call_evaluation_safe cx
      (int_calls_exprs (custom_error_exprs err))` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  (fn g as (asl,_) =>
     let
       val ih_tm = valOf (List.find
         (fn tm => can dest_forall tm andalso
           String.isSubstring "eval_expr cx e st" (term_to_string tm) andalso
           not (String.isSubstring "eval_exprs" (term_to_string tm)))
         asl)
       val ih = Q.SPECL [`env`, `st`, `expr_res`, `st1`] (ASSUME ih_tm)
     in
       mp_tac ih g
     end) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  `contract_storage_well_formed cx st1` by
    fs[runtime_storage_consistent_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
    drule_all eval_expr_success_storage_facts >> strip_tac >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (rr,rs)` >>
    imp_res_tac read_result_state >> gvs[] >>
    reverse (Cases_on `rr`)
    >- (simp[switch_BoolV_def, bind_def] >> strip_tac >> gvs[]) >>
    rename1 `read_result cx x st1 = (INL cv,st1)` >>
    `value_runtime_typed env (expr_type e) cv` by
      (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    reverse (Cases_on `b`) >> simp[switch_BoolV_def, bind_def, return_def]
    >- (
      Cases_on `err` >>
      Cases_on `get_module_code cx (FST p)`
      >- (rpt (qpat_x_assum `!x. _` kall_tac) >> simp[raise_def] >> strip_tac >> gvs[]) >>
      rename1 `get_module_code cx (FST p) = SOME tops` >>
      Cases_on `lookup_custom_error_args_in (SND p) tops`
      >- (rpt (qpat_x_assum `!x. _` kall_tac) >> simp[raise_def] >> strip_tac >> gvs[]) >>
      rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
      Cases_on `order_custom_error_args params (CustomError p l l0)`
      >- (rpt (qpat_x_assum `!x. _` kall_tac) >> simp[raise_def] >> strip_tac >> gvs[]) >>
      rename1
        `order_custom_error_args params
           (CustomError p positional kwargs) = SOME es` >>
      qpat_x_assum `!s tv t id positional kwargs tops params es. _`
        (drule_then mp_tac) >>
      disch_then (qspecl_then [`p`, `positional`, `kwargs`, `tops`, `params`, `es`] mp_tac) >>
      simp_tac (srw_ss()) [] >> strip_tac >>
      `PERM (custom_error_exprs
          (CustomError p positional kwargs)) es` by
        (drule order_custom_error_args_perm >> simp[]) >>
      `well_typed_exprs env es` by
        (drule well_typed_exprs_perm >>
         disch_then (qspec_then `env` mp_tac) >>
         simp[custom_error_exprs_def]) >>
      `call_evaluation_safe cx (int_calls_exprs es)` by
        (qspecl_then
           [`cx`, `custom_error_exprs (CustomError p positional kwargs)`,
            `es`]
           mp_tac call_evaluation_safe_exprs_perm >>
         simp[custom_error_exprs_def]) >>
      Cases_on `eval_exprs cx es st1` >>
      rename1 `eval_exprs cx es st1 = (args_res,st2)` >>
      ORACLE_STORAGE_TAC >>
      qpat_x_assum `!env st res st'. _ /\ _ ==> contract_storage_well_formed cx st'`
        (qspecl_then [`env`, `st1`, `args_res`, `st2`] mp_tac) >>
      impl_tac >- gvs[] >>
      strip_tac >>
      Cases_on `args_res`
      >- (Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x'` >>
          rpt (qpat_x_assum `!x. _` kall_tac) >>
          gvs[bind_def, lift_option_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[]) >>
      rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[bind_def, raise_def] >> rpt strip_tac >> gvs[]) >>
    rpt (qpat_x_assum `!x. _` kall_tac) >> rpt strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> rpt strip_tac >> gvs[]
QED


Finalise eval_scc_storage_preservation_results_mutual

Theorem eval_scc_storage_preservation_mutual =
  LIST_CONJ (List.take (CONJUNCTS eval_scc_storage_preservation_results_mutual, 10));


val () = let
  val th = eval_scc_storage_preservation_mutual
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
in
  if null (Thm.hyp th) andalso null axioms andalso
     List.all (fn oracle => oracle = "DISK_THM") oracles then
    print "Storage SCC finalised with no hypotheses or admitted dependencies\n"
  else raise Fail "storage SCC retains hypotheses or admitted dependencies"
end;

Theorem eval_stmt_preserves_contract_storage_well_formed:
  type_stmt env ret_ty s = SOME env' /\
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmt s) /\
  protected_storage_calls_preserve cx /\
  protected_storage_creates_preserve cx /\
  oracle_storage_ok cx st /\
  eval_stmt cx s st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 1 eval_scc_storage_preservation_mutual]
QED

Theorem eval_stmts_preserves_contract_storage_well_formed:
  type_stmts env ret_ty ss = SOME env' /\
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  protected_storage_calls_preserve cx /\
  protected_storage_creates_preserve cx /\
  oracle_storage_ok cx st /\
  eval_stmts cx ss st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 2 eval_scc_storage_preservation_mutual]
QED

Theorem eval_expr_preserves_contract_storage_well_formed:
  well_typed_expr env e /\
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  protected_storage_calls_preserve cx /\
  protected_storage_creates_preserve cx /\
  oracle_storage_ok cx st /\
  eval_expr cx e st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 5 eval_scc_storage_preservation_mutual]
QED

Theorem eval_exprs_preserves_contract_storage_well_formed:
  well_typed_exprs env es /\
  runtime_storage_consistent env cx st /\ source_supply st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  protected_storage_calls_preserve cx /\
  protected_storage_creates_preserve cx /\
  oracle_storage_ok cx st /\
  eval_exprs cx es st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 6 eval_scc_storage_preservation_mutual]
QED

val () = List.app (fn (name, th) =>
  if null (Thm.hyp th) andalso
     List.all (fn tag => tag = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) andalso
     null (#2 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Unexpected proof assumption: " ^ name))
  (DB.thms "vyperTypeEvalStoragePreservation");
