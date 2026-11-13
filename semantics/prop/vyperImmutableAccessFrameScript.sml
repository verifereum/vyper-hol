(*
 * What expr_accesses says about the running contract's immutables at run
 * time: an expression with no risky call (no external call, send,
 * raw_call, create or call-family builtin, in it or in an internal
 * function it reaches) changes the immutable id of module src only if its
 * accesses write StateRef (src,id).
 *
 * The function premise ties the accesses analysis to the code that runs,
 * as in vyperStorageAccessFrame: an internal call the expression reaches
 * is looked up in mods, and the function the evaluator calls is the one
 * function_accesses reads (or the empty constructor lookup_function
 * synthesizes).
 *
 * TOP-LEVEL:
 *   eval_expr_unwritten_immutable
 *)

Theory vyperImmutableAccessFrame
Ancestors
  vyperSubscriptOverlap vyperInterpreter vyperState vyperContext
  vyperStorageAccessFrame vyperLocalAccessFrame
  vyperTypeInvariants vyperTypeCallStackSoundness vyperTypeCallGraphSoundness
  vyperTypeCallGraph list alist finite_map
  vyperTypeInitialState vyperPlaceFrames vyperImmutablesPreservation
  vyperStatePreservation vyperStorageBackend

(* Why it holds (a reader may ignore this): immutables change only through
   an ImmutablePlace written by Assign, AugAssign, Append or Pop (inside an
   expression only Pop), and such a place is resolved from a target rooted
   at TopLevelNameTarget (src,id), whose accesses_target emits
   WriteAcc (StateRef (src,id)).  A write to another immutable updates
   another key of the same module's map (set_immutable), or another
   module's map (set_source_immutables keeps the others).  Internal calls
   keep cx.txn.target, and a reached callee's own accesses are in
   expr_accesses through reached_functions, as in
   vyperStorageAccessFrame's evaluate_finite_frame. *)

(* Closed term abbreviations, not additional semantic definitions. *)
val immutable_observation = ``\cx src id (st:evaluation_state).
  FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
             NONE => FEMPTY
           | SOME imms => get_source_immutables src imms) id``;

val immutable_frame = ``\cx A st st'. !src id.
  ~MEM (WriteAcc (StateRef (src,id))) A ==>
  ^immutable_observation cx src id st' =
  ^immutable_observation cx src id st``;

Theorem set_immutable_key_frame[local]:
  set_immutable cx s n tv v st = (res,st') /\ (s,n) <> (src,id) ==>
  ^immutable_observation cx src id st' =
  ^immutable_observation cx src id st
Proof
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[set_immutable_def, get_address_immutables_def,
       lift_option_type_def, bind_def, raise_def, return_def,
       set_address_immutables_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `src = s` >>
  gvs[get_source_immutables_set_same, get_source_immutables_set_other,
      FLOOKUP_UPDATE]
QED

Theorem write_place_key_frame[local]:
  write_place cx p v st = (res,st') /\
  (!path. p <> ImmutablePlace src id path) ==>
  ^immutable_observation cx src id st' =
  ^immutable_observation cx src id st
Proof
  Cases_on `p`
  >- (rpt strip_tac >> drule write_storage_place_immutables >> simp[])
  >- (rpt strip_tac >> drule write_memory_place_immutables >> simp[]) >>
  strip_tac >> rename1 `ImmutablePlace isrc iid ipath` >>
  `(isrc,iid) <> (src,id)` by
    (strip_tac >> gvs[] >> first_x_assum (qspec_then `ipath` mp_tac) >> simp[]) >>
  qpat_x_assum `!path. _` kall_tac >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule set_immutable_key_frame >>
  disch_then (qspecl_then [`src`,`id`] mp_tac) >> impl_tac
  >- metis_tac[pairTheory.PAIR_EQ] >>
  strip_tac >> gvs[]
QED

Theorem append_place_key_frame[local]:
  append_place cx p v st = (res,st') /\
  (!path. p <> ImmutablePlace src id path) ==>
  ^immutable_observation cx src id st' =
  ^immutable_observation cx src id st
Proof
  Cases_on `p` >>
  TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
       TRY (rename1 `ArrayTV et bd` >> Cases_on `bd`)) >>
  simp[append_place_def, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_storage_backend_state >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  imp_res_tac lift_sum_state >> gvs[] >>
  imp_res_tac write_storage_place_immutables >>
  imp_res_tac write_memory_place_immutables >>
  imp_res_tac write_storage_slot_immutables >> gvs[] >>
  drule write_place_key_frame >> simp[]
QED

Theorem pop_place_key_frame[local]:
  pop_place cx p st = (res,st') /\
  (!path. p <> ImmutablePlace src id path) ==>
  ^immutable_observation cx src id st' =
  ^immutable_observation cx src id st
Proof
  Cases_on `p` >>
  TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
       TRY (rename1 `ArrayTV et bd` >> Cases_on `bd`)) >>
  simp[pop_place_def, bind_def, ignore_bind_def, check_def, assert_def,
       get_scopes_def, type_check_def,
       set_scopes_def, pairTheory.UNCURRY, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_storage_backend_state >>
  gvs[get_scopes_def, return_def] >> imp_res_tac lift_option_type_state >>
  imp_res_tac type_check_state >> imp_res_tac lift_sum_state >> gvs[] >>
  imp_res_tac write_storage_slot_immutables >>
  gvs[set_scopes_def, return_def] >>
  imp_res_tac get_immutables_state >> gvs[] >>
  drule set_immutable_key_frame >> simp[]
QED

Theorem immutable_frame_refl[local]:
  ^immutable_frame cx A st st
Proof
  simp[]
QED

Theorem immutable_frame_trans[local]:
  ^immutable_frame cx A st mid /\ ^immutable_frame cx A mid st' ==>
  ^immutable_frame cx A st st'
Proof
  metis_tac[]
QED

Theorem immutable_frame_stack[local]:
  ^immutable_frame (cx with stk := stk) A st st' =
  ^immutable_frame cx A st st'
Proof
  simp[]
QED

(* Target provenance: indices may have effects, but cannot change the root. *)
Theorem lookup_global_immutable_origin[local]:
  lookup_global cx s n st =
    (INL (PlaceR (ImmutablePlace src id path)),st') ==>
  s = src /\ n = id
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_base_place_immutable_access[local]:
  !t cx st src id path st'.
    eval_base_place cx t st =
      (INL (PlaceR (ImmutablePlace src id path)),st') ==>
    MEM (WriteAcc (StateRef (src,id))) (accesses_target t)
Proof
  measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def,
          type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
          AllCaseEqs()]
  >- (PairCases_on `p` >> simp[Once evaluate_def] >> strip_tac >>
      drule lookup_global_immutable_origin >>
      simp[accesses_expr_def])
  >> simp[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def] >>
  rpt strip_tac >>
  `?path0. pv = PlaceR (ImmutablePlace src id path0)` by
    (Cases_on `pv` >> gvs[extend_place_def, raise_def]
     >- (Cases_on `p` >>
         gvs[extend_place_def, extend_memory_place_def, bind_def,
             ignore_bind_def, return_def, AllCaseEqs()] >>
         drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
         simp[]) >>
     gvs[extend_place_def, bind_def, lift_option_type_def, return_def,
         raise_def, value_type_CASE_rator, AllCaseEqs()]) >>
  gvs[] >> first_x_assum (qspec_then `b` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem eval_target_place_immutable_access[local]:
  eval_target_place cx t st = (INL (ImmutablePlace src id path),st') ==>
  MEM (WriteAcc (StateRef (src,id))) (accesses_target t)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_immutable_access]
QED

(* Access/closure interface shared by the untyped constructor proofs. *)
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

Theorem immutable_safe_accesses_drop[local]:
  !es n. ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) ==>
    ^safe_accesses A R (accesses_exprs (DROP n es)) (int_calls_exprs (DROP n es))
Proof
  Induct >> simp[accesses_expr_def, int_calls_expr_def] >>
  Cases_on `n` >> simp[accesses_expr_def, int_calls_expr_def] >>
  metis_tac[]
QED

Theorem lock_if_nr_immutables[local]:
  lock_if_nr cx nr is_view st = (res,st') ==> st'.immutables = st.immutables
Proof
  Cases_on `nr` >> Cases_on `is_view` >>
  simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[return_def, raise_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[]
QED

Theorem unlock_if_nr_immutables[local]:
  unlock_if_nr cx nr is_view st = (res,st') ==> st'.immutables = st.immutables
Proof
  Cases_on `nr /\ ~is_view` >>
  simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_immutables]
QED

val im_stmts = ``\cx ss. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_stmts ss) (int_calls_stmts ss) /\
  eval_stmts cx ss st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_exprs = ``\cx es. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) /\
  eval_exprs cx es st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_results = ``\cx es. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) /\
  eval_expr_results cx es st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_expr = ``\cx e. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_expr e) (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==> ^immutable_frame cx A st st'``;

val im_base = ``\cx t. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_target t) (int_calls_target t) /\
  eval_base_place cx t st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_target = ``\cx t. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_target t) (int_calls_target t) /\
  eval_target_place cx t st = (res,st') ==> ^immutable_frame cx A st st'``;

val im_stmt = ``\cx s. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_stmt s) (int_calls_stmt s) /\
  eval_stmt cx s st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_iterator = ``\cx it. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_iterator it) (int_calls_iterator it) /\
  eval_iterator cx it st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_for = ``\cx tyv id body vs. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_stmts body) (int_calls_stmts body) /\
  eval_for cx tyv id body vs st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_atarget = ``\cx g v. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_atarget g) (int_calls_atarget g) /\
  assign_tuple_targets cx g v st = (res,st') ==> ^immutable_frame cx A st st'``;
val im_atargets = ``\cx gs vs. !A R st res st'.
  ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_atargets gs) (int_calls_atargets gs) /\
  assign_tuple_target_list cx gs vs st = (res,st') ==> ^immutable_frame cx A st st'``;

(* Exact constructor premises, with the shared frame predicates substituted. *)
val immutable_ind_cases = let
  val (_,core) = strip_forall (concl evaluate_ind)
  val cs = strip_conj (fst (dest_imp core))
  val preds = [("P1",im_stmts),("P4",im_expr),("P5",im_exprs),
    ("P6",im_base),("P7",im_target),("P10",im_results)]
  fun inst t = subst (List.mapPartial (fn (n,p) =>
    Option.map (fn v => v |-> p)
      (List.find (fn v => fst (dest_var v) = n) (free_vars t))) preds) t
in map inst cs end;
fun immutable_constructor_case name = valOf (List.find (fn t =>
  can (find_term (fn u => is_const u andalso fst (dest_const u) = name))
    (snd (strip_imp (snd (strip_forall t))))) immutable_ind_cases);

fun immutable_predicate_cases name = let
  val (_,core) = strip_forall (concl evaluate_ind)
  val raw = strip_conj (fst (dest_imp core))
  fun matches t = let
    val c = snd (strip_imp (snd (strip_forall t)))
  in fst (dest_var (fst (strip_comb c))) = name end
in map #2 (List.filter (matches o #1) (ListPair.zip (raw,immutable_ind_cases))) end;

Theorem evaluate_immutable_name_case[local]:
  ^(immutable_constructor_case "Name")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem evaluate_immutable_global_case[local]:
  ^(immutable_constructor_case "TopLevelName")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_global_state >> gvs[]
QED

Theorem evaluate_immutable_flag_case[local]:
  ^(immutable_constructor_case "FlagMember")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_flag_mem_state >> gvs[]
QED

Theorem evaluate_immutable_literal_case[local]:
  ^(immutable_constructor_case "Literal")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_basename_case[local]:
  ^(immutable_constructor_case "NameTarget")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem evaluate_immutable_baseglobal_case[local]:
  ^(immutable_constructor_case "TopLevelNameTarget")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_global_state >> gvs[]
QED

Theorem evaluate_immutable_attribute_case[local]:
  ^(immutable_constructor_case "Attribute")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def,
      int_calls_expr_def] >>
  imp_res_tac select_result_state >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem subscript_base_read_state[local]:
  (if b then bind (read_result cx r) (\v. return (Value v)) else return r) s =
  (res, t) ==> t = s
Proof
  Cases_on `b` >> simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[]
QED

Theorem evaluate_immutable_subscript_case[local]:
  ^(immutable_constructor_case "Subscript")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def,
      int_calls_expr_def] >>
  imp_res_tac subscript_base_read_state >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  last_x_assum (drule_then (drule_then assume_tac)) >>
  rpt (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_baseattribute_case[local]:
  ^(immutable_constructor_case "AttributeTarget")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def,
      int_calls_expr_def] >>
  imp_res_tac extend_place_state >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_basesubscript_case[local]:
  ^(immutable_constructor_case "SubscriptTarget")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def,
      int_calls_expr_def] >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!s r t. eval_base_place _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_target_case[local]:
  ^(hd (immutable_predicate_cases "P7"))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_place_state >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_exprs_nil_case[local]:
  ^(hd (immutable_predicate_cases "P5"))
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_exprs_cons_case[local]:
  ^(List.nth (immutable_predicate_cases "P5",1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      accesses_expr_def, int_calls_expr_def] >>
  imp_res_tac read_result_state >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_results_nil_case[local]:
  ^(hd (immutable_predicate_cases "P10"))
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_results_cons_case[local]:
  ^(List.nth (immutable_predicate_cases "P10",1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      accesses_expr_def, int_calls_expr_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c. eval_expr _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_risky_cases[local]:
  ^(list_mk_conj (map immutable_constructor_case
    ["Send","ExtCall","RawCallTarget","RawCallCalldataTarget","CreateTarget"]))
Proof
  rpt conj_tac >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `~MEM RiskyAcc (accesses_expr _)` mp_tac >>
  simp[accesses_expr_def, risky_call_target_def]
QED

Theorem evaluate_immutable_struct_case[local]:
  ^(immutable_constructor_case "StructLit")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      accesses_expr_def, int_calls_expr_def, accesses_named_exprs_map,
      vyperTypeEvalSoundnessTheory.int_calls_exprs_MAP_SND] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_typebuiltin_case[local]:
  ^(immutable_constructor_case "TypeBuiltin")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(),
      accesses_expr_def, int_calls_expr_def] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_ifexp_case[local]:
  ^(immutable_constructor_case "IfExp")
Proof
  BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
       return_def, raise_def] >> strip_tac >>
  fs[accesses_expr_def, int_calls_expr_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  rpt (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` (mk_asm "closed") >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >>
  asm_x "closed" assume_tac >>
  rpt (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  rpt (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` kall_tac) >>
  metis_tac[]
QED

Theorem evaluate_immutable_pop_case[local]:
  ^(immutable_constructor_case "Pop")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_expr_def, int_calls_expr_def] >>
  qpat_x_assum `eval_expr _ (Pop _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> reverse strip_tac
  >- (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  rename1 `pop_place cx p mid = _` >>
  `!path. p <> ImmutablePlace src id path` by
    metis_tac[eval_target_place_immutable_access] >>
  drule_all pop_place_key_frame >> metis_tac[]
QED

Theorem evaluate_immutable_rawrevert_case[local]:
  ^(immutable_constructor_case "RawRevert")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(),
      accesses_expr_def, risky_call_target_def, int_calls_expr_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >>
  imp_res_tac lift_option_type_state >> gvs[]
QED

Theorem evaluate_immutable_rawlog_case[local]:
  ^(immutable_constructor_case "RawLog")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(),
      accesses_expr_def, risky_call_target_def, int_calls_expr_def,
      lift_option_type_def, vyperMiscTheory.option_CASE_rator,
      check_not_static_def, check_def, push_log_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_selfdestruct_case[local]:
  ^(immutable_constructor_case "SelfDestructTarget")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(),
      accesses_expr_def, risky_call_target_def, int_calls_expr_def,
      lift_option_type_def, vyperMiscTheory.option_CASE_rator,
      check_not_static_def, check_def, get_accounts_def] >>
  imp_res_tac transfer_value_immutables >> gvs[] >>
  Cases_on `cx.txn.created_in_tx` >>
  gvs[update_accounts_def, update_pending_deletions_def, bind_def,
      return_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_builtin_case[local]:
  ^(immutable_constructor_case "Builtin")
Proof
  simp[NoAsms, type_check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len`
      >- (gvs[accesses_expr_def, int_calls_expr_def] >>
          Cases_on `es` >> gvs[builtin_args_length_ok_def, accesses_expr_def,
            int_calls_expr_def, DISJ_IMP_THM, FORALL_AND_THM] >>
          qpat_x_assum `!A R st res st'. _`
            (qspecl_then [`A`,`R`] mp_tac) >> simp[] >>
          disch_tac >>
          qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
          simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
            assert_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
          imp_res_tac result_array_length_state >> gvs[] >>
          rpt strip_tac >> first_x_assum irule >> simp[] >>
          first_assum ACCEPT_TAC) >>
      Cases_on `bt = Bop In \/ bt = Bop NotIn`
      >- (gvs[accesses_expr_def, int_calls_expr_def] >>
          qpat_x_assum `!A R st res st'. _`
            (qspecl_then [`A`,`R`] mp_tac) >> simp[] >> disch_tac >>
          `!s r t. eval_exprs cx es s = (r,t) ==> ^immutable_frame cx A s t` by
            (BETA_TAC >> rpt strip_tac >> first_x_assum irule >> simp[] >>
             first_assum ACCEPT_TAC) >>
          qpat_x_assum `!st res st'. (_ /\ eval_exprs _ _ _ = _) ==> _` kall_tac >>
          qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
          qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
          simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
            assert_def, return_def, raise_def, lift_option_type_def,
            vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >> strip_tac >>
          imp_res_tac lift_sum_state >> gvs[] >>
          first_x_assum drule_all >> simp[]) >>
      Cases_on `bt = Env MsgGas`
      >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
            assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac next_gas_reading_state >> gvs[]) >>
      Cases_on `code_slice_source bt es`
      >- (gvs[accesses_expr_def, int_calls_expr_def] >>
          qpat_x_assum `!A R st res st'. _`
            (qspecl_then [`A`,`R`] mp_tac) >> simp[] >> disch_tac >>
          qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
          simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
            assert_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
          imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
          imp_res_tac precompile_call_success_state >> gvs[] >>
          rpt strip_tac >> first_x_assum irule >> simp[] >>
          first_assum ACCEPT_TAC) >>
      rename1 `code_slice_source bt es = SOME p` >> PairCases_on `p` >>
      gvs[accesses_expr_def, int_calls_expr_def] >>
      `(!x. MEM x (accesses_exprs (TL es)) ==> MEM x (accesses_exprs es)) /\
       (!x. MEM x (accesses_expr p1) ==> MEM x (accesses_exprs es)) /\
       (!c. MEM c (int_calls_exprs (TL es)) ==> MEM c (int_calls_exprs es)) /\
       (!c. MEM c (int_calls_expr p1) ==> MEM c (int_calls_exprs es))` by
        (qpat_x_assum `code_slice_source _ _ = SOME _` mp_tac >>
         rpt (pop_assum kall_tac) >> rw[code_slice_source_SOME] >>
         gvs[accesses_expr_def, int_calls_expr_def]) >>
      `!s r t. eval_exprs cx (TL es) s = (r,t) ==> ^immutable_frame cx A s t` by
        (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!A R st res st'. _`
           (qspecl_then [`A`,`R`,`s`,`r`,`t`] mp_tac) >>
         impl_tac >- (simp[accesses_expr_def, int_calls_expr_def] >> metis_tac[]) >>
         simp[]) >>
      `!s0 tvs s r t. eval_exprs cx (TL es) s0 = (INL tvs,s) /\
         eval_exprs cx [p1] s = (r,t) ==> ^immutable_frame cx A s t` by
        (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!s3 tvs t'. eval_exprs cx (TL es) s3 = (INL tvs,t') ==> _`
           (qspecl_then [`s0`,`tvs`,`s`] mp_tac) >>
         impl_tac >- simp[] >>
         disch_then (qspecl_then [`A`,`R`,`s`,`r`,`t`] mp_tac) >>
         impl_tac >- (simp[accesses_expr_def, int_calls_expr_def] >> metis_tac[]) >>
         simp[]) >>
      qpat_x_assum `!A R st res st'. _ /\ _ /\ eval_exprs cx (TL es) st = _ ==> _`
        kall_tac >>
      qpat_x_assum `!s3 tvs t'. eval_exprs cx (TL es) s3 = (INL tvs,t') ==> _` kall_tac >>
      qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
      qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
      imp_res_tac precompile_call_success_state >> gvs[] >>
      rpt strip_tac >> metis_tac[]) >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, raise_def]
QED

val immutable_stmt_ind_cases = map (fn t =>
  subst (List.mapPartial (fn (n,p) =>
    Option.map (fn v => v |-> p)
      (List.find (fn v => fst (dest_var v) = n) (free_vars t)))
    [("P0",im_stmt),("P2",im_iterator),("P3",im_for),
     ("P8",im_atarget),("P9",im_atargets)]) t) immutable_ind_cases;
fun immutable_stmt_case name = valOf (List.find (fn t =>
  can (find_term (fn u => is_const u andalso fst (dest_const u) = name))
    (snd (strip_imp (snd (strip_forall t))))) immutable_stmt_ind_cases);

fun immutable_stmt_cases name = List.filter (fn t =>
  can (find_term (fn u => is_const u andalso fst (dest_const u) = name))
    (snd (strip_imp (snd (strip_forall t))))) immutable_stmt_ind_cases;

Theorem evaluate_immutable_return_none_case[local]:
  ^(immutable_stmt_case "Return")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_return_some_case[local]:
  ^(List.nth (immutable_stmt_cases "Return",1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, raise_def, AllCaseEqs(),
      accesses_stmt_def, accesses_expr_def, int_calls_stmt_def,
      int_calls_expr_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_raise_bare_case[local]:
  ^(immutable_stmt_case "RaiseBare")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_raise_unreachable_case[local]:
  ^(immutable_stmt_case "RaiseUnreachable")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_raise_reason_case[local]:
  ^(immutable_stmt_case "RaiseReason")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, raise_def, lift_option_type_def,
      return_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs(),
      accesses_stmt_def, accesses_raise_reason_def, int_calls_stmt_def,
      int_calls_raise_reason_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_pass_case[local]:
  ^(immutable_stmt_case "Pass")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_break_case[local]:
  ^(immutable_stmt_case "Break")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_continue_case[local]:
  ^(immutable_stmt_case "Continue")
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_exprstmt_case[local]:
  ^(immutable_stmt_case "Expr")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs(),
      accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_log_case[local]:
  ^(immutable_stmt_case "Log")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, lift_option_def,
      vyperMiscTheory.option_CASE_rator, check_not_static_def, check_def,
      assert_def, return_def, raise_def, push_log_def, AllCaseEqs(),
      accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_annassign_case[local]:
  ^(immutable_stmt_case "AnnAssign")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs(),
      accesses_stmt_def, int_calls_stmt_def] >>
  imp_res_tac read_result_state >> imp_res_tac new_variable_immutables >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_array_iterator_case[local]:
  ^(immutable_stmt_case "Array")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs(),
      accesses_iterator_def, int_calls_iterator_def] >>
  imp_res_tac read_result_state >> imp_res_tac array_iterator_results_state >>
  gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_range_iterator_case[local]:
  ^(immutable_stmt_case "Range")
Proof
  BETA_TAC >> rpt strip_tac >>
  fs[accesses_iterator_def, int_calls_iterator_def, DISJ_IMP_THM,
     FORALL_AND_THM] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_append_case[local]:
  ^(immutable_stmt_case "Append")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `eval_stmt _ (Append _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c. eval_target_place _ _ _ = _ ==> _`
    drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  `!p s m. eval_target_place cx t s = (INL p,m) ==>
     !path. p <> ImmutablePlace src id path` by
    metis_tac[eval_target_place_immutable_access] >>
  imp_res_tac append_place_key_frame >> metis_tac[]
QED

Theorem evaluate_immutable_assign_base_case[local]:
  ^(immutable_stmt_case "Assign")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, accesses_atarget_def, int_calls_stmt_def,
      int_calls_atarget_def] >>
  qpat_x_assum `eval_stmt _ (Assign _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  `!p s m. eval_target_place cx t s = (INL p,m) ==>
     !path. p <> ImmutablePlace src id path` by
    metis_tac[eval_target_place_immutable_access] >>
  imp_res_tac write_place_key_frame >> metis_tac[]
QED

Theorem evaluate_immutable_augassign_case[local]:
  ^(immutable_stmt_case "AugAssign")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `eval_stmt _ (AugAssign _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac read_place_state >>
  imp_res_tac place_type_value_state >> imp_res_tac lift_sum_state >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c d e f g h i. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  `!p s m. eval_target_place cx t s = (INL p,m) ==>
     !path. p <> ImmutablePlace src id path` by
    metis_tac[eval_target_place_immutable_access] >>
  imp_res_tac write_place_key_frame >> metis_tac[]
QED

fun immutable_stmt_predicate_cases name = List.filter (fn t =>
  let val c = snd (strip_imp (snd (strip_forall t)))
  in is_abs (fst (strip_comb c)) andalso
    aconv (fst (strip_comb c)) name end) immutable_stmt_ind_cases;

Theorem evaluate_immutable_stmts_nil_case[local]:
  ^(hd (immutable_stmt_predicate_cases im_stmts))
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_stmts_cons_case[local]:
  ^(List.nth (immutable_stmt_predicate_cases im_stmts,1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  rpt (qpat_x_assum `!a b. eval_stmt _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_assign_tuple_case[local]:
  ^(List.nth (immutable_stmt_cases "Assign",1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def] >>
  qpat_x_assum `eval_stmt _ (Assign _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

(* Fix analysis parameters before consuming a guarded recursive IH. *)
Theorem immutable_exprs_frame_rule[local]:
  ^im_exprs cx es /\ ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) ==>
  !st res st'. eval_exprs cx es st = (res,st') ==>
    ^immutable_frame cx A st st'
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem immutable_results_frame_rule[local]:
  ^im_results cx es /\ ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) ==>
  !st res st'. eval_expr_results cx es st = (res,st') ==>
    ^immutable_frame cx A st st'
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem immutable_exprs_frame_rule[local]:
  ^im_exprs cx es /\ ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_exprs es) (int_calls_exprs es) ==>
  !st res st'. eval_exprs cx es st = (res,st') ==>
    ^immutable_frame cx A st st'
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem immutable_stmts_frame_rule[local]:
  ^im_stmts cx ss /\ ^callable_closed cx A R /\
  ^safe_accesses A R (accesses_stmts ss) (int_calls_stmts ss) ==>
  !st res st'. eval_stmts cx ss st = (res,st') ==>
    ^immutable_frame cx A st st'
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC
QED

(* Select the actual callable without exposing closure in consumers. *)
Theorem immutable_callable_safe[local]:
  !cx A R src fn ts mut nr args dflts ret body.
  ^callable_closed cx A R /\ MEM (src,fn) R /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  ^safe_accesses A R (accesses_exprs dflts) (int_calls_exprs dflts) /\
  ^safe_accesses A R (accesses_stmts body) (int_calls_stmts body)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` drule_all >>
  simp[function_int_calls_def, safe_accesses_append]
QED

(* Wrapper rules retain the effects of failed computations as well. *)
Theorem immutable_frame_finally[local]:
  (!r mid. f st = (r,mid) ==> ^immutable_frame cx A st mid) /\
  (!s r t. g s = (r,t) ==> ^immutable_frame cx A s t) /\
  finally f g st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  Cases_on `f st` >> Cases_on `q` >>
  simp[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[immutable_frame_trans]
QED

Theorem immutable_frame_finally_unless_halt[local]:
  (!r mid. f st = (r,mid) ==> ^immutable_frame cx A st mid) /\
  (!s r t. g s = (r,t) ==> ^immutable_frame cx A s t) ==>
  !res st'. finally_unless_halt f g st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  Cases_on `f st` >> Cases_on `q` >> TRY (Cases_on `y`) >>
  simp[finally_unless_halt_def, ignore_bind_def, bind_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[immutable_frame_trans]
QED

Theorem immutable_pop_scope_frame[local]:
  pop_scope st = (res,st') ==> ^immutable_frame cx A st st'
Proof
  simp[pop_scope_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem immutable_switch_bool_frame[local]:
  (!s r t. f s = (r,t) ==> ^immutable_frame cx A s t) /\
  (!s r t. g s = (r,t) ==> ^immutable_frame cx A s t) /\
  switch_BoolV cx tv f g st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  simp[switch_BoolV_def, bind_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >>
  rpt (qpat_x_assum `!s r t. _` drule_all >> strip_tac) >>
  metis_tac[]
QED

Theorem evaluate_immutable_if_case[local]:
  ^(immutable_stmt_case "If")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def, DISJ_IMP_THM, FORALL_AND_THM,
      push_scope_def, return_def] >>
  qpat_x_assum `eval_stmt _ (If _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `!a b c. eval_expr _ _ _ = _ ==> _`
    drule >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_tac) >>
  qpat_x_assum `!st res st'. _` drule_all >> simp[] >> strip_tac >>
  `!s r t. eval_stmts cx ss1 s = (r,t) ==> ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >>
     qpat_assum `!s r t src id. (_ /\ eval_stmts cx ss1 _ = _) /\ _ ==> _` irule >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `!s r t. eval_stmts cx ss2 s = (r,t) ==> ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >>
     qpat_assum `!s r t src id. (_ /\ eval_stmts cx ss2 _ = _) /\ _ ==> _` irule >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ignore_bind push_scope _ _ = _` mp_tac >>
  simp[ignore_bind_def, bind_def, push_scope_def, return_def] >> strip_tac >>
  `^immutable_frame cx A (s'' with scopes updated_by CONS FEMPTY) st'` by
    (BETA_TAC >> rpt strip_tac >>
     drule_at (Pat `finally _ _ _ = _`) (BETA_RULE immutable_frame_finally) >>
     disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
     disch_then irule >> conj_tac
     >- (rpt strip_tac >>
         drule (BETA_RULE immutable_pop_scope_frame) >>
         disch_then (qspecl_then [`cx`,`A`] mp_tac) >> simp[]) >>
     simp[] >> rpt strip_tac >>
     drule_at (Pat `switch_BoolV _ _ _ _ _ = _`)
       (BETA_RULE immutable_switch_bool_frame) >>
     disch_then (qspec_then `A` mp_tac) >>
     gvs[]) >>
  fs[]
QED

Theorem evaluate_immutable_assert_bare_case[local]:
  ^(immutable_stmt_case "AssertBare")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, raise_def, return_def,
      AllCaseEqs(), accesses_stmt_def, accesses_assert_reason_def,
      int_calls_stmt_def, int_calls_assert_reason_def] >>
  imp_res_tac read_result_state >> gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_assert_unreachable_case[local]:
  ^(immutable_stmt_case "AssertUnreachable")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, raise_def, return_def,
      AllCaseEqs(), accesses_stmt_def, accesses_assert_reason_def,
      int_calls_stmt_def, int_calls_assert_reason_def] >>
  imp_res_tac read_result_state >> gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_assert_reason_case[local]:
  ^(immutable_stmt_case "AssertReason")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, accesses_assert_reason_def, int_calls_stmt_def,
      int_calls_assert_reason_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `!a b c. eval_expr _ _ _ = _ ==> _` drule >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
       simp[] >> disch_tac) >>
  qpat_x_assum `!st res st'. _` drule_all >> simp[] >> strip_tac >>
  `!s r t. eval_expr cx se s = (r,t) ==> ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >>
     qpat_assum `!s r t src id. (_ /\ eval_expr cx se _ = _) /\ _ ==> _` irule >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `^immutable_frame cx A s'' st'` by
    (BETA_TAC >> rpt strip_tac >>
     drule_at (Pat `switch_BoolV _ _ _ _ _ = _`)
       (BETA_RULE immutable_switch_bool_frame) >>
     disch_then (qspec_then `A` mp_tac) >> disch_then irule >>
     qpat_x_assum `switch_BoolV _ _ _ _ _ = _` kall_tac >>
     qpat_x_assum `!s r t src id. (_ /\ eval_expr cx se _ = _) /\ _ ==> _` kall_tac >>
     qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
     conj_tac
     >- (simp[return_def] >> rpt strip_tac >> gvs[]) >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs(), lift_option_type_def,
          vyperMiscTheory.option_CASE_rator, return_def, raise_def] >>
     strip_tac >> imp_res_tac read_result_state >> gvs[] >>
     qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule_all >> simp[]) >>
  fs[]
QED

Theorem evaluate_immutable_raise_custom_case[local]:
  ^(immutable_stmt_case "RaiseCustomError")
Proof
  BETA_TAC >> rpt strip_tac >>
  Cases_on `err` >>
  gvs[accesses_stmt_def, accesses_raise_reason_def, int_calls_stmt_def,
      int_calls_raise_reason_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, AllCaseEqs(), raise_def] >> strip_tac >> gvs[] >>
  Cases_on `get_module_code cx (FST p)` >> gvs[raise_def] >>
  Cases_on `lookup_custom_error_args_in (SND p) x` >> gvs[raise_def] >>
  Cases_on `order_custom_error_args x' (CustomError p l l0)` >> gvs[raise_def] >>
  `x'' = custom_error_exprs (CustomError p l l0)` by
    (gvs[vyperASTTheory.order_custom_error_args_def,
         vyperASTTheory.custom_error_exprs_def, NULL_EQ, AllCaseEqs()] >>
     drule vyperASTTheory.order_custom_error_kwargs_SOME >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >>
  `!s r t. eval_exprs cx (custom_error_exprs (CustomError p l l0)) s = (r,t) ==>
     ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!st res st'. (_ /\ eval_exprs _ _ _ = _) ==> _` kall_tac >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, lift_option_def, vyperMiscTheory.option_CASE_rator,
       AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem evaluate_immutable_assert_custom_case[local]:
  ^(immutable_stmt_case "AssertCustomError")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, accesses_assert_reason_def, int_calls_stmt_def,
      int_calls_assert_reason_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `!a b c. eval_expr _ _ _ = _ ==> _` drule >> strip_tac) >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[] >> strip_tac >>
  `!s r t. eval_stmt cx (Raise (RaiseCustomError err)) s = (r,t) ==>
     ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >>
     irule (BETA_RULE evaluate_immutable_raise_custom_case) >>
     qexistsl [`A`,`R`,`err`,`r`] >>
     simp[accesses_stmt_def, accesses_raise_reason_def, int_calls_stmt_def,
          int_calls_raise_reason_def, MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `!s tv t id positional kwargs tops params es. _`
       (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[] >> disch_tac >> rpt strip_tac >>
     first_x_assum irule >>
     goal_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `_ = CustomError _ _ _`)) >>
     qexistsl [`A'`,`R'`] >> simp[] >> metis_tac[]) >>
  `^immutable_frame cx A s'' st'` by
    (BETA_TAC >> rpt strip_tac >>
     drule_at (Pat `switch_BoolV _ _ _ _ _ = _`)
       (BETA_RULE immutable_switch_bool_frame) >>
     disch_then (qspec_then `A` mp_tac) >> disch_then irule >>
     conj_tac
     >- (simp[return_def] >> rpt strip_tac >> gvs[]) >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!s r t. eval_stmt _ _ _ = _ ==> _` (irule o BETA_RULE) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `r` >> simp[Once evaluate_def] >>
     first_assum ACCEPT_TAC) >>
  fs[]
QED

Theorem evaluate_immutable_for_nil_case[local]:
  ^(hd (immutable_stmt_cases "eval_for"))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_for_stmt_case[local]:
  ^(immutable_stmt_case "For")
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_stmt_def, int_calls_stmt_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `evaluate_type (get_tenv cx) typ`
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, lift_option_type_def, raise_def] >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `!s tyv t. lift_option_type _ _ _ = _ ==> _` mp_tac >>
  simp[lift_option_type_def, return_def] >> disch_tac >>
  qpat_x_assum `!s tyv t s1 vs t1 s2 t2. lift_option_type _ _ _ = _ /\ _ ==> _` mp_tac >>
  simp[lift_option_type_def, return_def, check_def, ignore_bind_def,
       bind_def, assert_def, raise_def] >> disch_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, ignore_bind_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_then drule_all >> simp[] >> strip_tac >>
  qpat_x_assum `!s vs t. eval_iterator _ _ _ = _ /\ _ ==> _`
    (drule_at (Pat `eval_iterator _ _ _ = _`)) >>
  simp[check_def, ignore_bind_def, bind_def, assert_def, return_def, raise_def] >>
  disch_then (qspecl_then [`A`,`R`] mp_tac) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem immutable_try_loop_frame[local]:
  (!r t. f st = (r,t) ==> ^immutable_frame cx A st t) /\
  try (ignore_bind f (return F)) handle_loop_exception st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  Cases_on `f st` >> Cases_on `q` >>
  simp[try_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac handle_loop_exception_state >> gvs[] >> metis_tac[]
QED

Theorem evaluate_immutable_for_cons_case[local]:
  ^(List.nth (immutable_stmt_cases "eval_for",1))
Proof
  BETA_TAC >> rpt strip_tac >>
  Cases_on `read_result cx r st` >> rename1 `read_result cx r st = (rr,rt)` >>
  `rt = st` by metis_tac[read_result_state] >> pop_assum SUBST_ALL_TAC >>
  reverse (Cases_on `rr`)
  >- (drule eval_for_cons_read_error >> disch_then (fn th => gvs[th])) >>
  rename1 `read_result cx r st = (INL v,st)` >>
  qpat_assum `read_result _ _ _ = _` (fn rth =>
    qpat_x_assum `!a b c d e f. read_result _ _ _ = _ /\ push_scope_with_var _ _ _ _ = _ ==> _`
      (qspecl_then [`st`,`v`,`st`] (assume_tac o SIMP_RULE bool_ss [rth])) >>
    qpat_x_assum `!a b c d e f g h i. read_result _ _ _ = _ /\ _ ==> _`
      (qspecl_then [`st`,`v`,`st`] (assume_tac o SIMP_RULE bool_ss [rth]))) >>
  qpat_x_assum `!s x t. push_scope_with_var _ _ _ _ = _ ==> _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> disch_tac >>
  qpat_x_assum `!s x t s1 t1. push_scope_with_var _ _ _ _ = _ /\ _ ==> _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> disch_tac >>
  qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
  simp[] >> disch_tac >>
  `!s r t. eval_stmts cx body' s = (r,t) ==> ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >> first_x_assum irule >> simp[] >> gvs[]) >>
  qpat_x_assum `!st res st'. (_ /\ eval_stmts _ _ _ = _) ==> _` kall_tac >>
  `!s r t. finally (try (ignore_bind (eval_stmts cx body') (return F)) handle_loop_exception) pop_scope s = (r,t) ==>
    ^immutable_frame cx A s t` by
    (BETA_TAC >> rpt strip_tac >>
     drule_at (Pat `finally _ _ _ = _`) (BETA_RULE immutable_frame_finally) >>
     disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
     disch_then irule >> conj_tac
     >- (rpt strip_tac >> drule (BETA_RULE immutable_pop_scope_frame) >>
         disch_then (qspecl_then [`cx`,`A`] mp_tac) >> simp[]) >>
     rpt strip_tac >> drule_at (Pat `try _ _ _ = _`) (BETA_RULE immutable_try_loop_frame) >>
     disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
     disch_then irule >> rpt strip_tac >> first_x_assum (drule o BETA_RULE) >> simp[]) >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  drule eval_for_cons_read >> disch_then (fn th => simp[th]) >>
  simp[push_scope_with_var_def, ignore_bind_def, return_def, bind_def] >>
  Cases_on `finally (try (ignore_bind (eval_stmts cx body') (return F)) handle_loop_exception) pop_scope
    (st with scopes updated_by CONS (FEMPTY |+ (nm, <|assignable := F; type := tyv; value := v; popped := []|>)))` >>
  reverse (Cases_on `q`)
  >- (simp[raise_def] >> strip_tac >> gvs[GSYM ignore_bind_def] >>
      qpat_assum `!s r t. finally _ _ _ = _ ==> _` drule_all >>
      disch_then (mp_tac o SRULE []) >> simp[]) >>
  simp[] >> strip_tac >> gvs[GSYM ignore_bind_def] >>
  Cases_on `x`
  >- (gvs[return_def] >>
      qpat_assum `!s r t. finally _ _ _ = _ ==> _` drule_all >>
      disch_then (mp_tac o SRULE []) >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!s t. finally _ _ _ = _ ==> _` drule >>
  disch_then (qspecl_then [`A`,`R`] mp_tac) >> simp[] >>
  disch_then drule_all >> simp[] >> strip_tac >>
  qpat_assum `!s r t. finally _ _ _ = _ ==> _` drule_all >>
  disch_then (mp_tac o SRULE []) >> simp[]
QED

Theorem evaluate_immutable_atarget_base_case[local]:
  ^(hd (immutable_stmt_predicate_cases im_atarget))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_atarget_def, int_calls_atarget_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  gvs[] >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  `!p s m. eval_target_place cx t s = (INL p,m) ==>
     !path. p <> ImmutablePlace src id path` by
    metis_tac[eval_target_place_immutable_access] >>
  imp_res_tac write_place_key_frame >> metis_tac[]
QED

Theorem evaluate_immutable_atarget_tuple_case[local]:
  ^(List.nth (immutable_stmt_predicate_cases im_atarget,1))
Proof
  BETA_TAC >> rpt strip_tac >>
  Cases_on `v` >>
  gvs[Once evaluate_def, raise_def, accesses_atarget_def, int_calls_atarget_def] >>
  Cases_on `a` >>
  gvs[Once evaluate_def, raise_def] >>
  first_x_assum (qspecl_then [`A`,`R`] mp_tac) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem evaluate_immutable_atargets_nil_case[local]:
  ^(hd (immutable_stmt_predicate_cases im_atargets))
Proof
  BETA_TAC >> rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Theorem evaluate_immutable_atargets_cons_case[local]:
  ^(List.nth (immutable_stmt_predicate_cases im_atargets,1))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[accesses_atarget_def, int_calls_atarget_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `assign_tuple_target_list _ (_::_) (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  rpt (qpat_x_assum `!a b. assign_tuple_targets _ _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!A R st res st'. _` (qspecl_then [`A`,`R`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac) >>
  qpat_x_assum `!src fn ts mut nr args dflts ret body. _` kall_tac >>
  metis_tac[]
QED

Theorem evaluate_immutable_atargets_length_case[local]:
  ^(List.nth (immutable_stmt_predicate_cases im_atargets,2))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, raise_def]
QED

Theorem evaluate_immutable_atargets_length_other_case[local]:
  ^(List.nth (immutable_stmt_predicate_cases im_atargets,3))
Proof
  BETA_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, raise_def]
QED

Theorem immutable_defaults_scope_frame[local]:
  (!r t. f (st with scopes := scopes) = (r,t) ==>
    ^immutable_frame cx A (st with scopes := scopes) t) /\
  finally (ignore_bind (set_scopes scopes) f) (set_scopes prev) st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  simp[finally_def, set_scopes_def, ignore_bind_def, bind_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem immutable_try_function_frame[local]:
  (!r t. f st = (r,t) ==> ^immutable_frame cx A st t) /\
  try (ignore_bind f (return NoneV)) handle_function st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  Cases_on `f st` >> Cases_on `q` >>
  simp[try_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `y` >> gvs[handle_function_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem immutable_intcall_cleanup_frame[local]:
  ignore_bind (pop_function prev) (unlock_if_nr cx nr view) st = (res,st') ==>
  ^immutable_frame cx A st st'
Proof
  simp[pop_function_def, set_scopes_def, ignore_bind_def, bind_def,
       return_def, Excl "unlock_if_nr_def"] >>
  strip_tac >> drule unlock_if_nr_immutables >> simp[]
QED

val immutable_intcall_prefix = ``\cx src fn (es:expr list) ts mut nr args dflts ret body.
  ~MEM (src,fn) cx.stk /\ get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts``;

Theorem evaluate_immutable_intcall_case[local]:
  !cx src fn es ty drv.
  (!ts mut nr args dflts ret body.
    ^immutable_intcall_prefix cx src fn es ts mut nr args dflts ret body ==>
    ^im_exprs cx es) /\
  (!ts mut nr args dflts ret body s vs t.
    ^immutable_intcall_prefix cx src fn es ts mut nr args dflts ret body /\
    eval_exprs cx es s = (INL vs,t) ==>
    ^im_exprs (cx with stk updated_by CONS (src,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
  (!ts mut nr args dflts ret body s vs t sd prev dvs td env rtv sl x tl.
    ^immutable_intcall_prefix cx src fn es ts mut nr args dflts ret body /\
    eval_exprs cx es s = (INL vs,t) /\
    finally
      (ignore_bind (set_scopes [FEMPTY])
        (eval_exprs (cx with stk updated_by CONS (src,fn))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)))
      (set_scopes prev) sd = (INL dvs,td) /\
    bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    lock_if_nr cx nr (is_view_mut mut) sl = (INL x,tl) ==>
    ^im_stmts (cx with stk updated_by CONS (src,fn)) body) ==>
  ^im_expr cx (Call ty (IntCall (src,fn)) es drv)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "args_ih")
    (CONJUNCTS_THEN2 (mk_asm "defaults_ih") (mk_asm "body_ih"))) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM (src,fn) cx.stk`
  >- gvs[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
         bind_def, return_def, raise_def] >>
  Cases_on `get_module_code cx src`
  >- gvs[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
         ignore_bind_def, bind_def, return_def, raise_def] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `lookup_callable_function cx.in_deploy fn ts`
  >- gvs[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
         ignore_bind_def, bind_def, return_def, raise_def] >>
  rename1 `lookup_callable_function cx.in_deploy fn ts = SOME tup` >>
  PairCases_on `tup` >>
  rename1 `lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,bdy)` >>
  Cases_on `LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts`
  >- (asm_x "args_ih" mp_tac >> simp[] >>
      disch_then (mk_asm "args_frame") >>
      `^safe_accesses A R (accesses_exprs es) (int_calls_exprs es)` by
        gvs[accesses_expr_def, int_calls_expr_def] >>
      `^im_exprs cx es` by (asm "args_frame" mp_tac >> simp[]) >>
      rule_assum_tac BETA_RULE >>
      drule (BETA_RULE immutable_exprs_frame_rule) >>
      disch_then (qspecl_then [`R`,`A`] mp_tac) >> simp[] >>
      disch_then (mk_asm "args_run") >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (ar,sa)` >>
      Cases_on `ar`
      >- (rename1 `eval_exprs cx es st = (INL vs,sa)` >>
          qpat_x_assum `eval_expr cx _ st = _` mp_tac >>
          simp[Once evaluate_def, type_check_def, assert_def,
            lift_option_type_def, ignore_bind_def, bind_def, return_def,
            raise_def, get_scopes_def, Excl "lock_if_nr_def",
            Excl "unlock_if_nr_def", Excl "push_function_def",
            Excl "pop_function_def"] >>
          disch_then (mk_asm "run") >>
          `MEM (src,fn) R` by gvs[int_calls_expr_def] >>
          drule_all (BETA_RULE immutable_callable_safe) >> strip_tac >>
          `^safe_accesses A R
            (accesses_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts))
            (int_calls_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts))` by
            (BETA_TAC >> irule (BETA_RULE immutable_safe_accesses_drop) >> simp[]) >>
          `(cx with stk updated_by CONS (src,fn)) =
           (cx with stk := CONS (src,fn) cx.stk)` by
            simp[evaluation_context_component_equality] >>
          `^callable_closed (cx with stk updated_by CONS (src,fn)) A R` by
            (BETA_TAC >> asm_rewrite_tac[] >>
             rewrite_tac[BETA_RULE callable_closed_stk] >>
             qpat_x_assum `!src fn ts mut nr args dflts ret body. _` mp_tac >>
             simp[]) >>
          asm_x "defaults_ih" mp_tac >> simp[] >>
          disch_then drule >> simp[] >>
          disch_then (mk_asm "defaults_frame") >>
          `!s r t. eval_exprs (cx with stk := (src,fn)::cx.stk)
              (DROP (LENGTH dflts + LENGTH es - LENGTH args) dflts) s = (r,t) ==>
              ^immutable_frame cx A s t` by
            (BETA_TAC >> rpt gen_tac >> strip_tac >>
             asm "defaults_frame" (qspecl_then [`A`,`R`] mp_tac) >>
             `LENGTH dflts - (LENGTH args - LENGTH es) =
                LENGTH dflts + LENGTH es - LENGTH args` by decide_tac >>
             qpat_assum `cx with stk updated_by _ = _` (fn th => fs[th]) >>
             disch_then (qspecl_then [`s`,`r`,`t`] mp_tac) >> simp[] >>
             disch_tac >> rpt gen_tac >> strip_tac >>
             first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC) >>
          pop_assum (mk_asm "defaults_run") >>
          qmatch_asmsub_abbrev_tac `finally df dc sa` >>
          `!r t. finally df dc sa = (r,t) ==> ^immutable_frame cx A sa t` by
            (rpt strip_tac >>
             qpat_x_assum `finally df dc sa = _` mp_tac >>
             simp[Abbr `df`, Abbr `dc`, GSYM ignore_bind_def] >> strip_tac >>
             drule_at (Pat `finally _ _ _ = _`)
               (BETA_RULE immutable_defaults_scope_frame) >>
             disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
             disch_tac >> rpt gen_tac >> strip_tac >>
             first_x_assum irule >> simp[] >>
             asm "defaults_run" (mp_tac o BETA_RULE) >>
             disch_then (qspec_then `sa with scopes := [FEMPTY]` mp_tac) >>
             simp[]) >>
          pop_assum (mk_asm "scoped_run") >>
          Cases_on `finally df dc sa` >>
          rename1 `finally df dc sa = (dr,sd)` >>
          `^immutable_frame cx A sa sd` by
            (asm "scoped_run" (mp_tac o BETA_RULE) >> simp[]) >>
          `^immutable_frame cx A st sa` by
            (BETA_TAC >> rpt strip_tac >> asm "args_run" irule >> simp[] >> gvs[]) >>
          `^immutable_frame cx A st sd` by
            (irule immutable_frame_trans >> qexists_tac `sa` >> simp[]) >>
          pop_assum (mk_asm "prefix_frame") >>
          Cases_on `dr`
          >- (rename1 `finally df dc sa = (INL dvs,sd)` >>
              asm_x "run" mp_tac >> simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
              disch_then (mk_asm "run") >>
                  Cases_on `bind_arguments (get_tenv cx) args (vs ++ dvs)`
                  >- (asm_x "run" mp_tac >> simp[raise_def] >>
                      strip_tac >> qpat_x_assum `sd = st'` SUBST_ALL_TAC >>
                      asm "prefix_frame" (ACCEPT_TAC o BETA_RULE)) >>
                  rename1 `bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME argenv` >>
                  asm_x "run" mp_tac >> simp[return_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
                  disch_then (mk_asm "run") >>
                  Cases_on `evaluate_type (get_tenv cx) ret`
                  >- (asm_x "run" mp_tac >> simp[raise_def] >>
                      strip_tac >> qpat_x_assum `sd = st'` SUBST_ALL_TAC >>
                      asm "prefix_frame" (ACCEPT_TAC o BETA_RULE)) >>
                  rename1 `evaluate_type (get_tenv cx) ret = SOME rtv` >>
                  asm_x "run" mp_tac >> simp[return_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
                  disch_then (mk_asm "run") >>
                  Cases_on `lock_if_nr cx nr (mut = View \/ mut = Pure) sd` >>
                  rename1 `lock_if_nr cx nr (mut = View \/ mut = Pure) sd = (lr,sl)` >>
                  `sl.immutables = sd.immutables` by
                    (drule lock_if_nr_immutables >> simp[]) >>
                  `^immutable_frame cx A st sl` by
                    (asm "prefix_frame" mp_tac >> simp[]) >>
                  pop_assum (mk_asm "locked_frame") >>
                  Cases_on `lr`
                  >- (rename1 `lock_if_nr cx nr (mut = View \/ mut = Pure) sd = (INL lx,sl)` >>
                      asm_x "run" mp_tac >>
                      simp[push_function_def, return_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
                      disch_then (mk_asm "run") >>
                      unabbrev_all_tac >>
                      asm_x "body_ih" mp_tac >>
                      simp[GSYM ignore_bind_def, Excl "lock_if_nr_def"] >>
                      disch_then drule >> simp[Excl "lock_if_nr_def"] >>
                      disch_then (mk_asm "guarded_body") >>
                      qpat_assum `cx with stk updated_by _ = _`
                        (fn th =>
                          qpat_x_assum `finally _ _ sa = (INL dvs,sd)`
                            (assume_tac o SRULE [th, GSYM ignore_bind_def])) >>
                      asm_x "guarded_body" (drule_at (Pat `finally _ _ _ = _`)) >>
                      simp[Excl "lock_if_nr_def"] >>
                      Cases_on `lx` >>
                      disch_then (drule_at (Pat `lock_if_nr _ _ _ _ = _`)) >>
                      simp[Excl "lock_if_nr_def"] >>
                      disch_then (qspecl_then [`A`,`R`] mp_tac) >>
                      qpat_assum `cx with stk updated_by _ = _`
                        (fn th => rule_assum_tac (PURE_REWRITE_RULE [th] o BETA_RULE)) >>
                      simp[Excl "lock_if_nr_def"] >>
                      disch_then (mk_asm "body_run") >>
                      `!s r t. eval_stmts (cx with stk := (src,fn)::cx.stk) bdy s = (r,t) ==>
                         ^immutable_frame cx A s t` by
                        (BETA_TAC >> rpt strip_tac >>
                         asm "body_run" irule >> simp[MEM_APPEND] >>
                         first_assum (ACCEPT_TAC o SRULE [MEM_APPEND])) >>
                      pop_assum (mk_asm "body_exec") >>
                      asm_x "run" (mk_asm "run" o PURE_REWRITE_RULE [GSYM ignore_bind_def]) >>
                      qmatch_asmsub_abbrev_tac `finally_unless_halt bf bc (sl with scopes := [argenv])` >>
                      `!s r t. bc s = (r,t) ==> ^immutable_frame cx A s t` by
                        (qunabbrev_tac `bc` >> BETA_TAC >> rpt strip_tac >>
                         drule unlock_if_nr_immutables >> simp[]) >>
                      `!r t. bf (sl with scopes := [argenv]) = (r,t) ==>
                         ^immutable_frame cx A (sl with scopes := [argenv]) t` by
                        (qunabbrev_tac `bf` >> rpt gen_tac >> strip_tac >>
                         drule_at (Pat `finally _ _ _ = _`) immutable_frame_finally >>
                         disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
                         impl_tac >- (conj_tac
                           >- (rpt gen_tac >> strip_tac >>
                               drule_at (Pat `try _ _ _ = _`) immutable_try_function_frame >>
                               disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
                               impl_tac >- (rpt strip_tac >> asm "body_exec" drule >> simp[]) >>
                               simp[]) >>
                           simp[pop_function_def, set_scopes_def, return_def] >>
                           rpt strip_tac >> gvs[]) >>
                         simp[]) >>
                      `!r t. finally_unless_halt bf bc (sl with scopes := [argenv]) = (r,t) ==>
                         ^immutable_frame cx A (sl with scopes := [argenv]) t` by
                        (match_mp_tac immutable_frame_finally_unless_halt >>
                         conj_tac >> first_assum ACCEPT_TAC) >>
                      pop_assum (mk_asm "finished_body") >>
                      Cases_on `finally_unless_halt bf bc (sl with scopes := [argenv])` >>
                      rename1 `finally_unless_halt bf bc (sl with scopes := [argenv]) = (br,sb)` >>
                      asm_x "finished_body" (mp_tac o BETA_RULE) >> simp[NoAsms] >>
                      disch_then (mk_asm "body_frame") >>
                      asm_x "run" mp_tac >>
                      asm_x "body_frame" mp_tac >>
                      asm_x "locked_frame" mp_tac >>
                      POP_ASSUM_LIST (K ALL_TAC) >>
                      Cases_on `br`
                      >- (rename1 `INL rv` >> Cases_on `safe_cast rtv rv` >>
                          simp[return_def, raise_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
                      simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
                  asm_x "run" mp_tac >>
                  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
                  strip_tac >> qpat_x_assum `sl = st'` SUBST_ALL_TAC >>
                  asm "locked_frame" (ACCEPT_TAC o BETA_RULE)) >>
          asm_x "run" mp_tac >>
          simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
          strip_tac >> qpat_x_assum `sd = st'` SUBST_ALL_TAC >>
          asm "prefix_frame" (ACCEPT_TAC o BETA_RULE)) >>
      qpat_x_assum `eval_expr cx _ st = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def,
        lift_option_type_def, ignore_bind_def, bind_def, return_def, raise_def,
        Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
      strip_tac >> qpat_x_assum `sa = st'` SUBST_ALL_TAC >>
      rpt strip_tac >> asm "args_run" irule >> simp[] >> gvs[]) >>
  gvs[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
      ignore_bind_def, bind_def, return_def, raise_def]
QED

val intcall_ind_premise = let
  val (ps, core) = strip_forall (concl evaluate_ind)
  val cs = strip_conj (fst (dest_imp core))
  val c = List.find (fn t => can (find_term (fn u =>
    is_const u andalso fst (dest_const u) = "IntCall"))
    (snd (strip_imp (snd (strip_forall t))))) cs
in valOf c end;
val intcall_predicate_subst = map (fn (n,t) =>
  (valOf (List.find (fn v => fst (dest_var v) = n)
    (free_vars intcall_ind_premise))) |-> t)
  [("P1",im_stmts),("P4",im_expr),("P5",im_exprs)];
val intcall_normalization = INST intcall_predicate_subst
  (SIMP_CONV (srw_ss())
    [type_check_def, assert_def, lift_option_type_def, get_scopes_def,
     push_function_def, set_scopes_def, bind_def, ignore_bind_def,
     return_def, raise_def, vyperMiscTheory.option_CASE_rator,
     Excl "lock_if_nr_def", Excl "is_view_mut_def", AllCaseEqs()]
    intcall_ind_premise);

Theorem evaluate_immutable_intcall_ind_bridge[local]:
  ^(subst intcall_predicate_subst intcall_ind_premise)
Proof
  CONV_TAC (K intcall_normalization) >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "ind_body")
    (CONJUNCTS_THEN2 (mk_asm "ind_defaults") (mk_asm "ind_args"))) >>
  irule evaluate_immutable_intcall_case >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
      qpat_x_assum `~MEM _ _ /\ _` strip_assume_tac >>
      rename1 `lookup_callable_function cx.in_deploy fn ts =
        SOME (mut,nr,args,dflts,ret,bdy)` >>
      asm "ind_body" (drule_at (Pat `lookup_callable_function _ _ _ = _`)) >>
      simp[NoAsms, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      disch_then (mk_asm "body_run") >> rpt strip_tac >>
      asm "body_run" irule >>
      asm_x "ind_body" kall_tac >> asm_x "ind_defaults" kall_tac >>
      asm_x "ind_args" kall_tac >> asm_x "body_run" kall_tac >>
      `?s0:evaluation_state. s0.scopes = prev` by
        (qexists_tac `sd with scopes := prev` >> simp[]) >>
      Cases_on `x` >> fs[GSYM ignore_bind_def] >>
      simp[SF SFY_ss] >>
      (conj_tac >- (qexistsl_tac [`A`,`R`] >> gvs[] >> metis_tac[])) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
      qpat_x_assum `~MEM _ _ /\ _` strip_assume_tac >>
      asm "ind_defaults" (drule_at (Pat `lookup_callable_function _ _ _ = _`)) >>
      simp[NoAsms] >> disch_then (mk_asm "defaults_run") >> rpt strip_tac >>
      asm "defaults_run" irule >>
      asm_x "ind_body" kall_tac >> asm_x "ind_defaults" kall_tac >>
      asm_x "ind_args" kall_tac >> asm_x "defaults_run" kall_tac >>
      simp[SF SFY_ss] >>
      qexistsl_tac [`A`,`R`] >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  qpat_x_assum `~MEM _ _ /\ _` strip_assume_tac >>
  asm "ind_args" (drule_at (Pat `lookup_callable_function _ _ _ = _`)) >>
  simp[NoAsms] >> disch_then (mk_asm "args_run") >> rpt strip_tac >>
  asm "args_run" irule >>
  asm_x "ind_body" kall_tac >> asm_x "ind_defaults" kall_tac >>
  asm_x "ind_args" kall_tac >> asm_x "args_run" kall_tac >>
  simp[SF SFY_ss] >>
  qexistsl_tac [`A`,`R`] >> gvs[] >> metis_tac[]
QED

Theorem evaluate_immutable_frame_untyped[local]:
  (!cx s. ^im_stmt cx s) /\
  (!cx ss. ^im_stmts cx ss) /\
  (!cx it. ^im_iterator cx it) /\
  (!cx tyv nm body vs. ^im_for cx tyv nm body vs) /\
  (!cx e. ^im_expr cx e) /\
  (!cx es. ^im_exprs cx es) /\
  (!cx t. ^im_base cx t) /\
  (!cx t. ^im_target cx t) /\
  (!cx g v. ^im_atarget cx g v) /\
  (!cx gs vs. ^im_atargets cx gs vs) /\
  (!cx es. ^im_results cx es)
Proof
  BETA_TAC >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  BETA_TAC >> FIRST (map (ACCEPT_TAC o BETA_RULE) [
    evaluate_immutable_name_case, evaluate_immutable_global_case,
    evaluate_immutable_flag_case, evaluate_immutable_literal_case,
    evaluate_immutable_basename_case, evaluate_immutable_baseglobal_case,
    evaluate_immutable_attribute_case, evaluate_immutable_subscript_case,
    evaluate_immutable_baseattribute_case, evaluate_immutable_basesubscript_case,
    evaluate_immutable_target_case, evaluate_immutable_exprs_nil_case,
    evaluate_immutable_exprs_cons_case, evaluate_immutable_results_nil_case,
    evaluate_immutable_results_cons_case, evaluate_immutable_struct_case,
    evaluate_immutable_typebuiltin_case, evaluate_immutable_ifexp_case,
    evaluate_immutable_pop_case, evaluate_immutable_rawrevert_case,
    evaluate_immutable_rawlog_case, evaluate_immutable_selfdestruct_case,
    evaluate_immutable_builtin_case, evaluate_immutable_return_none_case,
    evaluate_immutable_return_some_case, evaluate_immutable_raise_bare_case,
    evaluate_immutable_raise_unreachable_case, evaluate_immutable_raise_reason_case,
    evaluate_immutable_pass_case, evaluate_immutable_break_case,
    evaluate_immutable_continue_case, evaluate_immutable_exprstmt_case,
    evaluate_immutable_log_case, evaluate_immutable_annassign_case,
    evaluate_immutable_array_iterator_case, evaluate_immutable_range_iterator_case,
    evaluate_immutable_append_case, evaluate_immutable_assign_base_case,
    evaluate_immutable_augassign_case, evaluate_immutable_stmts_nil_case,
    evaluate_immutable_stmts_cons_case, evaluate_immutable_assign_tuple_case,
    evaluate_immutable_if_case, evaluate_immutable_assert_bare_case,
    evaluate_immutable_assert_unreachable_case, evaluate_immutable_assert_reason_case,
    evaluate_immutable_raise_custom_case, evaluate_immutable_assert_custom_case,
    evaluate_immutable_for_nil_case, evaluate_immutable_for_stmt_case,
    evaluate_immutable_for_cons_case, evaluate_immutable_atarget_base_case,
    evaluate_immutable_atarget_tuple_case, evaluate_immutable_atargets_nil_case,
    evaluate_immutable_atargets_cons_case, evaluate_immutable_atargets_length_case,
    evaluate_immutable_atargets_length_other_case,
    evaluate_immutable_intcall_ind_bridge] @
    map (ACCEPT_TAC o BETA_RULE) (CONJUNCTS evaluate_immutable_risky_cases))
QED

Theorem eval_expr_unwritten_immutable:
  !cx e st res st' env mods src id.
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
    ~MEM RiskyAcc (expr_accesses mods e) /\
    ~MEM (WriteAcc (StateRef (src,id))) (expr_accesses mods e) ==>
    FLOOKUP (case ALOOKUP st'.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) id =
    FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) id
Proof
  rpt strip_tac >>
  drule_all callable_closed_initial >> strip_tac >>
  drule safe_accesses_expr_initial >> strip_tac >>
  qspecl_then [`cx`,`e`] (mp_tac o BETA_RULE)
    (cj 5 evaluate_immutable_frame_untyped) >>
  disch_then (qspecl_then [`expr_accesses mods e`,
    `reached_functions mods e`,`st`,`res`,`st'`] mp_tac) >>
  gvs[] >> disch_then drule >>
  disch_then (qspecl_then [`src`,`id`] mp_tac) >> simp[]
QED
