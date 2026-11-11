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
  simp[write_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
       AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  drule set_immutable_key_frame >> simp[]
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
  cheat
QED
