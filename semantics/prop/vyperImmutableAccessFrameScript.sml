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
    ^im_results cx es) /\
  (!ts mut nr args dflts ret body s results t.
    ^immutable_intcall_prefix cx src fn es ts mut nr args dflts ret body /\
    eval_expr_results cx es s = (INL results,t) ==>
    ^im_exprs (cx with stk updated_by CONS (src,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
  (!ts mut nr args dflts ret body s results t sd prev dvs td sr vs tr env rtv sl x tl.
    ^immutable_intcall_prefix cx src fn es ts mut nr args dflts ret body /\
    eval_expr_results cx es s = (INL results,t) /\
    finally
      (ignore_bind (set_scopes [FEMPTY])
        (eval_exprs (cx with stk updated_by CONS (src,fn))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)))
      (set_scopes prev) sd = (INL dvs,td) /\
    read_results cx results sr = (INL vs,tr) /\
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
      `^im_results cx es` by (asm "args_frame" mp_tac >> simp[]) >>
      rule_assum_tac BETA_RULE >>
      drule (BETA_RULE immutable_results_frame_rule) >>
      disch_then (qspecl_then [`R`,`A`] mp_tac) >> simp[] >>
      disch_then (mk_asm "args_run") >>
      Cases_on `eval_expr_results cx es st` >>
      rename1 `eval_expr_results cx es st = (ar,sa)` >>
      Cases_on `ar`
      >- (rename1 `eval_expr_results cx es st = (INL avs,sa)` >>
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
              Cases_on `read_results cx avs sd` >>
              rename1 `read_results cx avs sd = (rr,sr)` >>
              `sr = sd` by metis_tac[read_results_state] >>
              qpat_x_assum `sr = sd` SUBST_ALL_TAC >>
              Cases_on `rr`
              >- (rename1 `read_results cx avs sd = (INL vs,sd)` >>
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
                      disch_then (drule_at (Pat `read_results _ _ _ = _`)) >>
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
                      qmatch_asmsub_abbrev_tac `finally bf bc (sl with scopes := [argenv])` >>
                      `!r t. finally bf bc (sl with scopes := [argenv]) = (r,t) ==>
                         ^immutable_frame cx A (sl with scopes := [argenv]) t` by
                        (BETA_TAC >> rpt strip_tac >>
                         drule_at (Pat `finally _ _ _ = _`) (BETA_RULE immutable_frame_finally) >>
                         disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
                         disch_then irule >> reverse conj_tac
                         >- (rpt strip_tac >>
                             qunabbrev_tac `bf` >>
                             drule_at (Pat `try _ _ _ = _`) (BETA_RULE immutable_try_function_frame) >>
                             disch_then (qspecl_then [`cx`,`A`] mp_tac) >>
                             disch_then irule >>
                             asm "body_exec" (mp_tac o BETA_RULE) >> simp[])
                         >> rpt strip_tac >>
                         qunabbrev_tac `bc` >>
                         metis_tac[BETA_RULE immutable_intcall_cleanup_frame]) >>
                      pop_assum (mk_asm "finished_body") >>
                      Cases_on `finally bf bc (sl with scopes := [argenv])` >>
                      rename1 `finally bf bc (sl with scopes := [argenv]) = (br,sb)` >>
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
          asm_x "run" mp_tac >>
          simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
          strip_tac >> qpat_x_assum `sd = st'` SUBST_ALL_TAC >>
          asm "prefix_frame" (ACCEPT_TAC o BETA_RULE)) >>
      qpat_x_assum `eval_expr cx _ st = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def,
        lift_option_type_def, ignore_bind_def, bind_def, return_def, raise_def,
        Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
      strip_tac >> qpat_x_assum `sa = st'` SUBST_ALL_TAC >>
      BETA_TAC >> rpt strip_tac >> asm "args_run" irule >> simp[] >> gvs[]) >>
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
  [("P1",im_stmts),("P4",im_expr),("P5",im_exprs),("P10",im_results)];
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
