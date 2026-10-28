(* Structural arena lifetime: every evaluator preserves existing token indices.
   Contents need not be readable or well typed. AbiEncode releases only captures
   allocated inside its own mark, including on exceptional exits. *)
Theory vyperEvalAbiMemory
Ancestors
  list rich_list pair option arithmetic vyperMisc vyperState vyperAbiOperand vyperAbiFrame
  vyperInterpreter vyperStorageBackend vyperStatePreservation vyperLookup
  vyperCallOutcome vyperCallOutcomeFrame vyperCreate vyperAbiStateTyping
  vyperAbiMemoryProps
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = hide "body";

Definition arenas_grow_def:
  arenas_grow st rt <=>
    LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
    LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
End

Theorem arenas_grow_trans:
  arenas_grow st mid /\ arenas_grow mid rt ==> arenas_grow st rt
Proof
  simp[arenas_grow_def] >> metis_tac[LESS_EQ_TRANS]
QED

Definition arena_extends_def:
  arena_extends f <=> !st. arenas_grow st (SND (f st))
End

Theorem arena_extends_result:
  arena_extends f <=> !st res rt. f st = (res,rt) ==>
    (LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
     LENGTH st.abi_immutables <= LENGTH rt.abi_immutables)
Proof
  simp[arena_extends_def, GSYM arenas_grow_def] >>
  eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `st` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`st`,`FST (f st)`,`SND (f st)`] mp_tac) >> simp[]
QED

Theorem arena_extends_bind:
  arena_extends f /\
  (!s v t. f s = (INL v,t) ==> arena_extends (g v)) ==>
  arena_extends (bind f g)
Proof
  simp[arena_extends_def, bind_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  `arenas_grow st r` by
    (qpat_x_assum `!st. arenas_grow st (SND (f st))`
      (qspec_then `st` mp_tac) >> simp[]) >>
  TRY (qpat_x_assum `!s v t. _` (qspecl_then [`st`,`x`,`r`] mp_tac) >>
    simp[] >> disch_then (qspec_then `r` mp_tac) >>
    strip_tac >> drule_all arenas_grow_trans >> simp[])
QED

Theorem arena_extends_finally:
  arena_extends f /\ arena_extends g ==> arena_extends (finally f g)
Proof
  simp[arena_extends_def, finally_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `g r` >> Cases_on `q'` >> gvs[] >>
  qpat_x_assum `!st. arenas_grow st (SND (f st))` (qspec_then `st` mp_tac) >>
  qpat_x_assum `!st. arenas_grow st (SND (g st))` (qspec_then `r` mp_tac) >>
  Cases_on `q` >> simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  metis_tac[arenas_grow_trans]
QED

Theorem arena_extends_try:
  arena_extends f /\ (!e. arena_extends (h e)) ==> arena_extends (try f h)
Proof
  simp[arena_extends_def, try_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `!st. arenas_grow st (SND (f st))`
    (qspec_then `st` mp_tac) >>
  TRY (qpat_x_assum `!e st. _` (qspecl_then [`y`,`r`] mp_tac)) >>
  simp[] >> metis_tac[arenas_grow_trans]
QED

Theorem arena_extends_pure[local]:
  (!st res rt. f st = (res,rt) ==> rt = st) ==> arena_extends f
Proof
  simp[arena_extends_result] >> metis_tac[LESS_EQ_REFL]
QED

Theorem arena_extends_reads:
  arena_extends (get_Value tv) /\ arena_extends (materialise cx tv) /\
  arena_extends get_accounts /\ arena_extends get_transient_storage /\
  arena_extends (lookup_global cx src id) /\
  arena_extends (lookup_flag_mem cx nsid mid) /\
  arena_extends (read_storage_slot cx tr slot ty) /\
  arena_extends (get_storage_backend cx tr) /\
  arena_extends (check_array_bounds cx tv v) /\
  arena_extends (toplevel_array_length cx tv) /\
  arena_extends (lift_option_type x msg) /\ arena_extends (lift_option y msg) /\
  arena_extends (lift_sum z) /\ arena_extends (lift_sum_runtime zr) /\
  arena_extends (assign_result ty ao v subs) /\
  arena_extends (resolve_array_element cx tr slot ty subs) /\
  arena_extends (read_abi_operand cx arg) /\
  arena_extends (check_abi_projection cx arg ty sub)
Proof
  rpt conj_tac >> irule arena_extends_pure >> rpt strip_tac >>
  FIRST [drule_all get_Value_state, drule_all materialise_state,
    drule_all get_accounts_state, drule_all get_transient_storage_state,
    drule_all lookup_global_state, drule_all lookup_flag_mem_state,
    drule_all read_storage_slot_state, drule_all get_storage_backend_state,
    drule_all check_array_bounds_state, drule_all toplevel_array_length_state,
    drule_all lift_option_type_state, drule_all lift_option_state,
    drule_all lift_sum_state, drule_all lift_sum_runtime_state,
    drule_all assign_result_state, drule_all resolve_array_element_state,
    drule_all read_abi_operand_state, drule_all check_abi_projection_state] >> simp[]
QED

Theorem arena_extends_primitives:
  arena_extends (return x) /\ arena_extends (raise e) /\
  arena_extends (λs. return (g s) s) /\
  arena_extends (check b msg) /\ arena_extends (type_check b msg) /\
  arena_extends get_scopes /\ arena_extends (set_scopes scs) /\
  arena_extends push_scope /\ arena_extends pop_scope /\
  arena_extends (push_scope_with_var nm ty v) /\
  arena_extends (new_variable id ty v) /\
  arena_extends (update_accounts fa) /\ arena_extends (update_transient ft) /\
  arena_extends (append_logs ls) /\ arena_extends (push_log lg) /\
  arena_extends get_pending_deletions /\
  arena_extends (update_pending_deletions fp) /\
  arena_extends (get_immutables cx src) /\
  arena_extends (set_immutable cx src nm ty v) /\
  arena_extends (write_storage_slot cx tr slot ty v) /\
  arena_extends (set_global cx src nm v) /\
  arena_extends (transfer_value sender target amount) /\
  arena_extends (acquire_nonreentrant_lock target lock view) /\
  arena_extends (release_nonreentrant_lock target lock) /\
  arena_extends (push_function fn sc cx) /\ arena_extends (pop_function scs) /\
  arena_extends mark_abi_memory /\ arena_extends mark_abi_captures
Proof
  simp[arena_extends_def, arenas_grow_def, check_def, type_check_def, assert_def,
    get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, new_variable_def, update_accounts_def,
    update_transient_def, append_logs_def, push_log_def,
    get_pending_deletions_def, update_pending_deletions_def,
    get_immutables_def, get_address_immutables_def,
    set_immutable_def, set_address_immutables_def,
    get_storage_backend_def, set_storage_backend_def, write_storage_slot_def,
    set_global_def, transfer_value_def, get_accounts_def,
    acquire_nonreentrant_lock_def, release_nonreentrant_lock_def,
    get_transient_storage_def, push_function_def, pop_function_def,
    mark_abi_memory_def, mark_abi_captures_def,
    bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >> asm_simp_tac (srw_ss()) [] >>
    gvs[set_scopes_def, update_accounts_def, update_transient_def,
        set_address_immutables_def, get_storage_backend_def,
        set_storage_backend_def, write_storage_slot_def,
        lift_option_type_def, lift_option_def, lift_sum_def,
        get_accounts_def, get_transient_storage_def, check_def,
        type_check_def, assert_def,
        bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[get_storage_backend_eq, set_storage_backend_eq,
      option_CASE_rator, prod_CASE_rator, COND_RATOR,
      return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.PURE_CASE_TAC >> asm_simp_tac (srw_ss()) [] >>
    gvs[get_storage_backend_eq, set_storage_backend_eq, set_storage_def,
        return_def, raise_def, AllCaseEqs()]) >>
  qmatch_goalsub_abbrev_tac `set_storage _ _ backend _` >>
  Cases_on `backend` >> simp[set_storage_def]
QED

Theorem arena_extends_capture_write:
  arena_extends (capture_abi_memory cx id ty v) /\
  arena_extends (write_abi_memory cx id ty v subs ao) /\
  arena_extends (capture_abi_immutable cx src id ty v) /\
  arena_extends (write_abi_immutables cx src id ty v subs ao)
Proof
  simp[arena_extends_result] >> rpt strip_tac >>
  imp_res_tac capture_abi_memory_length >>
  imp_res_tac capture_abi_memory_typing_frame >>
  imp_res_tac write_abi_memory_length >>
  imp_res_tac write_abi_memory_immutables >>
  imp_res_tac capture_abi_immutable_length >>
  imp_res_tac capture_abi_immutable_frame >>
  imp_res_tac write_abi_immutables_length >>
  imp_res_tac write_abi_immutables_frame >> simp[]
QED

Theorem arena_extends_handlers:
  arena_extends (handle_loop_exception e) /\ arena_extends (handle_function e)
Proof
  Cases_on `e` >> simp[handle_loop_exception_def, handle_function_def,
    arena_extends_def, arenas_grow_def, return_def, raise_def]
QED

Theorem arena_extends_outcomes:
  arena_extends (take_call_outcome target data amount) /\
  arena_extends (adopt_call_outcome rq co)
Proof
  simp[arena_extends_result] >> rpt strip_tac >>
  TRY (drule take_call_outcome_frame >>
    simp[evaluation_state_component_equality] >> NO_TAC) >>
  gvs[adopt_call_outcome_equation, return_def, AllCaseEqs()]
QED

(* Net-guided monadic composition, splitting only the exposed case. *)
fun arena_net facts binds =
  List.foldl (fn (th,n) => Net.insert (concl th, MATCH_ACCEPT_TAC th) n)
    (List.foldl (fn (th,n) => Net.insert
      (snd (dest_imp (concl th)), MATCH_MP_TAC th >> conj_tac) n)
      Net.empty (map SPEC_ALL binds)) (map SPEC_ALL facts);

val arena_head_conv =
  let
    val rules = List.concat (map (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
      (LET_THM :: COND_CLAUSES ::
       List.mapPartial (total TypeBasePure.case_def_of) (TypeBase.elts ())));
    val net = List.foldl (fn (th,n) => Net.insert
      (lhs (concl th), REWR_CONV th) n) Net.empty rules;
    fun root tm = FIRST_CONV (Net.match tm net) tm;
    fun head tm = (BETA_CONV ORELSEC root ORELSEC
      REWR_CONV UNCURRY ORELSEC RATOR_CONV head) tm;
  in head end;

fun ARENA_CASE_TAC (g as (old,_)) =
  (BasicProvers.PURE_TOP_CASE_TAC >>
   (fn (asl,w) => simp_tac bool_ss (map ASSUME
     (List.filter (fn a => not (is_forall a) andalso
       not (List.exists (aconv a) old)) asl)) (asl,w))) g;

val arena_base_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [arena_extends_reads, arena_extends_primitives, arena_extends_capture_write,
   arena_extends_handlers, arena_extends_outcomes]);

fun arena_step facts =
  let val net = arena_net facts
    [arena_extends_bind, arena_extends_finally, arena_extends_try]
  in FIRST [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
    first_assum MATCH_ACCEPT_TAC,
    (fn g as (_,w) => FIRST (Net.match w net) g),
    CONV_TAC (RAND_CONV (CHANGED_CONV arena_head_conv)),
    CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
    CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
    strip_tac, conj_tac, ARENA_CASE_TAC] end;

val ARENA_PRIMITIVE_TAC = rpt (arena_step arena_base_facts);

Theorem arena_extends_abi:
  arena_extends (unwrap_abi_operand cx arg) /\
  arena_extends (stage_abi_operands cx args) /\
  arena_extends (lookup_abi_local cx id) /\
  arena_extends (lookup_abi_global cx src id) /\
  arena_extends (project_abi_operand cx arg sub) /\
  arena_extends (subscript_abi_operand cx ty arg index) /\
  arena_extends (attribute_abi_operand cx arg id) /\
  arena_extends (project_abi_path cx arg subs) /\
  arena_extends (abi_target_operand cx loc subs) /\
  arena_extends (abi_pop_pointer cx arg)
Proof
  `!cx arg. arena_extends (unwrap_abi_operand cx arg)` by
    (rpt gen_tac >> Cases_on `arg` >> simp_tac bool_ss [unwrap_abi_operand_def] >> ARENA_PRIMITIVE_TAC) >>
  `!args cx. arena_extends (stage_abi_operands cx args)` by
    (Induct >> gen_tac >> simp_tac bool_ss [stage_abi_operands_def] >> ARENA_PRIMITIVE_TAC) >>
  `!cx id. arena_extends (lookup_abi_local cx id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_local_def] >> ARENA_PRIMITIVE_TAC) >>
  `!cx src id. arena_extends (lookup_abi_immutable cx src id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_immutable_def] >> ARENA_PRIMITIVE_TAC) >>
  `!cx src id. arena_extends (lookup_abi_global cx src id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_global_def] >> ARENA_PRIMITIVE_TAC) >>
  `!cx arg sub. arena_extends (project_abi_operand cx arg sub)` by
    (rpt gen_tac >> simp_tac bool_ss [oneline project_abi_operand_def] >> ARENA_PRIMITIVE_TAC) >>
  `!cx ty arg index. arena_extends (subscript_abi_operand cx ty arg index)` by
    (rpt gen_tac >> Cases_on `arg` >> simp_tac bool_ss [subscript_abi_operand_def] >>
     ARENA_PRIMITIVE_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `!cx arg id. arena_extends (attribute_abi_operand cx arg id)` by
    (rpt gen_tac >> Cases_on `arg` >> simp_tac bool_ss [attribute_abi_operand_def] >>
     ARENA_PRIMITIVE_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `!subs cx arg. arena_extends (project_abi_path cx arg subs)` by
    (Induct >> rpt gen_tac >> simp_tac bool_ss [project_abi_path_def] >>
     ARENA_PRIMITIVE_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `!cx loc subs. arena_extends (abi_target_operand cx loc subs)` by
    (rpt gen_tac >> Cases_on `loc` >> Cases_on `subs` >>
     simp_tac bool_ss [abi_target_operand_def] >>
     ARENA_PRIMITIVE_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `!cx arg. arena_extends (abi_pop_pointer cx arg)` by
    (rpt gen_tac >> simp_tac bool_ss [abi_pop_pointer_def] >>
     ARENA_PRIMITIVE_TAC >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem arena_extends_assignment:
  (!cx tgt ao. arena_extends (assign_target cx tgt ao)) /\
  (!cx tgts vs. arena_extends (assign_targets cx tgts vs))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >>
  simp_tac bool_ss [Once assign_target_def, FORALL_PROD, LET_THM] >> rpt strip_tac >>
  ARENA_PRIMITIVE_TAC
QED

Theorem arena_extends_calls:
  arena_extends (eval_raw_call cx flags target data amount) /\
  arena_extends (eval_send cx has_gas vs) /\
  arena_extends (eval_ext_call cx static skip sig opts vs) /\
  arena_extends (eval_create cx kind salt rof tys vs blueprint_size) /\
  arena_extends (check_create_blueprint salt vs)
Proof
  rpt conj_tac >>
  TRY (PairCases_on `sig`) >> TRY (Cases_on `vs` >> TRY (Cases_on `t`)) >>
  simp_tac bool_ss [eval_raw_call_def, eval_send_def, eval_ext_call_def,
    eval_create_def, create_soft_failure_def, LET_THM] >>
  ARENA_PRIMITIVE_TAC >>
  simp[arena_extends_def, arenas_grow_def, check_create_blueprint_state]
QED

(* Release is not monotone in isolation. Its mark is the incoming arena length. *)
Theorem arena_extends_scoped:
  arena_extends f ==>
  arena_extends (do mark <- mark_abi_captures; finally f (release_abi_captures mark) od)
Proof
  simp[arena_extends_def, arenas_grow_def, mark_abi_captures_def, bind_def,
       return_def, finally_def, release_abi_captures_def] >> strip_tac >> gen_tac >>
  Cases_on `f st` >> Cases_on `q` >>
  simp[ignore_bind_def, bind_def, release_abi_captures_def, return_def, raise_def, LENGTH_TAKE] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

val arena_facts = arena_base_facts @ List.concat (map (CONJUNCTS o SPEC_ALL)
  [arena_extends_abi, arena_extends_assignment, arena_extends_calls]);
val ARENA_TAC = rpt (arena_step arena_facts);

fun arena_finish (g as (asl,w)) =
  let
    fun key tm = dest_thy_const (fst (strip_comb (rand tm))) |> #Name;
    val atomic = List.concat (map (CONJUNCTS o ASSUME)
      (List.filter (not o is_forall) asl));
    val base = SIMP_RULE (bool_ss ++ numSimps.ARITH_ss)
      [ignore_bind_def, oneTheory.one, FST, SND];
    val atomic = map base atomic;
    val branch = List.filter (fn th => is_eq (concl th) andalso
      not (pairSyntax.is_pair (rhs (concl th)))) atomic;
    val norm = SIMP_RULE (bool_ss ++ numSimps.ARITH_ss)
      (ignore_bind_def :: oneTheory.one :: FST :: SND :: branch);
    val facts = map norm atomic @ atomic;
    val candidates = rev (List.filter (fn tm => is_forall tm andalso
      total (key o snd o strip_imp o snd o strip_forall) tm = total key w) asl);
    fun guard_conv tm =
      if is_forall tm then BINDER_CONV guard_conv tm
      else LAND_CONV (SIMP_CONV (bool_ss ++ numSimps.ARITH_ss)
        [ignore_bind_def, oneTheory.one, FST, SND]) tm;
    fun discharge th =
      if is_imp (snd (strip_forall (concl th))) then
        discharge (tryfind (MATCH_MP (CONV_RULE guard_conv th)) (TRUTH :: facts))
      else base th;
    fun finish tm = MATCH_ACCEPT_TAC
      (discharge (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (norm (ASSUME tm))));
  in FIRST (map (fn tm => fn g => finish tm g) candidates) g end;

val ARENA_FINISH_TAC = simp_tac bool_ss [FST, SND] >> arena_finish;

fun ARENA_SUSPEND pattern tag (g as (_,w)) =
  if can (match_term pattern) w then suspend tag g else NO_TAC g;

Theorem eval_arena_extends_mutual:
  (!cx s. arena_extends (eval_stmt cx s)) /\
  (!cx ss. arena_extends (eval_stmts cx ss)) /\
  (!cx it. arena_extends (eval_iterator cx it)) /\
  (!cx tgt. arena_extends (eval_target cx tgt)) /\
  (!cx tgts. arena_extends (eval_targets cx tgts)) /\
  (!cx bt. arena_extends (eval_base_target cx bt)) /\
  (!cx ty id body vs. arena_extends (eval_for cx ty id body vs)) /\
  (!cx e. arena_extends (eval_expr cx e)) /\
  (!cx es. arena_extends (eval_exprs cx es)) /\
  (!cx e. arena_extends (eval_abi_expr cx e)) /\
  (!cx es. arena_extends (eval_abi_exprs cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >> TRY strip_tac >>
  TRY (ARENA_SUSPEND ``arena_extends (eval_expr cx (TypeBuiltin ty tb typ es))`` "TypeBuiltin") >>
  TRY (ARENA_SUSPEND ``arena_extends (eval_expr cx (Call ty (IntCall nsid) es v0))`` "IntCall") >>
  TRY (ARENA_SUSPEND ``arena_extends (eval_expr cx (Call ty (CreateTarget kind has_salt rof) es v0))`` "CreateTarget") >>
  simp[Once evaluate_def] >> ARENA_TAC >> ARENA_FINISH_TAC
QED

Resume eval_arena_extends_mutual[TypeBuiltin]:
  Cases_on `tb` >> gvs[] >> simp[Once evaluate_def] >>
  (* Match the whole marked region before decomposing its finally. *)
  rpt (FIRST [MATCH_MP_TAC arena_extends_scoped, arena_step arena_facts]) >>
  gvs[oneTheory.one] >> first_x_assum drule >>
  simp[mark_abi_captures_def, return_def]
QED

Resume eval_arena_extends_mutual[IntCall]:
  simp[Once evaluate_def] >> ARENA_TAC >> ARENA_FINISH_TAC
QED

Resume eval_arena_extends_mutual[CreateTarget]:
  Cases_on `kind` >> Cases_on `has_salt` >> gvs[] >>
  simp[Once evaluate_def] >> ARENA_TAC >> ARENA_FINISH_TAC
QED

Finalise eval_arena_extends_mutual

Theorem evaluate_abi_memory_length:
  (!cx s st res rt. eval_stmt cx s st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx ss st res rt. eval_stmts cx ss st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx it st res rt. eval_iterator cx it st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx tgt st res rt. eval_target cx tgt st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx tgts st res rt. eval_targets cx tgts st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx bt st res rt. eval_base_target cx bt st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx ty id body vs st res rt. eval_for cx ty id body vs st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx e st res rt. eval_expr cx e st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx es st res rt. eval_exprs cx es st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx e st res rt. eval_abi_expr cx e st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory) /\
  (!cx es st res rt. eval_abi_exprs cx es st = (res,rt) ==> LENGTH st.abi_memory <= LENGTH rt.abi_memory)
Proof
  metis_tac[eval_arena_extends_mutual, arena_extends_result]
QED

val eval_expr_abi_memory_length = save_thm("eval_expr_abi_memory_length",
  List.nth (CONJUNCTS evaluate_abi_memory_length, 7));
val eval_exprs_abi_memory_length = save_thm("eval_exprs_abi_memory_length",
  List.nth (CONJUNCTS evaluate_abi_memory_length, 8));
val eval_abi_expr_abi_memory_length = save_thm("eval_abi_expr_abi_memory_length",
  List.nth (CONJUNCTS evaluate_abi_memory_length, 9));
val eval_abi_exprs_abi_memory_length = save_thm("eval_abi_exprs_abi_memory_length",
  List.nth (CONJUNCTS evaluate_abi_memory_length, 10));

Theorem assign_target_abi_immutables_length:
  assign_target cx tgt ao st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
Proof
  metis_tac[cj 1 arena_extends_assignment, arena_extends_result]
QED

Theorem eval_expr_abi_immutables_length:
  eval_expr cx e st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
Proof
  metis_tac[cj 8 eval_arena_extends_mutual, arena_extends_result]
QED

Theorem eval_exprs_abi_immutables_length:
  eval_exprs cx es st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
Proof
  metis_tac[cj 9 eval_arena_extends_mutual, arena_extends_result]
QED

Theorem eval_abi_expr_abi_immutables_length:
  eval_abi_expr cx e st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
Proof
  metis_tac[cj 10 eval_arena_extends_mutual, arena_extends_result]
QED

Theorem eval_abi_exprs_abi_immutables_length:
  eval_abi_exprs cx es st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables
Proof
  metis_tac[cj 11 eval_arena_extends_mutual, arena_extends_result]
QED
