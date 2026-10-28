(*
 * Frame and outcome properties of the contract-creation builtins.
 *
 * TOP-LEVEL:
 *   eval_create_logs_extend                  — creation extends the log
 *   eval_create_preserves_scopes_immutables  — scopes/immutables framed
 *   eval_create_exception_is_error           — only Error exceptions
 *   eval_create_no_type_error                — no TypeError past decoding
 *)

Theory vyperCreateFrame
Ancestors
  arithmetic byte combin integer list option pair rich_list words
  contractABI sptree vfmTypes vfmConstants vfmState vfmContext
  vfmExecution[ignore_grammar] vyperAST vyperABI vyperMisc vyperValue
  vyperContext vyperState vyperEvmBoundary vyperCreate
Libs
  wordsLib monadsyntax

Theorem check_create_blueprint_result_state:
  check_create_blueprint has_salt vs st = (res, st') ==> st' = st
Proof
  metis_tac[check_create_blueprint_state, pairTheory.SND]
QED

Theorem check_create_blueprint_exception_is_error:
  check_create_blueprint has_salt vs st = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  simp[check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def]
QED

Theorem check_create_blueprint_no_type_error:
  check_create_blueprint has_salt vs st = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  simp[check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> rw[return_def, raise_def]
QED

(* The adapter-result chain leaves a combined record update, which the
   per-field accfupds theorems do not directly simplify. *)
Theorem evaluation_state_accounts_tStorage_acc:
  (s with <| accounts := a; tStorage := t |>).scopes = s.scopes /\
  (s with <| accounts := a; tStorage := t |>).immutables = s.immutables /\
  (s with <| accounts := a; tStorage := t |>).logs = s.logs /\
  (s with <| accounts := a; tStorage := t |>).accounts = a /\
  (s with <| accounts := a; tStorage := t |>).tStorage = t
Proof
  Cases_on `s` >> simp[evaluation_state_accfupds]
QED

(* KEY LEMMA: the EVM-backed tail of eval_create only updates accounts,
   transient storage, pending deletions, and logs — never scopes or immutables.
   Stated with the accessor monads already unfolded, so it matches eval_create's body
   directly. *)
Theorem create_tail_preserves_scopes:
  (case run_create_evm a b c d e f h g of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  st'.scopes = s.scopes /\ st'.immutables = s.immutables
Proof
  Cases_on `run_create_evm a b c d e f h g`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[evaluation_state_accfupds]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_accfupds] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[evaluation_state_accounts_tStorage_acc,
                       evaluation_state_accfupds]
QED

(* Every creation path leaves the old log sequence as a prefix. *)
Theorem create_tail_log_extends:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  isPREFIX s.logs st'.logs
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >>
      gvs[evaluation_state_accfupds, rich_listTheory.IS_PREFIX_REFL]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_accfupds,
      rich_listTheory.IS_PREFIX_REFL, rich_listTheory.IS_PREFIX_APPEND] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[evaluation_state_accounts_tStorage_acc, evaluation_state_accfupds,
      rich_listTheory.IS_PREFIX_REFL, rich_listTheory.IS_PREFIX_APPEND]
QED

(* Every raise on the EVM-backed tail raises an Error; the remaining outcomes
   all come from return. *)
Theorem create_tail_exception_is_error:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Reduce only the executed monadic head. In particular, never simplify a
   continuation or the context containing the guarded operand equations. *)
local
  val head_rules = map (REWR_CONV o CONV_RULE (DEPTH_CONV ETA_CONV))
    (List.concat (map (CONJUNCTS o SPEC_ALL)
    [eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
     get_accounts_def, check_def, assert_def, return_def, raise_def,
     update_accounts_def, get_transient_storage_def,
     get_pending_deletions_def, create_soft_failure_def,
     pairTheory.pair_case_thm, sumTheory.sum_case_def,
     optionTheory.option_case_def, LET_THM, COND_RATOR, COND_CLAUSES]));
  val guard_ss = bool_ss;
  val frame_ss = bool_ss ++ rewrites [evaluation_state_accfupds];
  val log_ss = frame_ss ++ rewrites [rich_listTheory.IS_PREFIX_REFL];
  val error_ss = bool_ss ++ rewrites
    [sumTheory.INR_11, sumTheory.sum_distinct, exception_11,
     vyperValueOperationTheory.error_distinct];

  fun create_head_conv facts tm =
    let
      fun equation th =
        if is_eq (concl th) then th
        else if is_neg (concl th) then EQF_INTRO th else EQT_INTRO th;
      val root = FIRST_CONV
        (BETA_CONV :: map (REWR_CONV o equation) facts @ head_rules);
      fun step tm =
        (CHANGED_CONV root ORELSEC
         (fn tm =>
           let val (h,args) = strip_comb tm in
             if is_const h andalso
                ((fst (dest_const h) = "pair_CASE" andalso length args = 2) orelse
                 (mem (fst (dest_const h)) ["sum_CASE", "option_CASE"] andalso
                  length args = 3))
             then funpow (length args - 1) RATOR_CONV
                    (RAND_CONV (CHANGED_CONV (create_head_conv facts))) tm
             else if is_cond tm then
               RATOR_CONV (RATOR_CONV
                 (RAND_CONV (CHANGED_CONV (SIMP_CONV guard_ss facts)))) tm
             else RATOR_CONV (CHANGED_CONV (create_head_conv facts)) tm
           end)) tm;
    in REPEATC step tm end;

  fun create_guard tm =
    if is_cond tm then #1 (dest_cond tm)
    else
      let val (h,args) = strip_comb tm in
        if is_const h andalso
           ((fst (dest_const h) = "pair_CASE" andalso length args = 2) orelse
            (mem (fst (dest_const h)) ["sum_CASE", "option_CASE"] andalso
             length args = 3))
        then create_guard (hd args)
        else create_guard (rator tm)
      end;

  fun create_paths tail finish (asl,w) =
    let
      val cv = create_head_conv (map ASSUME asl);
      val tm = lhs (fst (dest_imp w));
      val th = cv tm;
      val next = rhs (concl th);
      val reduce = CONV_TAC (LAND_CONV (LAND_CONV (K th)));
    in
      (reduce >>
       (case total create_guard next of
          SOME guard => ASM_CASES_TAC guard >> create_paths tail finish
        | NONE =>
            DISCH_THEN (fn result =>
              if pairSyntax.is_pair next then finish (SOME result)
              else mp_tac (MATCH_MP tail result) >> finish NONE))) (asl,w)
    end;

  (* Only substitute the final-state equation in the goal; leave the
     guarded decode and check facts untouched. A tail lemma already supplies
     the conclusion, so only its accessor updates need simplifying. *)
  fun create_state_finish ss result =
    (case result of
       NONE => ALL_TAC
     | SOME result =>
         let
           val snd = rator (pairSyntax.mk_snd (lhs (concl result)));
           val state = REWRITE_RULE [pairTheory.SND] (AP_TERM snd result);
         in SUBST1_TAC (SYM state) end) >> simp_tac ss [];

  (* Outcome properties need only the result projection, not the state or
     any decode/check assumptions. *)
  fun create_error_finish result =
    (case result of
       NONE => ALL_TAC
     | SOME result =>
         let
           val fst = rator (pairSyntax.mk_fst (lhs (concl result)));
           val outcome = SIMP_RULE error_ss []
             (REWRITE_RULE [pairTheory.FST] (AP_TERM fst result));
         in
           if aconv (concl outcome) F then CONTR_TAC outcome
           else SUBST1_TAC (SYM outcome)
         end) >> simp_tac error_ss [];

in
  fun create_result_tac tail finish =
    qpat_x_assum `eval_create _ _ _ _ _ _ _ _ = _` mp_tac >>
    create_paths (REWRITE_RULE [GSYM ignore_bind_def] tail) finish;
  val create_frame_tac =
    create_result_tac create_tail_preserves_scopes (create_state_finish frame_ss);
  val create_logs_tac =
    create_result_tac create_tail_log_extends (create_state_finish log_ss);
  fun create_outcome_tac tail = create_result_tac tail create_error_finish;
  val create_exception_tac = create_outcome_tac create_tail_exception_is_error;
end;

(* Constructor events extend, rather than preserve, the log sequence. *)
Theorem eval_create_logs_extend:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  isPREFIX st.logs st'.logs
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_logs_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_logs_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_logs_tac
QED

Theorem eval_create_preserves_scopes_immutables:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_frame_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_frame_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_frame_tac
QED

(* Storage is NOT preserved across creation in general: the constructor runs
   arbitrary EVM code that may write any account's storage, including the
   created account's own.  There is therefore no frame rule to prove here,
   and the old eval_create_preserves_storage theorem has been removed as
   false.

   Downstream storage preservation must handle creation the same way it
   handles external calls: by postulating the analogous property at the EVM
   boundary.  Cf. protected_storage_calls_preserve_def in
   vyperTypeStoragePreservationScript.sml, which is postulated for
   run_ext_call.  The matching postulate for run_create_evm belongs beside
   it; create_tail_preserves_scopes above is the shape lemma that hook
   consumes. *)

(* KEY LEMMA for the type-soundness consumer.

   Once the three operand-shape decodes and the initcode construction have
   succeeded, every remaining failure in eval_create is an Error raised
   by check/assert or the EVM-backed tail, which performs no typing checks.

   The shape hypotheses are essential: lift_option_type raises
   Error (TypeError _), so without them the lemma is false. *)

(* the soft-failure path either returns the zero address or raises RuntimeError *)
Theorem create_soft_failure_no_type_error:
  create_soft_failure rof msg s = (res, st') ==>
  !m. res <> INR (Error (TypeError m))
Proof
  Cases_on `rof` >> strip_tac >>
  gvs[create_soft_failure_def] >> gvs[raise_def, return_def]
QED

(* KEY LEMMA for the type-soundness consumer.  The EVM-backed tail runs no
   typing checks: every outcome is an address or a non-TypeError Error. *)
Theorem create_tail_no_type_error:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_create_exception_is_error:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_exception_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_exception_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_exception_tac
QED

Theorem eval_create_no_type_error:
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys /\
  build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
    SOME code_info /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >> create_outcome_tac create_tail_no_type_error
QED
