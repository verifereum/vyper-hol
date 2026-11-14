(* Source outcome-consuming-step horizon, shared by call and deployment. *)
Theory sourceCallCount
Ancestors
  vyperInterpreter vyperCallOutcome extCallOracle vyperRuntimeAccounts
  finite_map list option pair

val _ = Parse.hide "body";

Definition fn_entry_run_def:
  fn_entry_run os gobs am cx nr mut all_mods args dflts vals fbody =
    let all_tenv = type_env_all_modules all_mods in
    let n_provided = LENGTH vals in
    let n_expected = LENGTH args in
    let n_missing = n_expected - n_provided in
    if n_provided > n_expected \/ n_missing > LENGTH dflts then NONE
    else
      let needed_dflts = DROP (LENGTH dflts - n_missing) dflts in
      case (if cx.in_deploy then
              evaluate_all_constants cx am cx.txn.target all_mods
            else SOME am) of
        NONE => NONE
      | SOME am_c =>
        let st0 = initial_state am_c [FEMPTY] with
                    <| outcomes := SOME os; requests := []; gas_obs := gobs |> in
        SOME (do
                send_call_value mut cx;
                dflt_vs <- eval_external_defaults cx needed_dflts;
                case bind_arguments all_tenv args (vals ++ dflt_vs) of
                  NONE => raise (Error (RuntimeError "call bind_arguments"))
                | SOME env => do
                    set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
                    eval_stmts cx fbody
                  od
              od st0)
End

Definition call_entry_run_def:
  call_entry_run os gobs am tx =
    let src_id_opt = find_function_module am tx.target tx.function_name in
    let cx = initial_evaluation_context am.sources am.layouts tx src_id_opt in
    case ALOOKUP am.sources tx.target of
      NONE => NONE
    | SOME all_mods =>
    case (case src_id_opt of
            NONE => get_self_code cx
          | SOME src_id => get_module_code cx (SOME src_id)) of
      NONE => NONE
    | SOME ts =>
    case lookup_exported_function cx am tx.function_name of
      NONE => NONE
    | SOME (mut, nr, args, dflts, ret, fbody) =>
        fn_entry_run os gobs am cx nr mut all_mods args dflts tx.args fbody
End

Definition deploy_entry_run_def:
  deploy_entry_run os gobs tops am tx =
    let mods = [(NONE,tops)] in
    let ts = case ALOOKUP mods NONE of SOME ts => ts | NONE => [] in
    case initial_immutables (type_env_all_modules mods) mods of
      NONE => NONE
    | SOME imms =>
      let am0 = am with <| immutables updated_by CONS (tx.target,imms);
                            exports updated_by CONS (tx.target,[]) |> in
      case lookup_function NONE tx.function_name Deploy ts of
        NONE => NONE
      | SOME (mut,nr,args,dflts,ret,fbody) =>
        let cx = (initial_evaluation_context ((tx.target,mods)::am0.sources)
                    am0.layouts (tx with created_in_tx := T) NONE)
                  with in_deploy := T in
        fn_entry_run os gobs am0 cx nr mut mods args dflts tx.args fbody
End

Definition empty_failed_outcome_def:
  empty_failed_outcome =
    <| co_created := 0w; co_toDelete := []; co_success := F;
       co_returnData := []; co_accounts := K empty_account_state;
       co_tStorage := empty_transient_storage; co_logs := [] |>
End

Definition probe_failed_outcome_def:
  probe_failed_outcome =
    empty_failed_outcome with
      co_accounts := K (empty_account_state with balance := 2 ** 256)
End

Definition entry_calls_within_from_def:
  entry_calls_within_from 0 os run =
    (case run os of
       NONE => T
     | SOME (_, st_end) => st_end.outcomes <> SOME []) /\
  entry_calls_within_from (SUC k) os run =
    (case run (os ++ [probe_failed_outcome]) of
       NONE => T
     | SOME (res_p, st_p) =>
         if st_p.outcomes <> SOME [] then T
         else
           let o_next =
             case run (os ++ [empty_failed_outcome]) of
               SOME (res_e, _) =>
                 if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                    res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                    ~NULL st_p.requests
                 then failed_outcome (LAST st_p.requests)
                 else empty_failed_outcome
             | NONE => empty_failed_outcome
           in entry_calls_within_from k (os ++ [o_next]) run)
End

Definition entry_calls_within_def:
  entry_calls_within n os run =
    entry_calls_within_from (n - LENGTH (TAKE n os)) (TAKE n os) run
End

Definition source_calls_within_def:
  source_calls_within n am tx os gobs =
    entry_calls_within n os (\xs. call_entry_run xs gobs am tx)
End

Definition deploy_source_calls_within_def:
  deploy_source_calls_within n tops am tx os gobs =
    entry_calls_within n os (\xs. deploy_entry_run xs gobs tops am tx)
End
