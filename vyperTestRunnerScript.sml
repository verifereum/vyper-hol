Theory vyperTestRunner
Ancestors
  contractABI vyperABI vyperSmallStep
Libs
  cv_transLib

(* TODO: move to contractABITheory? *)

Datatype:
  abi_function = <|
    name: string
  ; inputs: (string # abi_type) list
  ; outputs: (string # abi_type) list
  ; mutability: function_mutability (* TODO: not dependent on Vyper *)
  |>
End

Datatype:
  abi_entry
  = Function abi_function
  | Event string (* TODO need any info on event args? *)
End

Datatype:
  deployment_trace = <|
    sourceAst: toplevel list
  ; contractAbi: abi_entry list
  ; deployedAddress: address
  ; deployer: address
  ; deploymentSuccess: bool
  ; value: num
  ; timeStamp: num
  ; callData: byte list
  |>
End

Definition compute_selector_names_def:
  compute_selector_names [] = [] ∧
  compute_selector_names (Function x::ls) = (
  let name = x.name in
  let argTypes = MAP SND x.inputs in
  let retTypes = MAP SND x.outputs in
  let sel = function_selector name argTypes in
    (sel, name, argTypes, retTypes)::compute_selector_names ls ) ∧
  compute_selector_names (e::ls) = compute_selector_names ls
End

val () = cv_auto_trans compute_selector_names_def;

Definition find_deploy_function_name_def:
  find_deploy_function_name [] = "__init__" ∧
  find_deploy_function_name ((FunctionDecl Deploy _ name _ _ _)::_) = name ∧
  find_deploy_function_name (_::ts) = find_deploy_function_name ts
End

val () = cv_auto_trans find_deploy_function_name_def;

Definition find_args_by_name_def:
  find_args_by_name n [] = [] ∧
  find_args_by_name n (Function x::ls) =
  (if n = x.name then MAP SND x.inputs else
     find_args_by_name n ls) ∧
  find_args_by_name n (_::ls) =
  find_args_by_name n ls
End

val () = cv_auto_trans find_args_by_name_def;

Datatype:
  call_trace = <|
    sender: address
  ; target: address
  ; callData: byte list
  ; value: num
  ; timeStamp: num
  ; gasLimit: num
  ; gasPrice: num
  ; static: bool
  ; expectedOutput: byte list option
  |>
End

Datatype:
  trace
  = Deployment deployment_trace
  | Call call_trace
  | SetBalance address num
  | ClearTransientStorage
End

Definition compute_vyper_args_def:
  compute_vyper_args ts vis name argTys cd = let
    abiTupTy = Tuple argTys;
    abiArgsTup = dec abiTupTy cd;
    rcd = enc abiTupTy abiArgsTup;
    vyTysRet = case lookup_function name vis ts
                of SOME (_,args,ret,_) => (MAP SND args, ret)
                  | NONE => ([], NoneT);
    vyArgsTenvOpt = if cd = rcd then let
      vyTys = FST vyTysRet;
      tenv = type_env ts;
      vyArgsTup = abi_to_vyper tenv (TupleT vyTys) abiArgsTup;
      vyArgs = (case OPTION_BIND vyArgsTup extract_elements
                  of NONE => [] | SOME ls => ls)
      in SOME (vyArgs, tenv) else NONE;
  in
    (vyArgsTenvOpt, SND vyTysRet)
End

Definition run_deployment_def:
  run_deployment am dt = let
    sns = compute_selector_names dt.contractAbi;
    name = find_deploy_function_name dt.sourceAst;
    argTys = find_args_by_name name dt.contractAbi;
    ar = compute_vyper_args dt.sourceAst
         Deploy name argTys dt.callData;
    res = case FST ar of NONE => INR (Error "run_deployment args")
          | SOME (args, _) => let
    tx = <| sender := dt.deployer
          ; target := dt.deployedAddress
          ; function_name := name
          ; args := args
          ; value := dt.value
          ; time_stamp := dt.timeStamp
          ; is_creation := T |>;
    in load_contract am tx dt.sourceAst
  in (sns, res)
End

val () = cv_auto_trans run_deployment_def;

Definition run_call_def:
  run_call sns am ct = let
    sel = TAKE 4 ct.callData;
    fna = case ALOOKUP sns sel of SOME fna => fna
             | NONE => ("__default__", [], []);
    name = FST fna; argTys = FST (SND fna);
    ts = case ALOOKUP am.sources ct.target of SOME ts => ts | _ => [];
    ar = compute_vyper_args ts External name argTys (DROP 4 ct.callData);
    retTys = SND (SND fna);
  in
    case FST ar of NONE => ((INR (Error "run_call args"), am),
                            (retTys, (SND ar, FEMPTY)))
  | SOME (args, tenv) => let
    tx = <| sender := ct.sender
          ; target := ct.target
          ; function_name := name
          ; args := args
          ; value := ct.value
          ; time_stamp := ct.timeStamp
          ; is_creation := F |>;
    (* TODO: set static based on ct.static *)
    (* TODO: set env data somewhere? *)
  in (call_external am tx, (retTys, (SND ar, tenv)))
End

val () = cv_auto_trans run_call_def;

Definition is_transfer_def:
  is_transfer ct ⇔
  NULL ct.callData ∧ ¬ct.static ∧
  ct.expectedOutput = SOME []
End

val () = cv_auto_trans is_transfer_def;

Definition do_transfer_def:
  do_transfer ct am = let
    acc = am.accounts;
    saddr = ct.sender;
    taddr = ct.target;
    sender = lookup_account saddr acc;
    target = lookup_account taddr acc;
    value = ct.value;
    sbal = sender.balance;
    (* TODO: charge gas too *)
  in
    if value ≤ sbal then
      INL $
      am with accounts updated_by
        (update_account saddr
          (sender with <| balance updated_by (flip $- value);
                          nonce updated_by SUC |>) o
          (update_account taddr
            (target with balance updated_by ($+ value))))
    else INR (Error "do_transfer")
End

val () = do_transfer_def
  |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF]
  |> cv_auto_trans;

Definition run_trace_def:
  run_trace snss am tr =
  case tr
  of Deployment dt => let
      result = run_deployment am dt;
      sns = FST result; res = SND result;
      res = if dt.deploymentSuccess then res
            else if ISR res then INL am
            else INR (Error "deployment success");
      snss = (dt.deployedAddress,sns)::snss;
    in
      (snss, res)
   | ClearTransientStorage => (snss,
       INL (am with globals updated_by reset_all_transient_globals))
   | SetBalance addr bal => (snss,
       INL (am with accounts updated_by
            (update_account addr
             ((lookup_account addr am.accounts) with balance := bal)))
     )
   | Call ct => (snss,
     if is_transfer ct then do_transfer ct am else
     case ALOOKUP snss ct.target
     of NONE => if IS_NONE ct.expectedOutput then INL am
                else INR (Error "sns not found")
      | SOME sns => let
        cr = run_call sns am ct;
        call_res = FST cr;
        am = SND call_res in
       case FST call_res
       of (* TODO: maybe AssertException is ok though? *)
       | INR ex => if IS_NONE ct.expectedOutput then INL am
                   else INR ex
       | INL v =>
       case ct.expectedOutput
         of NONE => INR (Error "error expected")
          | SOME out => let
              rets = SND cr;
              abiRetTys = FST rets;
              abiRetTy = Tuple abiRetTys;
              ar = SND rets;
              rawVyRetTy = FST ar; tenv = SND ar;
              alreadyTuple = (rawVyRetTy = NoneT ∨ is_TupleT rawVyRetTy);
              vyRetTy = if alreadyTuple then rawVyRetTy
                        else TupleT [rawVyRetTy];
              abiret = dec abiRetTy out;
              vyret = abi_to_vyper tenv vyRetTy abiret;
              expect = if alreadyTuple then v
                       else ArrayV (Fixed 1) [v];
            in
              if vyret = SOME expect
              then INL am
              else INR (Error "output mismatch"))
End

val () = cv_auto_trans run_trace_def;

Definition run_test_loop_def:
  run_test_loop snss am [] = INL () ∧
  run_test_loop snss am (tr::trs) =
  case run_trace snss am tr of
       (snss, INL am) => run_test_loop snss am trs
     | (_, INR ex) => INR ex
End

val () = cv_auto_trans run_test_loop_def;

Definition run_test_def:
  run_test trs = run_test_loop []
    initial_machine_state trs
End

val () = cv_auto_trans run_test_def;
