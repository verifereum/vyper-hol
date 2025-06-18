open HolKernel boolLib bossLib Parse cv_transLib
     vfmTypesTheory vyperAstTheory
     vyperAbiTheory contractABITheory
     vyperInterpreterTheory vyperSmallStepTheory

val () = new_theory "vyperTestRunner";

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
  abi_entry = Function abi_function (* TODO: event, etc. *)
End

(*
Datatype:
  vyper_abi_function = <|
    name: identifier
  ; inputs: argument list
  ; outputs: argument list
  ; mutability: function_mutability |>
End

Datatype:
  vyper_contract_abi_entry
  = Function vyper_abi_function
End
*)

Datatype:
  deployment_trace = <|
    sourceAst: toplevel list
  ; contractAbi: abi_entry list
  ; deployedAddress: address
  ; deployer: address
  ; deploymentSuccess: bool
  ; value: num
  ; callData: byte list
  |>
End

Definition compute_selector_names_def:
  compute_selector_names [] = [] ∧
  compute_selector_names (Function x::ls) =
  let name = x.name in
  let argTypes = MAP SND x.inputs in
  let sel = function_selector name argTypes in
    (sel, name, argTypes)::compute_selector_names ls
End

val () = cv_auto_trans compute_selector_names_def;

Datatype:
  call_trace = <|
    sender: address
  ; target: address
  ; callData: byte list
  ; value: num
  ; gasLimit: num
  ; gasPrice: num
  ; static: bool
  ; expectedOutput: byte list option
  |>
End

Datatype:
  trace = Deployment deployment_trace | Call call_trace
End

Definition find_function_args_by_name_def:
  find_function_args_by_name n [] = [] ∧
  find_function_args_by_name n (FunctionDecl _ _ id args _ _ :: ts) =
  (if n = id then args else find_function_args_by_name n ts) ∧
  find_function_args_by_name n (_ :: ts) =
  find_function_args_by_name n ts
End

Definition compute_vyper_args_def:
  compute_vyper_args ts name argTys cd = let
    abiArgsTup = dec (Tuple argTys) cd;
    vyTys = MAP SND $ find_function_args_by_name name ts;
    vyArgsTup = abi_to_vyper (TupleT vyTys) abiArgsTup;
  in
    case OPTION_BIND vyArgsTup extract_elements
      of NONE => [] | SOME ls => ls
End

Definition run_deployment_def:
  run_deployment am dt = let
    sns = compute_selector_names dt.contractAbi;
    sel = TAKE 4 dt.callData;
    fna = case ALOOKUP sns sel of SOME fna => fna | NONE => ("__init__", []);
    name = FST fna; argTys = SND fna;
    tx = <| sender := dt.deployer
          ; target := dt.deployedAddress
          ; function_name := name
          ; args := compute_vyper_args dt.sourceAst name
                      argTys (DROP 4 dt.callData)
          ; value := dt.value |>;
  in (sns, load_contract am tx dt.sourceAst)
  (* TODO: check dt.deploymentSuccess *)
End

val () = cv_auto_trans run_deployment_def;

Definition run_call_def:
  run_call sns am ct = let
    sel = TAKE 4 ct.callData;
    fna = case ALOOKUP sns sel of SOME fna => fna | NONE => ("__default__", []);
    name = FST fna; argTys = SND fna;
    ts = case ALOOKUP am.sources ct.target of SOME ts => ts | _ => [];
    tx = <| sender := ct.sender
          ; target := ct.target
          ; function_name := name
          ; args := compute_vyper_args ts name argTys (DROP 4 ct.callData)
          ; value := ct.value |>;
  in call_external am tx
End

val () = cv_auto_trans run_call_def;

val () = export_theory();
