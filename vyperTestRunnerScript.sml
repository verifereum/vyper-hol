open HolKernel boolLib bossLib Parse
     contractABITheory vfmTypesTheory vyperAstTheory

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

val () = export_theory();
