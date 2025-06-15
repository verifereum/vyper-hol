open HolKernel boolLib bossLib Parse
     vfmTypesTheory vyperAstTheory

val () = new_theory "vyperTestRunner";

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

Datatype:
  deployment_trace = <|
    sourceAst: toplevel list
  ; contractAbi: vyper_contract_abi_entry list
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
