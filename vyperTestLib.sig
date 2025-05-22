signature vyperTestLib = sig

  type abi_function = {
    name: string,
    inputs: (string * term) list,
    outputs: (string * term) list,
    mutability: term
  }

  datatype abi_entry = Function of abi_function

  type deployment = {
    sourceCode: term,
    abi: abi_entry list,
    deployedAddress: term,
    expectSuccess: bool,
    value: string
  }

  type call = {
    sender: term,
    callData: term,
    value: string,
    gasLimit: string,
    gasPrice: string,
    target: term,
    static: bool,
    expectedOutput: term option
  }

  datatype trace =
      Deployment of deployment
    | Call of call

  val read_test_json : string -> (string * trace list) list

end
