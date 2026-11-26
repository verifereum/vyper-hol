# e2e_deploy_correctness_deployed

## run_call

The EVM run of the creation frame finishes, with result `r` and final
state `es'`.

## frame_starved

Either the frame starved: it stopped with `OutOfGas`, or with
`StackOverflow` in code that fails the static stack check.

## gas_readings_rel

Or the rest holds for every list of gas readings `gs` consistent with the
values the EVM's `GAS` instructions returned in this run.

## deploy_result_rel_at

The run's result matches the source constructor's, run with those readings
and with the call outcomes this run observed.

## IN

What follows applies when the new account is not scheduled for deletion.

## load_contract

The source constructor succeeds, giving the source machine `am'`.

## deployed

The contract is then deployed at its address in the next source machine,
which is what the call theorems assume about it.

## target

For every later transaction `tx'` to that address,

## storage_ok

the call theorems' storage hypothesis holds for `H` on the next source
machine.

# vyper_call_correct_deployed

## run_call

The EVM run of the call frame finishes, with result `r` and final state
`es'`.

## frame_starved

Either the frame starved: it stopped with `OutOfGas`, or with
`StackOverflow` in code that fails the static stack check.

## calldata_result_rel

Or the run gives the source's result: if the calldata selects no function,
the frame reverts with empty return data; otherwise the result matches the
source run of the selected function on the decoded arguments.

## LENGTH

Whatever the result, when the call is the only frame running,

## IN

and the contract is not scheduled for deletion after the run,

## deployed

the contract is still deployed in the world the call leaves: the EVM's
accounts after a successful call, the world before it after a failed one.

# e2e_deploy_gas_sufficient

## g

There is an amount of gas `g` such that the rest holds for every `g'` of
at least `g` added to the creation frame's gas.

## run_call

The run with the added gas finishes, with result `r` and final state `es'`.

## deploy_within

If the source constructor, run with that run's call outcomes, stays within
`H` for every gas filling,

## deploy_gas_source_exempt

does not stop with one of the listed errors for any gas filling,

## LENGTH

and the run's call trace has fewer than 2⁶⁴ entries,

## r

then if the run still ran out of gas,

## max_code_size

the runtime bytecode with the immutables appended is longer than the EVM's
code-size limit.

# vyper_call_gas_sufficient_deployed

## g

There is an amount of gas `g` such that the rest holds for every `g'` of
at least `g` added to the call frame's gas.

## run_call

The run with the added gas finishes, with result `r` and final state `es'`.

## call_within

If the source run, with that run's call outcomes, stays within `H` for
every gas filling,

## calldata_dispatch

and, when the calldata selects function `f` with arguments `vals`,

## gas_source_exempt

that function's source run does not stop with one of the listed errors for
any gas filling,

## LENGTH

and the run's call trace has fewer than 2⁶⁴ entries,

## frame_raises

then the frame does not run out of gas.
