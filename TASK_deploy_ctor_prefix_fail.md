# TASK: A constructor whose source run stops before its body

## Meta
Status: planned
Priority: P0
Created: 2026-11-05
Location: lowering/proofs/ctorDeployLoweringPrefixScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem deploy_ctor_prefix_fail:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
    ?fuel. !gobs.
      deploy_venom_result_rel tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context fuel dunit.cu_context vs)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `deploy_ctor_prefix_fail` is proved, with no `cheat`, and `holbuild -j4 build ctorDeployLoweringPrefixTheory` passes.
2. No statement or definition outside new helper theorems changes. No new definitions, axioms, timeout overrides, or `TRY`/`ORELSE` around search tactics (`metis_tac`, `fs`, `simp` searches).
3. Helpers go in `lowering/proofs/ctorDeployLoweringPrefixScript.sml` or in a new theory `lowering/proofs/ctorDeployLoweringPrefix<Name>Script.sml`. Do not edit any other existing file.

## Build

```sh
holbuild -j4 build ctorDeployLoweringPrefixTheory
```

## Background

A contract with a constructor, where the source never reaches the
constructor's body: no `deploy_ctor_start` holds
(`lowering/proofs/ctorDeployLoweringDefsScript.sml`). `deploy_ctor_start`
lists `load_contract`'s steps before the body (`semantics/vyperInterpreterScript.sml`,
`load_contract`, `call_external_function`): the constructor lookup, the
argument count, `bind_arguments`, `initial_immutables`,
`evaluate_all_constants`, then the value transfer (`send_call_value`) and the
lock. Most of these can't fail under the premises: `deploy_state_rel`
(`lowering/e2eDeployDefsScript.sml`) gives `tx.function_name = "__init__"`,
`constructor_args_encode` and `value_transfer_ok`; `deploy_source_ok`
(`lowering/proofs/ctorDeployDefsScript.sml`) gives the deployment typing
(`initial_immutables`, constant evaluation: `semantics/prop/vyperTypeDeploymentSoundnessScript.sml`);
a supported constructor isn't nonreentrant. What's left is a failure the
source reports as an error (`INR (Error _)`), e.g. a non-payable constructor
called with value, where the deployment unit's prefix (the payable check
`CALLVALUE`/`ISZERO`/`ASSERT`, then argument decoding) must abort, so the pair
is in `deploy_venom_result_rel` (`lowering/proofs/ctorDeployDefsScript.sml`).
The unit's code: `compile_generate_deploy` (`lowering/defs/moduleLoweringScript.sml`).

## Domain Constraints

- Default proof-step limit; checkpoints and cache on.
- Out-of-scope theorems that are admitted (cheated) are allowed dependencies,
  including `deploy_imm_budget_ok` (`lowering/proofs/ctorDeployLoweringBudgetScript.sml`);
  add no admissions of your own.
- If the statement is false, stop and give a concrete counterexample and the
  smallest change to the statement that would make it true.

## Available Resources

- `lowering/proofs/ctorDeployLoweringPrefixScript.sml` (target)
- `lowering/proofs/ctorDeployLoweringDefsScript.sml`, `lowering/proofs/ctorDeployDefsScript.sml`, `lowering/e2eDeployDefsScript.sml`
- `lowering/defs/compileVyperScript.sml`, `lowering/defs/vyperCompilerScript.sml`, `lowering/defs/moduleLoweringScript.sml`
- `lowering/ctorRegisterArgsScript.sml` (constructor argument decoding)
- `lowering/e2e/e2eEntryScript.sml`, `lowering/fragExecScript.sml`, `venom/defs/venomExecSemanticsScript.sml`
- `semantics/vyperInterpreterScript.sml`, `semantics/prop/vyperTypeDeploymentSoundnessScript.sml`

## Notes

The statement parses: it built with `cheat` in this worktree. Many shared
ancestors are cheated locally (the commit "LOCAL OVERLAY"); that is expected.
Do not touch or revert that commit.

### Update: the negative-argument counterexample is ruled out

The previous run's witness (`__init__(x: uint256)`, `tx.args = [IntV (-1)]`)
predates the current head. `constructor_args_encode_def`
(`lowering/e2eDeployDefsScript.sml`) now also requires
`IS_SOME (bind_arguments (type_env tops) args tx.args)`, and
`deploy_state_rel` includes `constructor_args_encode`, so that witness no
longer satisfies the premises. `deploy_prefix_negative_counterexample` was
removed. The concrete witness theorems in `ctorDeployLoweringPrefixScript.sml`
(`deploy_prefix_negative_*`, `*_probe`, `*_artifact`, the concrete
`deploy_state_rel` instance) are obsolete: delete those that no longer build or
no longer serve the proof, and keep the general helpers (parse lemmas,
`deploy_prefix_safe_*_no_abort`). Prove the frozen statement as-is.
