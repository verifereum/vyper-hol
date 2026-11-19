# Compiler proof spine

The path from each top theorem down through the stage contracts it uses.
Per stage: the contract theorem, the hypotheses that cross into it from
the stage before or from the caller, and the theorem that produces each
one. Read it from a top statement down to review what the tops rest on,
or from a restriction (a `supported_*` gate, an excluded construct) up to
the first contract that must change to lift it.

[Compiler proof dependencies](compiler-proof-dependencies.md) is the
older, dated audit of the same boundary; this page is kept current.
`tools/proof_index.py` lists, per theory, which stage contracts' proofs
reach it (`theories.tsv`, column `stages`) and which theorems the tops
use.

## Top theorems

| Theorem | Script |
|---|---|
| `e2eCorrectness.vyper_call_correct` | `lowering/e2eCorrectnessScript.sml` |
| `e2eDeployCorrectness.e2e_deploy_correctness` | `lowering/e2eDeployCorrectnessScript.sml` |
| `e2eGasSufficientTop.vyper_call_gas_sufficient` | `lowering/e2eGasSufficientTopScript.sml` |
| `e2eGasSufficientTop.e2e_deploy_gas_sufficient` | `lowering/e2eGasSufficientTopScript.sml` |

The call theorem composes the stages in `lowering/e2eCorrectnessScript.sml`,
where `vyper_call_correct_dispatched` splits into `vyper_call_correct_identity`
and `vyper_call_correct_asm_opt` by finalizer; deployment in
`lowering/e2eDeployAtMarksScript.sml`, gas in
`lowering/e2eGasSufficientScript.sml`.

## S1: lowering runs the source program

- Contract: `loweringCalldataCorrect.lower_vyper_runtime_unit_correct_dispatched_with`
- Hypotheses crossing the boundary:
- Producers:

## S2: lowered units have the source-unit shape

- Contract: `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok`
- Hypotheses crossing the boundary:
- Producers:

## S3: lowered units are memory-safe

- Contract: `loweringMemCorrect.lower_vyper_runtime_unit_memory_ok`
- Hypotheses crossing the boundary:
- Producers:

## S3d: DLOAD offsets stay in range

- Contract: `loweringMemCorrect.lower_vyper_runtime_unit_dload_offset_ok`
- Hypotheses crossing the boundary:
- Producers:

## S4: the O1 Venom pipeline simulates its input

- Contract: `o1PipelineCorrect.run_venom_pipeline_correct`
- Hypotheses crossing the boundary:
- Producers:

## S5: the O1 pipeline's memory obligations

- Contracts: `o1PipelineCorrect.o1_pipeline_memory_obligations`;
  `e2eProducers.o1_pipeline_memory_obligations_raw`, the form the call,
  deployment and gas proofs use
- Hypotheses crossing the boundary:
- Producers:

## S6: the O1 pipeline's output shape

- Contract: `o1PipelineCorrect.run_venom_pipeline_output_shape`
- Hypotheses crossing the boundary:
- Producers:

## S7: code generation

- Contracts: `codegenCorrectness.codegen_correct` (identity finalizer),
  `codegenAsmOpt.codegen_correct_asm_opt` (assembly optimizer)
- Hypotheses crossing the boundary:
- Producers:

## Deployment

- Contract:
- Hypotheses crossing the boundary:
- Producers:

## Gas sufficiency

- Contracts: `codegenCorrectness.codegen_gas_sufficient` (calls),
  `ctorDeployFrame.deploy_frame_gas_sufficient` (deployment); linked to
  the call pipeline by `e2eCorrectness.call_pipeline_gas_link`
- Hypotheses crossing the boundary:
- Producers:
