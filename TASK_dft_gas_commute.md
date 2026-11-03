# TASK: DFT commutation lemmas under the gas-readings oracle

## Meta
- Project: vyper-hol (HOL4, holbuild)
- Script: venom/passes/dft/proofs/dftBlockSimScript.sml
- Theory: dftBlockSimTheory

## Theorem Statement (FROZEN)

Four theorems in dftBlockSimScript.sml, each currently `cheat`:

```sml
Theorem gas_pair_commute:
  !fuel ctx inst1 inst2 ss v2 s21.
    gas_pair inst1.inst_opcode inst2.inst_opcode /\
    inst_wf inst1 /\ inst_wf inst2 /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst1 v2 = OK s21 ==>
    ?ss1 v1. ss = (ss1 with vs_gas_readings := ss.vs_gas_readings) /\
             step_inst fuel ctx inst1 ss1 = OK v1 /\
             step_inst fuel ctx inst2 v1 = OK s21
```

plus `independent_commute_eq` and `output_var_agree_across_independent`
exactly as they stand in the file (each gained the premise
`~gas_pair inst1.inst_opcode inst2.inst_opcode`, resp. `inst_a`/`inst_b`).
Their original proofs are kept in a comment inside the `Proof`.

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria
- The four theorems above proved with no `cheat`, statements byte-identical.
- `holbuild -j4 build dftPermSimTheory` succeeds, 0 CHEAT in dftBlockSim.
- No new axioms, no new hypotheses on frozen statements. Helper lemmas and
  theories are fine (DFT ones under venom/passes/dft/proofs/).

## Build
From the project root:

```
holbuild -j4 build dftPermSimTheory
```

## Background
- GAS now pops `vs_gas_readings` (`exec_gas`, venom/defs/venomExecSemanticsScript.sml),
  reading `0w` once the list is empty, and `is_effect_free_op GAS = F`. An
  INVOKE's callee can run GAS, so INVOKE consumes readings too (`merge_callee_state`
  copies `vs_gas_readings` back). `gas_pair` (top of dftBlockSim) names the pairs
  that both consume readings.
- `independent_commute_eq` / `output_var_agree_across_independent` broke only
  because GAS used to be effect-free: their old proofs fail in the case where
  one side is GAS and the other is neither GAS nor INVOKE.
  `passSharedFrameTheory.effects_independent_commute` excludes GAS on both
  sides. A non-GAS, non-INVOKE instruction keeps `vs_gas_readings`, so GAS
  reads the same value on either side of it.
- `gas_pair_commute`: the original order runs from a state that differs from
  `ss` only in `vs_gas_readings` and ends in exactly `s21`. Intended readings
  (R = ss.vs_gas_readings, hd0 l = HD l or 0w on []):
  - GAS x GAS: swapped order reads x = hd0 R then y = hd0 (TL R); take
    `y :: x :: DROP 2 R`.
  - inst2 = INVOKE, inst1 = GAS: callee consumes n (from `gas_oracle_replay`,
    step clause), GAS then reads y = hd0 (DROP n R); take
    `y :: gas_prefix n R ++ DROP (n+1) R`.
  - inst2 = GAS, inst1 = INVOKE: GAS reads y = hd0 R, callee consumes n from
    TL R; take `gas_prefix n (TL R) ++ y :: DROP n (TL R)`.
  `setup_callee` resets `vs_vars`, so the callee's start states differ only
  in readings, which is the replay premise.

## Domain Constraints
- Don't change any definition under venom/defs/ or venom/passes/dft/defs/, nor
  `gas_pair_def`, `bi_independent_def`, `ext_bi_independent_def`.
- Don't raise the tactic timeout; no `TRY`/`ORELSE` around metis or other search.
- Theorems consumed outside their own theory keep their statements.

## Available Resources
- venom/proofs/gasOracleReplayScript.sml: `gas_oracle_replay`, `gas_prefix`, `gas_replay_at`.
- venom/passes/dft/proofs/dftCommutationScript.sml: frame lemmas, `exec_gas_frame`.
- venom/passes/shared/proofs/passSharedFrameScript.sml: `effects_independent_commute`.
- venom/defs/venomExecSemanticsScript.sml: `step_inst`, `exec_gas`, `setup_callee`,
  `merge_callee_state`, `bind_outputs`.

## Notes
- Other cheats in the project (dftRunRel, o1ContractDft) are out of scope.
