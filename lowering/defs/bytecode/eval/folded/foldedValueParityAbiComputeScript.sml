(* Generic equalities for bounded ABI evaluation. *)
Theory foldedValueParityAbiCompute
Ancestors foldedValueParityCompute stackPlanGenCompute codegenReadyCompute
Libs foldedValueParityLib

Theorem parity_dfs_split:
  !insts order eda offspring flip rest count state.
    dfs_run_fuel (dfs_step insts order eda offspring flip) (rest + count) state =
    dfs_run_fuel (dfs_step insts order eda offspring flip) rest
      (dfs_run_fuel (dfs_step insts order eda offspring flip) count state)
Proof
  simp[dftDefsTheory.dfs_run_fuel_eq_FUNPOW, arithmeticTheory.FUNPOW_ADD]
QED

Theorem parity_uncurry_compute:
  UNCURRY f p = pair_CASE p f
Proof
  Cases_on `p` >> simp[pairTheory.UNCURRY_DEF, pairTheory.pair_case_thm]
QED

Theorem parity_operand_equiv_refl:
  !graph operand. operand_equiv graph operand operand
Proof
  simp[dfgDefsTheory.operand_equiv_def]
QED

Theorem parity_plan_last:
  generate_block_insts_plan_acc liveness dfg cfg func bb_label is_halting
    n_params block_len i [inst] ps acc =
  (case generate_inst_plan liveness dfg cfg func inst
      (live_vars_at liveness bb_label block_len) is_halting F bb_label ps of
     NONE => NONE
   | SOME (ops,ps') =>
       generate_block_insts_plan_acc liveness dfg cfg func bb_label is_halting
         n_params block_len (i + 1) [] ps' (REVERSE ops ++ acc))
Proof
  CONV_TAC (LAND_CONV (REWR_CONV (CONJUNCT2 (SPEC_ALL
    stackPlanGenComputeTheory.generate_block_insts_plan_acc_def)))) >> simp[]
QED

Theorem parity_plan_next:
  generate_block_insts_plan_acc liveness dfg cfg func bb_label is_halting
    n_params block_len i (inst::next_i::rest) ps acc =
  (case generate_inst_plan liveness dfg cfg func inst
      (live_vars_at liveness bb_label (i + n_params + 1)) is_halting
      (is_terminator next_i.inst_opcode) bb_label ps of
     NONE => NONE
   | SOME (ops,ps') =>
       generate_block_insts_plan_acc liveness dfg cfg func bb_label is_halting
         n_params block_len (i + 1) (next_i::rest) ps' (REVERSE ops ++ acc))
Proof
  CONV_TAC (LAND_CONV (REWR_CONV (CONJUNCT2 (SPEC_ALL
    stackPlanGenComputeTheory.generate_block_insts_plan_acc_def)))) >> simp[]
QED

Theorem parity_plan_fuel:
  !fuel live dfg cfg func worklist visited ps continuation.
    (case generate_fn_plan_aux_fuel fuel live dfg cfg func worklist visited ps of
       NONE => F
     | SOME result => continuation (SOME result)) ==>
    continuation (generate_fn_plan_aux live dfg cfg func worklist visited ps)
Proof
  rpt gen_tac >>
  Cases_on `generate_fn_plan_aux_fuel fuel live dfg cfg func worklist visited ps` >>
  simp[] >> strip_tac >>
  drule_all (CONJUNCT1 (Q.SPEC `fuel` stackPlanGenComputeTheory.generate_plan_fuel_some)) >>
  simp[]
QED

val () = foldedValueParityLib.audit "foldedValueParityAbiCompute";
