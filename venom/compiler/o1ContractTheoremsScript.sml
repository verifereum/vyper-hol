(*
 * The O1 contract theorems, one planned admission per pass run, stated
 * with o1PassContract's contract.  o1PipelineCompose composes them into
 * S4 and S6.
 *
 * The pre-walk runs of SimplifyCFG and DretDesugar map a pass over every
 * function of the source unit and keep its invariant (o1_src_inv); the
 * nine walk runs are indexed by their stage k: their step contract takes
 * function row k to row k+1 (o1_step_contract_at) and their stage contract
 * row k of o1_inv to row k+1 (o1_run_contract).  MakeSSA runs twice and
 * gets one theorem per run.
 *
 * A pass task proves its theorem in its own theory, under the same
 * statement, and the admission here becomes an alias of that proof
 * (Theorem o1_contract_<run> = <passTheory>.o1_contract_<run>), so
 * nothing downstream changes.
 *
 * Each holds for every dead-byte set D (free in the statements).  A pass
 * that keeps every byte proves the exact simulation and lifts it with
 * unit_result_rel_dead_result_rel.
 *)
Theory o1ContractTheorems
Ancestors
  o1PassContract o1DretDesugarContract unitMemInv venomPassSchedule
  venomCompilerTypes

(* ===== The pre-walk runs ===== *)

Theorem o1_contract_simplify_cfg_pre_walk:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  (!view. o1_stage_contract rpolicy D (CFP_Simple VP_SimplifyCFG) view no_pre
            o1_src_inv o1_src_inv)
Proof
  cheat
QED

(* DretDesugar's run keeps every invariant I: it is the identity on
   DRET-free stage contexts. *)
Theorem o1_contract_dret_desugar_pre_walk =
  o1DretDesugarContractTheory.o1_contract_dret_desugar_pre_walk

(* ===== The walk runs, by stage ===== *)

Theorem o1_contract_make_ssa_1:
  o1_step_contract_at 0 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 0
Proof
  cheat
QED

Theorem o1_contract_lower_dload:
  o1_step_contract_at 1 rpolicy (CFP_Simple VP_LowerDload) /\
  o1_run_contract rpolicy D 1
Proof
  cheat
QED

(* ConcretizeMemLoc reads callee layouts (the walk view): the raw
   invariant becomes the static one. *)
Theorem o1_contract_concretize_mem_loc:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc) /\
  o1_run_contract rpolicy D 2
Proof
  cheat
QED

(* FmpLowering reads callee signatures (the walk view): the static
   invariant becomes the lowered one. *)
Theorem o1_contract_fmp_lowering:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering) /\
  o1_run_contract rpolicy D 3
Proof
  cheat
QED

Theorem o1_contract_make_ssa_2:
  o1_step_contract_at 4 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 4
Proof
  cheat
QED

Theorem o1_contract_simplify_cfg:
  o1_step_contract_at 5 rpolicy (CFP_Simple VP_SimplifyCFG) /\
  o1_run_contract rpolicy D 5
Proof
  cheat
QED

Theorem o1_contract_sue:
  o1_step_contract_at 6 rpolicy (CFP_Simple VP_SingleUseExpansion) /\
  o1_run_contract rpolicy D 6
Proof
  cheat
QED

(* DFT reorders GAS reads: forall-out exists-in over the oracle. *)
Theorem o1_contract_dft:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT) /\
  o1_run_contract_gas rpolicy D 7
Proof
  cheat
QED

Theorem o1_contract_cfg_normalization:
  o1_step_contract_at 8 rpolicy (CFP_Simple VP_CFGNormalization) /\
  o1_run_contract rpolicy D 8
Proof
  cheat
QED
