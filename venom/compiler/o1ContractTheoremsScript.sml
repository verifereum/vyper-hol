(*
 * The O1 contract theorems, one planned admission per pass run, stated
 * with o1PassContract's contract.  o1PipelineCompose composes them into
 * S4 and S6.
 *
 * The pre-walk runs of SimplifyCFG and DretDesugar map a pass over every
 * function of the source unit, taking o1_pre_walk_inv to the walk's input
 * (o1_walk_src_inv); the nine walk runs are indexed by their stage k:
 * their step contract takes function row k to row k+1
 * (o1_step_contract_at) and their stage contract row k of o1_inv to row
 * k+1 (o1_run_contract).  MakeSSA runs twice and gets one theorem per run.
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
  o1PassContract o1DretDesugarContract o1ContractFmpLowering unitMemInv
  o1ContractCfgNorm o1ContractCfgNormGas
  venomPassSchedule venomCompilerTypes o1ContractLowerDloadStage
  o1ContractSimplifyCfg o1SimplifyCfgGasEvents o1ContractSue
  o1ContractMakeSsa o1ContractConcretize o1ContractDft

(* ===== The pre-walk runs ===== *)

(* SimplifyCFG's pre-walk takes the lowering's output (no PHI, definite
   assignment) to the walk's input (row 0). *)
Theorem o1_contract_simplify_cfg_pre_walk =
  o1ContractSimplifyCfgTheory.o1_contract_simplify_cfg_pre_walk

(* DretDesugar's run keeps every invariant I: it is the identity on
   DRET-free stage contexts. *)
Theorem o1_contract_dret_desugar_pre_walk =
  o1DretDesugarContractTheory.o1_contract_dret_desugar_pre_walk

(* ===== The walk runs, by stage ===== *)

Theorem o1_contract_make_ssa_1 =
  o1ContractMakeSsaTheory.o1_contract_make_ssa_1

Theorem o1_contract_lower_dload =
  o1ContractLowerDloadStageTheory.o1_contract_lower_dload

Theorem o1_contract_concretize_mem_loc =
  o1ContractConcretizeTheory.o1_contract_concretize_mem_loc

(* FmpLowering reads callee signatures (the walk view): the static
   invariant becomes the lowered one. *)
Theorem o1_contract_fmp_lowering =
  o1ContractFmpLoweringTheory.o1_contract_fmp_lowering

Theorem o1_contract_make_ssa_2 =
  o1ContractMakeSsaTheory.o1_contract_make_ssa_2

Theorem o1_contract_simplify_cfg =
  o1ContractSimplifyCfgTheory.o1_contract_simplify_cfg

Theorem o1_contract_sue =
  o1ContractSueTheory.o1_contract_sue

Theorem o1_contract_dft =
  o1ContractDftTheory.o1_contract_dft

Theorem o1_contract_cfg_normalization =
  o1ContractCfgNormTheory.o1_contract_cfg_normalization
