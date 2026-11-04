(*
 * CFG Normalization Pass — Correctness Statement
 *
 * About cfg_norm_function_supply, the variant the pass dispatcher runs.
 * Proofs in proofs/cfgNormSupplySimScript.sml and
 * venom/compiler/o1ContractCfgNormScript.sml.
 *)

Theory cfgNormCorrectness
Ancestors
  cfgNormSupplySim o1ContractCfgNorm cfgNormIter

Theorem cfg_norm_pass_correct:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn' /\ wf_ssa fn' /\ wf_function fn'
Proof
  strip_tac >>
  `supply_norm_inv s fn` by simp[supply_norm_inv_def] >>
  `supply_norm_inv s' fn'` by metis_tac[cfg_norm_function_supply_norm_inv] >>
  gvs[supply_norm_inv_def] >>
  metis_tac[cfg_norm_function_supply_fn_bisim]
QED
