(*
 * FmpLowering's step contract: the structural half of its O1 pass
 * contract.  Lowering any function of a well-shaped observed unit keeps
 * the O1 function shape, takes new instruction ids and labels from the
 * supply, maps no labels, and keeps the supply's instruction-id record.
 *
 * TOP-LEVEL:
 *   fmp_step_contract  - o1_step_contract for VP_FmpLowering
 *)

Theory fmpStepContract
Ancestors
  o1PassContract fmpLowerDefs venomPassDispatcher
  fmpStepBridge fmpStepShape fmpStepStructural fmpStepRestrictions fmpStepLayout

(* Why it holds (intuition, not a prescribed proof).

   A sealed input comes back unchanged.  An unsealed one either only gets
   its signature sealed, or is rewritten: DALLOCA becomes ADD/NOT/AND/BUMP
   on a runner variable, an INVOKE of a callee taking the FMP passes the
   runner as a hidden argument, reclaim points get an ASSIGN of the
   runner, and the entry block gets the root (INITIAL_FMP for the context
   entry, FMP_PARAM otherwise, placed after the user parameters) and, for
   a non-entry function, its RETPC_PARAM re-indexed.  Every new
   instruction id comes from fresh_inst_id on the supply and every new
   variable from fresh_ir_var; no block or label is added, so the label
   map is empty.  The first block has no PHI (first_block_no_phi), so the
   inserted root keeps the PHI prefix of bb_well_formed. *)

Theorem fmp_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_FmpLowering)
Proof
  simp[o1_step_contract_def] >> rpt strip_tac >>
  drule_all fmp_fn_pass_step_input >> strip_tac >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  rpt conj_tac
  >- (simp[o1_fn_shape_def] >> rpt conj_tac
      >- metis_tac[fmp_lower_function_wf_function]
      >- metis_tac[fmp_lower_function_inst_wf, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_fn_shape_ok]
      >- metis_tac[fmp_lower_function_first_block_no_preds, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_first_block_no_phi, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_invoke_ok, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_label_refs_ok, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_no_dret]
      >- metis_tac[fmp_lower_function_dalloca_nonopaque]
      >- metis_tac[fmp_lower_function_entry_restrictions] >>
      metis_tac[SRULE[] fmp_lower_function_nonentry_restrictions])
  >- metis_tac[fmp_lower_function_fresh_names]
  >- simp[label_map_sources_ok_def] >>
  metis_tac[fmp_lower_function_inst_ok]
QED

(* The step contract of FmpLowering's walk run: it adds no ALLOCA, so the
   function row (no ALLOCA from row 3 on) carries over. *)
Theorem fmp_step_contract_at:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering)
Proof
  irule o1_step_contract_at_preserve >> simp[fmp_step_contract] >>
  rpt strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
  fs[o1_fn_row_def] >> metis_tac[fmp_lower_function_no_alloca]
QED
