(* Final-target structural certificates.  Reuse the existing pass-wide
 * block preservation boundary; no second layout-transfer proof is needed. *)
Theory makeSsaCurrentTargetWf
Ancestors
  o1MakeSsaFormats venomWf o1PassContract irSupply makeSsaCurrentDefs list

Theorem current_final_block_well_formed:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  MEM bb' fn'.fn_blocks ==> bb_well_formed bb'
Proof
  rpt strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by
    gvs[EVERY_MEM, wf_function_def] >>
  drule_all make_ssa_current_fn_blocks_well_formed >>
  simp[EVERY_MEM] >> strip_tac >> metis_tac[]
QED
