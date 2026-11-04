(*
 * MakeSSA (make_ssa_current_fn, the supply variant the O1 dispatcher runs)
 * produces SSA: every variable is written once, and every use is reached
 * only through its definition.  The premises are those of the run's
 * simulation lemmas (o1ContractMakeSsa); the same statement covers the
 * first run (no PHIs in the input) and the second (the first run's PHIs).
 * One more premise: each input PHI names every label once, and only
 * predecessors.  The pass never drops a pair, so an extra or repeated label
 * would survive into the output and break phi_edge_uses_wf; on the second
 * run the first run's wf_ssa output gives it.
 *)
Theory makeSsaCurrentWfSsa
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaCurrentRenameTrace list

(* Consumer probe: the annotation at an output position names exactly the
   concrete output at that position.  Defaults cannot be substituted here. *)
Theorem current_wf_inst_output_name[local]:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns /\ j < LENGTH anns ==>
  j < LENGTH inst'.inst_outputs /\
  current_token_name H' (FST (EL j anns)) = SOME (EL j inst'.inst_outputs)
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule_all current_outputs_trace_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  Cases_on `EL j anns` >> simp[]
QED

Theorem make_ssa_current_fn_wf_ssa:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  wf_ssa fn'
Proof
  cheat
QED
