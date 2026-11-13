(* MakeSSA cannot introduce a label operand absent from both the input's
   operands and its block labels.  PHI predecessor labels need the latter. *)
Theory o1LabelFlowSourceSsaLabels
Ancestors
  o1ContractMakeSsaPtrOk o1MakeSsaStructuralShape makeSsaCurrentProps
  venomInst

Theorem make_ssa_current_fn_label_operand_absent:
  make_ssa_input_ok f /\ fn_inst_wf f /\ wf_function f /\
  first_block_no_preds f /\ first_block_no_phi f /\
  ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s f = (g,s') /\
  ~MEM l (fn_labels f) /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label l) i.inst_operands) ==>
  (!i. MEM i (fn_insts g) ==> ~MEM (Label l) i.inst_operands)
Proof
  strip_tac >>
  drule_all mssa_origin >> strip_tac >>
  drule_all mssa_wf_ssa >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  rpt strip_tac >>
  Cases_on `i.inst_opcode = PHI`
  >- (drule_all wf_ssa_phi_label_ref >> gvs[fn_labels_def]) >>
  qpat_x_assum `!inst. MEM inst (fn_insts g) ==> _` drule >>
  rewrite_tac[mssa_inst_origin_def] >> disch_then strip_assume_tac >>
  gvs[] >>
  `MEM (Label l)
     (MAP (\op. case op of Var u => Var (orig u) | _ => op)
       i.inst_operands)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `Label l` >> simp[]) >>
  metis_tac[]
QED
