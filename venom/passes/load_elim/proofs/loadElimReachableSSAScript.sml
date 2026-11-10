Theory loadElimReachableSSA
Ancestors
  venomWf venomInst list pair

Definition le_reachable_ssa_def:
  le_reachable_ssa fn <=>
    ssa_form fn /\
    (!bb inst.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      fn_reachable fn bb.bb_label /\ inst.inst_opcode <> PHI ==>
      !v. MEM (Var v) inst.inst_operands ==>
          def_available_at fn bb (SOME inst) v) /\
    (!bb inst.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI ==>
      phi_well_formed inst.inst_operands /\
      ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
      (!pred. fn_cfg_edge fn pred bb.bb_label <=>
        ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred) /\
      (!pred v.
        MEM (pred,v) (phi_pairs inst.inst_operands) /\
        fn_reachable fn pred ==>
        ?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
             fn_cfg_edge fn pred bb.bb_label /\
             def_available_at fn pb NONE v))
End

Theorem le_wf_ssa_reachable:
  wf_ssa fn ==> le_reachable_ssa fn
Proof
  rw[wf_ssa_def, le_reachable_ssa_def] >>
  fs[def_dominates_uses_def, phi_edge_uses_wf_def] >> metis_tac[]
QED

Theorem le_reachable_ssa_unique:
  le_reachable_ssa fn ==> ssa_form fn
Proof
  simp[le_reachable_ssa_def]
QED

Theorem le_reachable_ssa_ordinary_available:
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ fn_reachable fn bb.bb_label /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  def_available_at fn bb (SOME inst) v
Proof
  simp[le_reachable_ssa_def] >> metis_tac[]
QED

Theorem le_reachable_ssa_phi_shape:
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
  phi_well_formed inst.inst_operands
Proof
  simp[le_reachable_ssa_def] >> metis_tac[]
QED

Theorem le_reachable_ssa_phi_distinct:
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))
Proof
  simp[le_reachable_ssa_def] >> metis_tac[]
QED

Theorem le_reachable_ssa_phi_edges:
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
  (fn_cfg_edge fn pred bb.bb_label <=>
    ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)
Proof
  simp[le_reachable_ssa_def] >> metis_tac[]
QED

Theorem le_reachable_ssa_phi_available:
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (pred,v) (phi_pairs inst.inst_operands) /\ fn_reachable fn pred ==>
  ?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
       fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pb NONE v
Proof
  simp[le_reachable_ssa_def] >> metis_tac[]
QED
