Theory lowerDloadPtrForward
Ancestors
  contextCodegenRel venomExecSemantics

(* Interval membership is deliberately distinct from revert_forward_at:
   the latter marks only the two endpoints. *)
Theorem revert_forward_pair_interval_opcode:
  !bb i j k inst.
    revert_forward_pair bb i j /\ i <= k /\ k <= j /\
    get_instruction bb k = SOME inst ==>
    (k = i /\ inst.inst_opcode = RETURNDATACOPY) \/
    (i < k /\ k < j /\ inst.inst_opcode = ASSIGN) \/
    (k = j /\ inst.inst_opcode = REVERT)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[revert_forward_pair_def] >>
  Cases_on `k = i` >- gvs[] >>
  Cases_on `k = j` >- gvs[] >>
  `i < k /\ k < j` by decide_tac >>
  metis_tac[]
QED
