(* Shared observational effects of the checked encoder prefix. *)
Theory revertReasonPrefixFramePtr
Ancestors revertReasonPrefixPtr ghostObservationPtr decoderGhostFramePtr
  fragGasSeqPtr revertReasonLayout context venomInst

Theorem inst_seq_ptr_other_output_frame:
  !is D lo ctx func PG G tn s Gf tnf x.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. ~MEM x i.inst_outputs) is ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_prov_other_output, step_taint_other_output]
QED

Theorem inst_seq_ptr_nonmemory_taint_frame:
  !is D lo ctx func PG G tn s Gf tnf.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
      i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) is ==>
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_taint_nonmemory_frame]
QED

Theorem revert_reason_prefix_ghost_observations:
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn ms) s Gf tnf ==>
  (!x. (!k. k < 3 ==> x <> STRING #"%" (toString (vn+k))) ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  tnf.t_imm = tn.t_imm
Proof
  strip_tac >> conj_tac >-
    (gen_tac >> disch_tac >> irule inst_seq_ptr_other_output_frame >>
     goal_assum (drule_at Any) >>
     simp[revert_reason_prefix_def, mk_inst_def] >>
     qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  irule inst_seq_ptr_nonmemory_taint_frame >>
  goal_assum (drule_at Any) >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED
