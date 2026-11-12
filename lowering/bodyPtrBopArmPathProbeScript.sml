Theory bodyPtrBopArmPathProbe
Ancestors
  bodyPtrBopJumpGhost bodyPtrBopWordPathProbe fragGasPathPtr fragExec

(* Supplied witnesses compose on this execution. This is not path inversion. *)
Theorem bop_arm_path_probe:
  gas_path_ptr D lo ctx fn PG G0 tn0 s0 k G1 tn1 sresult /\
  sresult = OK s1 /\
  gas_path_ptr_edge D lo ctx fn PG G1 tn1 s1 n G2 tn2 (OK s2) /\
  gas_path_ptr_edge D lo ctx fn PG G2 tn2 s2 m G3 tn3 (OK s3) /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME b1 /\
  get_instruction b1 s1.vs_inst_idx = SOME assign /\
  assign.inst_opcode = ASSIGN /\ assign.inst_outputs = [z] /\
  assign.inst_operands = [op] /\ op_prov G1 op = NONE /\
  lookup_block s2.vs_current_bb fn.fn_blocks = SOME b2 /\
  get_instruction b2 s2.vs_inst_idx = SOME jump /\
  jump.inst_opcode = JMP /\
  lookup_block s3.vs_current_bb fn.fn_blocks = SOME join /\
  phi_prefix_length join.bb_instructions = 0 /\ ~s3.vs_halted ==>
  gas_path_ptr D lo ctx fn PG G0 tn0 s0 (k + (n + m)) G3 tn3 (OK s3) /\
  op_prov G3 (Var z) = NONE
Proof
  strip_tac >>
  `G3 = G2 /\ tn3 = tn2` by
    (drule bop_jump_edge_ghost >> disch_then drule_all >> simp[]) >>
  `FLOOKUP G2 z = NONE` by
    (qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ G2 _ _ _ G3 _ _` kall_tac >>
     drule bop_forward_edge_none >> simp[] >> disch_then drule_all >> simp[]) >>
  reverse conj_tac >- simp[ptrDisciplineTheory.op_prov_def] >>
  `gas_path_ptr D lo ctx fn PG G2 tn2 s2 m G3 tn3 (OK s3)` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_0] >>
  `gas_path_ptr D lo ctx fn PG G1 tn1 s1 (n + m) G3 tn3 (OK s3)` by
    metis_tac[gas_path_ptr_rules] >>
  gvs[] >> metis_tac[gas_path_ptr_then]
QED
