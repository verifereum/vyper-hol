(* Successful prefix composition retains the counted instruction cursor. *)
Theory bodyPtrPrecompileBuiltinsSeq
Ancestors fragGasSeqPtr fragExec exprLoweringProps instIdxIndep venomState list arithmetic

Theorem inst_seq_ptr_append:
  !xs s t ys G tn G2 tn2.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t ==>
    (inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2 <=>
     ?G1 tn1.
       inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\
       inst_seq_ptr D lo ctx fn PG G1 tn1 ys
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2)
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`, `ys`,
     `step_prov PG G h u`, `step_taint h s u tn`, `G2`, `tn2`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD1] >>
  metis_tac[]
QED

Theorem inst_seq_ptr_append_cursors:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = OK t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn xs
    (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 ys
    (t with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys)
    (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> gen_tac >>
  `run_inst_seq xs (s with vs_inst_idx := k) =
     OK (t with vs_inst_idx := k)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all inst_seq_ptr_append >> simp[] >> metis_tac[]
QED
