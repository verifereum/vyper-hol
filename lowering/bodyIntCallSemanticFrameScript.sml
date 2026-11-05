Theory bodyIntCallSemanticFrame
Ancestors
  fragExec exprLoweringProps venomCallOracleDefs venomState venomExecSemantics list rich_list

Theorem run_inst_seq_observation:
  !insts s t obs.
    EVERY (\i. !s t. step_inst_base i s = OK t ==> obs t = obs s) insts /\
    run_inst_seq insts s = OK t ==> obs t = obs s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem frag_exec_run_inst_seq_observation:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. !s t. step_inst_base i s = OK t ==> obs t = obs s)
    (emitted_insts sa sb) /\
  (!s n. obs (s with vs_inst_idx := n) = obs s) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb (\s. P s /\ obs s = saved)
    (\t. Q t /\ obs t = saved) (\r. F)
Proof
  strip_tac >> irule frag_exec_run_inst_seq >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!s. P s ==> _` drule >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >>
  drule_all run_inst_seq_observation >> simp[]
QED

Theorem frag_exec_run_inst_seq_storage_frame:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. !s t. step_inst_base i s = OK t ==>
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s) (emitted_insts sa sb) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb
    (\s. P s /\ (contract_storage s,contract_transient s) = saved)
    (\t. Q t /\ (contract_storage t,contract_transient t) = saved) (\r. F)
Proof
  strip_tac >>
  ho_match_mp_tac frag_exec_run_inst_seq_observation >>
  simp[contract_storage_def, contract_transient_def] >>
  gvs[EVERY_MEM, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Semantic frame probe has unproved dependencies"
  end) [run_inst_seq_observation, frag_exec_run_inst_seq_observation,
        frag_exec_run_inst_seq_storage_frame];

Theorem frag_exec_observation_then:
  cs_extends sa sm /\ cs_extends sm sb /\
  frag_exec ctx sa sm P (\m. A m /\ obs m = saved) (\r. F) /\
  (!m. A m ==> frag_exec ctx sm sb (\s. s = m)
    (\t. B m t /\ obs t = obs m) (\r. F)) ==>
  frag_exec ctx sa sb P (\t. (?m. A m /\ B m t) /\ obs t = saved) (\r. F)
Proof
  strip_tac >> drule frag_exec_then >> disch_then irule >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!m. A m ==> _` drule >>
  strip_tac >> irule frag_exec_weaken >>
  first_assum (irule_at Any) >> simp[] >>
  metis_tac[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag frag_exec_observation_then)
  in
    if null axioms andalso null (Thm.hyp frag_exec_observation_then) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Observation composition has unproved dependencies"
  end;
