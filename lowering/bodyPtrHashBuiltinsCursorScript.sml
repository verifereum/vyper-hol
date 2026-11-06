(* Straight-line execution preserves the block cursor; shared hash boundary. *)
Theory bodyPtrHashBuiltinsCursor
Ancestors exprSimHash venomExecSemantics venomState venomInst
  venomInstProps list
  exprLoweringProps bodyPtrHashBuiltinsKeccakFixedRun

Theorem hash_run_inst_seq_current_bb:
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
    run_inst_seq_preserves_field)) >>
  qexists_tac `insts` >> asm_rewrite_tac [] >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem hash_fixed_keccak_emitted_length:
  compile_keccak256_bytesm x m sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 3
Proof
  strip_tac >> drule hash_fixed_keccak_emission >> simp[]
QED
