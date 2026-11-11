Theory bodyPtrIntCallRunBlock
Ancestors ptrSafeRun venomExecSemantics venomInst list arithmetic

Theorem intcall_ghost_block_invariant:
  !I Q bb D lo fuel ctx fn PG s G tn.
  (!s G tn. I s G tn ==> Q G tn) /\
  (!s G tn inst t. I s G tn /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
    step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
    I (t with vs_inst_idx := SUC s.vs_inst_idx)
      (FST (ghost_step fuel ctx PG G tn inst s))
      (SND (ghost_step fuel ctx PG G tn inst s))) /\
  (!s G tn inst t. I s G tn /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
    step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode /\
    ~t.vs_halted /\
    ptr_safe_blocks D lo fuel ctx fn PG (entry_prov fn t G)
      (entry_taint_vars fn t tn) t ==>
    Q (FST (ghost_blocks fuel ctx fn PG (entry_prov fn t G)
      (entry_taint_vars fn t tn) t))
      (SND (ghost_blocks fuel ctx fn PG (entry_prov fn t G)
      (entry_taint_vars fn t tn) t))) /\
  I s G tn /\ ptr_safe_block D lo fuel ctx fn PG G tn bb s ==>
  Q (FST (ghost_block fuel ctx fn PG G tn bb s))
    (SND (ghost_block fuel ctx fn PG G tn bb s))
Proof
  ntac 10 gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (once_rewrite_tac[ghost_block_def] >> simp[] >> metis_tac[]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[] >> disch_tac >>
  once_rewrite_tac[ghost_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gnvs[]
  >- (rename1 `step_inst fuel ctx inst s = OK t` >>
      Cases_on `is_terminator inst.inst_opcode` >> gnvs[]
      >- (Cases_on `t.vs_halted` >> gvs[] >> metis_tac[]) >>
      gvs[] >>
      `s.vs_inst_idx < LENGTH bb.bb_instructions` by
        fs[get_instruction_def, AllCaseEqs()] >>
      qpat_x_assum `!y. LENGTH _ < _ /\ _ ==> _` irule >> simp[] >>
      metis_tac[]) >>
  metis_tac[]
QED
