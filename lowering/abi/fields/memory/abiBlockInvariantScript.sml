(* TOP-LEVEL: lift a successful-instruction invariant to native block
   execution. The continuation uses the real instruction index update;
   internal calls are handled by the supplied native-step property. *)
Theory abiBlockInvariant
Ancestors venomExecSemantics venomState venomInst list arithmetic

Theorem exec_block_invariant_aux:
  !P fuel ctx bb.
    (!state inst next.
      get_instruction bb state.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst state = OK next /\ P state ==>
      P next /\ P (next with vs_inst_idx := SUC state.vs_inst_idx)) ==>
    !n ss out.
      n = LENGTH bb.bb_instructions - ss.vs_inst_idx /\
      exec_block fuel ctx bb ss = OK out /\ P ss ==> P out
Proof
  rpt gen_tac >> DISCH_TAC >> completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` (mp_tac o ONCE_REWRITE_RULE [exec_block_def]) >>
  Cases_on `get_instruction bb ss.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb ss.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst ss` >> simp[] >>
  rename1 `step_inst fuel ctx inst ss = OK next` >>
  qpat_x_assum `!state inst next. _` (qspecl_then [`ss`, `inst`, `next`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `next.vs_halted` >> simp[] >> DISCH_TAC >> gvs[]) >>
  simp[] >> DISCH_TAC >>
  `ss.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  `LENGTH bb.bb_instructions - SUC ss.vs_inst_idx < n` by decide_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC ss.vs_inst_idx` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`next with vs_inst_idx := SUC ss.vs_inst_idx`, `out`] mp_tac) >>
  simp[]
QED

Theorem exec_block_invariant:
  !P fuel ctx bb ss out.
    (!state inst next.
      get_instruction bb state.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst state = OK next /\ P state ==>
      P next /\ P (next with vs_inst_idx := SUC state.vs_inst_idx)) /\
    exec_block fuel ctx bb ss = OK out /\ P ss ==> P out
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`P`, `fuel`, `ctx`, `bb`] exec_block_invariant_aux) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`LENGTH bb.bb_instructions - ss.vs_inst_idx`, `ss`, `out`] mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native block invariant lifting: " ^ name)
  end) (DB.thms "abiBlockInvariant")
