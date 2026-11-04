(* Finite ordinary prefixes and the last instruction of block execution. *)
Theory simplifyCfgEndpoints
Ancestors
  simplifyCfgFragments venomExecSemantics venomExecProofs venomInst venomState list

Theorem scfg_exec_endpoint:
  !s. !k C bb r. exec_block k C bb s = r /\ (!e. r <> Error e) ==>
  ?u i z. scfg_iprefix C bb s u /\ get_instruction bb u.vs_inst_idx = SOME i /\
    step_inst k C i u = z /\
    ((z = r /\ (!v. z <> OK v)) \/
     ?v. z = OK v /\ is_terminator i.inst_opcode /\
       r = if v.vs_halted then Halt v else OK v)
Proof
  rpt gen_tac >> measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `step_inst k C i s` >> simp[]
  >- suspend "ok" >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`s`, `i`] >> simp[scfg_iprefix_rules] >>
  Cases_on `step_inst k C i s` >> gvs[]
QED

Resume scfg_exec_endpoint[ok]:
  rename1 `step_inst k C i s = OK next` >>
  Cases_on `is_terminator i.inst_opcode` >> simp[]
  >- (strip_tac >> qexistsl_tac [`s`, `i`] >> simp[scfg_iprefix_rules]) >>
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `next with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qx_choosel_then [`u`, `j`] strip_assume_tac) >>
  qexistsl_tac [`u`, `j`] >> simp[] >>
  irule scfg_iprefix_trans >> qexists_tac `next with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[] >> irule scfg_iprefix_single >> metis_tac[]
QED
Finalise scfg_exec_endpoint

Theorem scfg_exec_endpoint_reconstruct:
  scfg_iprefix C bb s u /\ get_instruction bb u.vs_inst_idx = SOME i /\
  step_inst k C i u = z /\ (!e. r <> Error e) /\
  ((z = r /\ (!v. z <> OK v)) \/
   ?v. z = OK v /\ is_terminator i.inst_opcode /\
     r = if v.vs_halted then Halt v else OK v) ==>
  ?m. exec_block m C bb s = r
Proof
  strip_tac >> irule scfg_iprefix_continue >>
  simp[] >> qexistsl_tac [`k`, `u`] >> simp[] >>
  Cases_on `z` >> gvs[] >> simp[Once exec_block_def] >>
  Cases_on `step_inst k C i u` >> gvs[]
QED
