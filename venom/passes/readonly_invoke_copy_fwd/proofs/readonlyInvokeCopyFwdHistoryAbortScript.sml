(* Abort suffixes need operand availability, not relocated value equality. *)
Theory readonlyInvokeCopyFwdHistoryAbort
Ancestors
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdRel
  o1LowerDloadAvailableSuffix taintAgree venomInst venomState
  venomExecSemantics finite_map list pred_set

Theorem ricf_block_edit_unchanged_fetch:
  ricf_block_edit bb bb' /\ get_instruction bb i = SOME ii /\
  ii.inst_opcode <> MCOPY /\ ii.inst_opcode <> INVOKE ==>
  get_instruction bb' i = SOME ii
Proof
  strip_tac >> drule ricf_block_edit_EL >> strip_tac >>
  gvs[get_instruction_def] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[ricf_inst_edit_def] >> metis_tac[]
QED

Theorem ricf_history_assign_suffix_abort:
  ricf_block_edit bb bb' /\ ricf_frame_agree D X sites PG G tn s t /\
  s.vs_inst_idx = t.vs_inst_idx /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\
  (!k ii. k < d /\ get_instruction bb (s.vs_inst_idx + k) = SOME ii ==>
          ii.inst_opcode = ASSIGN) /\
  exec_block fuel C bb s = Abort reason u ==>
  ?v. exec_block fuel C' bb' t = Abort reason v
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels /\ FDOM s.vs_vars = FDOM t.vs_vars` by
    gvs[ricf_frame_agree_def, taint_agree_def, venom_state_component_equality] >>
  drule_at (Pat `exec_block _ _ _ _ = _`) ld_available_suffix_abort >>
  disch_then irule >> (conj_tac >- simp[]) >> qexistsl_tac [`UNIV`, `d`, `ri`] >>
  simp[] >> (conj_tac
    >- (gen_tac >> simp[FLOOKUP_DEF] >> IF_CASES_TAC >> simp[])) >>
  (conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >>
  rpt strip_tac >>
  Cases_on `k = d`
  >- (gvs[] >> sym_tac >> irule ricf_block_edit_unchanged_fetch >>
      simp[] >> qexists_tac `bb` >> simp[]) >>
  `k < d` by decide_tac >>
  Cases_on `get_instruction bb (s.vs_inst_idx + k)`
  >- (drule ricf_block_edit_EL >> gvs[get_instruction_def]) >>
  rename1 `get_instruction bb (s.vs_inst_idx + k) = SOME ii` >>
  `ii.inst_opcode = ASSIGN` by metis_tac[] >>
  gvs[] >> sym_tac >> irule ricf_block_edit_unchanged_fetch >>
  simp[] >> qexists_tac `bb` >> simp[]
QED
