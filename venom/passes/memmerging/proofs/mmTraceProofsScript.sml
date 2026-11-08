(* Reachability facts at the finite execution visits used by memmerging. *)
Theory mmTraceProofs
Ancestors
  dftGasFromListTraceDefs unitMemInv o1PassLift contextCodegenRelProps
  dftGasFromListReachBoundary venomInstProofs venomExecProofs
  venomExecSemantics contextCodegenRel venomInst list pair

Theorem mm_exec_block_entry:
  !s. reachability_closed Inv ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!i. active_inst fn i s ==> Inv ctx fn i s) /\
    exec_block fuel ctx bb s = OK out /\ ~out.vs_halted ==>
    fn_entry_inv Inv ctx fn out
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst s` by
    (irule lookup_instruction_active >> simp[]) >>
  `Inv ctx fn inst s` by metis_tac[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (strip_tac >> gvs[AllCaseEqs()] >> simp[fn_entry_inv_def] >>
      rpt strip_tac >> irule reachability_closed_block >> metis_tac[]) >>
  strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac)) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  metis_tac[reachability_closed_next]
QED

Theorem mm_trace_root_inv:
  (!p d fuel ctx fn inst s.
    reachability_closed Inv ctx ==>
    EVERY (\((q,e,id),f,i,t). q <> [])
      (trace_step p d fuel ctx fn inst s)) /\
  (!p d fuel ctx fn bb s.
    reachability_closed Inv ctx /\
    (p = [] ==> lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      (!i. active_inst fn i s ==> Inv ctx fn i s)) ==>
    EVERY (\((q,e,id),f,i,t).
      q = [] ==> p = [] /\ f = fn /\ Inv ctx fn i t)
      (trace_block p d fuel ctx fn bb s)) /\
  (!p d fuel ctx fn s.
    reachability_closed Inv ctx /\
    (p = [] ==> fn_entry_inv Inv ctx fn s) ==>
    EVERY (\((q,e,id),f,i,t).
      q = [] ==> p = [] /\ f = fn /\ Inv ctx fn i t)
      (trace_blocks p d fuel ctx fn s))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume mm_trace_root_inv[step]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once trace_defs] >>
  rpt (CASE_TAC >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!v nm ops fn args s''. _` (mp_tac o Q.SPEC `(q,r)`) >>
  simp[] >> disch_then drule >> disch_then drule >>
  disch_then drule >> simp[EVERY_MEM, FORALL_PROD]
QED

Resume mm_trace_root_inv[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  simp[Once trace_defs] >>
  simp[EVERY_APPEND] >>
  conj_tac >- (strip_tac >> gvs[] >>
    metis_tac[lookup_instruction_active]) >>
  conj_tac >- (
    gvs[] >>
    gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  gvs[] >> first_x_assum irule >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all step_preserves_control_flow >> strip_tac >> simp[] >>
  rpt strip_tac >> metis_tac[reachability_closed_next, lookup_instruction_active]
QED

Resume mm_trace_root_inv[blocks]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >>
  simp[Once trace_defs] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `p = [] ==> lookup_block sp.vs_current_bb fn.fn_blocks = SOME bb /\
    (!i. active_inst fn i (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      ==> Inv ctx fn i (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (strip_tac >> gvs[] >>
     drule eval_phis_preserves_current_bb >> strip_tac >> simp[] >>
     rpt strip_tac >> irule fn_entry_inv_active >>
     simp[enters_block_def] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> first_x_assum irule >> simp[]) >>
  Cases_on `exec_block n ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `exec_block _ _ _ _ = OK out` >>
  Cases_on `out.vs_halted` >> simp[] >>
  gvs[] >> first_x_assum irule >> simp[] >>
  strip_tac >> gvs[] >> irule mm_exec_block_entry >>
  simp[] >> qexistsl [`bb`, `n`,
    `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >> simp[]
QED

Finalise mm_trace_root_inv

Theorem mm_entry_trace_bound:
  reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn s /\
  fn_entry_state fn s /\
  (!i t. Inv ctx fn i t ==> static_mem_ok eom ctx fn i t) ==>
  EVERY (\((p,d,id),f,i,t).
    p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn s)
Proof
  strip_tac >>
  `trace_function fuel ctx fn s = trace_blocks [] 0 fuel ctx fn s` by
    (gvs[fn_entry_state_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venomStateTheory.venom_state_component_equality]) >>
  simp[] >>
  qspecl_then [`[]`, `0`, `fuel`, `ctx`, `fn`, `s`] mp_tac
    (cj 3 mm_trace_root_inv) >>
  simp[] >> simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED
