(* Instruction counter and register bounds for a confined entry path. *)
Theory groupedRegistrationCounters
Ancestors
  fragGasPath fragExec loweringStateRelDefs
  venomExecSemantics venomExecProofs venomMemProofs venomInstProofs
  venomInst venomState finite_map list relation

Theorem grouped_registration_alloca_bound_step[local]:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode = ALLOCA ==> inst.inst_id < st.cs_next_id) /\
  (!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> id < st.cs_next_id) ==>
  !id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < st.cs_next_id
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def,
           AllCaseEqs(), LET_THM] >> rpt strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `id = inst.inst_id` >> gvs[] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_non_invoke, step_inst_base_preserves_allocas] >>
  asm_rewrite_tac[]
QED

Theorem grouped_registration_vars_bound_step[local]:
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode /\
  EVERY (not_fresh_at st) inst.inst_outputs /\ fresh_vars_wrt st s ==>
  fresh_vars_wrt st t
Proof
  strip_tac >> simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  `~MEM (STRING #"%" (toString n)) inst.inst_outputs` by
    (fs[EVERY_MEM, not_fresh_at_def] >> metis_tac[arithmeticTheory.GREATER_EQ]) >>
  drule_all step_preserves_non_output_vars >>
  strip_tac >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by
    fs[fresh_vars_wrt_def] >>
  qpat_x_assum `lookup_var _ t = lookup_var _ s` mp_tac >>
  asm_simp_tac (srw_ss()) [lookup_var_def, FLOOKUP_DEF]
QED

Theorem grouped_registration_jump_bound[local]:
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t ==>
  ?lbl. t = jump_to lbl s
Proof
  strip_tac >> drule_all step_inst_ok_terminator_jump >>
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(), LET_THM] >>
  metis_tac[]
QED

Theorem grouped_registration_bounds_edge[local]:
  gas_path_edge ctx fn s n (OK t) /\
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    !i. get_instruction bb s.vs_inst_idx = SOME i ==>
      i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
      EVERY (not_fresh_at st) i.inst_outputs) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\
  (!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> id < st.cs_next_id) ==>
  fresh_vars_wrt st t /\
  (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < st.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  gvs[exit_result_def]
  >- (`inst.inst_opcode <> INVOKE /\
       (inst.inst_opcode = ALLOCA ==> inst.inst_id < st.cs_next_id) /\
       EVERY (not_fresh_at st) inst.inst_outputs` by metis_tac[] >>
      conj_tac
      >- (drule_all grouped_registration_vars_bound_step >>
          simp[fresh_vars_wrt_def]) >>
      simp[] >> metis_tac[grouped_registration_alloca_bound_step])
  >- (drule_all grouped_registration_jump_bound >> strip_tac >>
      `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
      drule_then assume_tac eval_phis_no_phi >>
      gvs[jump_to_def, fresh_vars_wrt_def])
  >- fs[jump_to_def, fresh_vars_wrt_def] >>
  qpat_x_assum `OK t = step_inst fuel ctx inst s`
    (fn eq => fs[GSYM eq, exit_result_def])
QED

Theorem grouped_registration_bounds_rtc:
  !ctx fn st region s t.
    RTC (\u v. region u /\ ?k. gas_path_edge ctx fn u k (OK v)) s t /\
    (!u bb i. region u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME i ==>
      i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
      EVERY (not_fresh_at st) i.inst_outputs) /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    fresh_vars_wrt st s /\
    (!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> id < st.cs_next_id) ==>
    fresh_vars_wrt st t /\
    (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < st.cs_next_id)
Proof
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `fresh_vars_wrt st s` mp_tac >>
  qpat_x_assum `!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> _` mp_tac >>
  qpat_x_assum `RTC _ s t` mp_tac >>
  MAP_EVERY qid_spec_tac [`t`,`s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  `fresh_vars_wrt st s'' /\
    (!id pair. FLOOKUP s''.vs_allocas id = SOME pair ==> id < st.cs_next_id)` by
    (irule grouped_registration_bounds_edge >>
     qexistsl_tac [`ctx`,`fn`,`k`,`s`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem grouped_terminator_successor[local]:
  step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode /\
  ~t.vs_halted ==>
  t.vs_inst_idx = 0 /\ MEM t.vs_current_bb (get_successors inst)
Proof
  strip_tac >>
  drule_all grouped_registration_jump_bound >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> fs[is_terminator_def]) >>
  `MEM t.vs_current_bb (get_successors inst)` by
    metis_tac[step_inst_non_invoke, step_inst_base_term_succs] >>
  fs[jump_to_def]
QED

Theorem grouped_registration_edge_pc:
  gas_path_edge ctx fn s n (OK t) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb i.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    (if is_terminator i.inst_opcode then
       t.vs_inst_idx = 0 /\ MEM t.vs_current_bb (get_successors i)
     else t.vs_current_bb = s.vs_current_bb /\
          t.vs_inst_idx = SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  gvs[exit_result_def]
  >- metis_tac[step_preserves_control_flow]
  >- (drule_all grouped_terminator_successor >> strip_tac >>
      imp_res_tac eval_phis_preserves_current_bb >>
      metis_tac[])
  >- (`~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
      drule_all grouped_terminator_successor >> simp[jump_to_def]) >>
  qpat_x_assum `OK t = step_inst fuel ctx inst s`
    (fn eq => fs[GSYM eq, exit_result_def])
QED
