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

Theorem grouped_registration_scope_endpoint[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t scope prefix. r = OK t /\ scope s /\ prefix t /\
      (!u k v. gas_path_edge ctx fn u k (OK v) /\ scope u ==>
        scope v /\ (prefix v ==> prefix u)) ==> prefix s
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> rpt strip_tac
  >- fs[]
  >- metis_tac[] >>
  fs[exit_result_def]
QED

Theorem grouped_registration_bounds_path:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t st scope prefix. r = OK t /\ scope s /\ prefix t /\
    (!u k v. gas_path_edge ctx fn u k (OK v) /\ scope u ==>
      scope v /\ (prefix v ==> prefix u)) /\
    (!u k v bb i. scope u /\ prefix v /\
      gas_path_edge ctx fn u k (OK v) /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
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
  ho_match_mp_tac gas_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (gvs[] >> simp[])
  >~ [`exit_result r`] >- fs[exit_result_def] >>
  rename1 `gas_path_edge ctx fn s k (OK u)` >>
  `scope u` by metis_tac[] >>
  `prefix u` by
    (drule (Q.SPEC `ctx` grouped_registration_scope_endpoint) >>
     strip_tac >> qpat_assum `!t scope prefix. _`
       (qspecl_then [`t`,`scope`,`prefix`] (fn th =>
          SUBGOAL_THEN (#1 (dest_imp (concl th))) (ACCEPT_TAC o MATCH_MP th))) >>
     asm_rewrite_tac[]) >>
  `fresh_vars_wrt st u /\
   (!id pair. FLOOKUP u.vs_allocas id = SOME pair ==> id < st.cs_next_id)` by
    (irule grouped_registration_bounds_edge >> asm_rewrite_tac[] >>
     qexistsl_tac [`ctx`,`fn`,`k`,`s`] >> asm_rewrite_tac[] >>
     metis_tac[]) >>
  qpat_assum `!t st scope prefix. _`
    (qspecl_then [`t`,`st`,`scope`,`prefix`] (fn th =>
       SUBGOAL_THEN (#1 (dest_imp (concl th))) (ACCEPT_TAC o MATCH_MP th))) >>
  asm_rewrite_tac[]
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

Theorem grouped_registration_bounds_pc_path:
  gas_path ctx fn s n (OK t) /\ scope s.vs_current_bb s.vs_inst_idx /\
  prefix t.vs_current_bb t.vs_inst_idx /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\
  (!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> id < st.cs_next_id) /\
  (!label index bb i target next.
    scope label index /\ lookup_block label fn.fn_blocks = SOME bb /\
    get_instruction bb index = SOME i /\
    (if is_terminator i.inst_opcode then next = 0 /\ MEM target (get_successors i)
     else target = label /\ next = SUC index) ==>
    scope target next /\
    (prefix target next ==> prefix label index /\
      i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
      EVERY (not_fresh_at st) i.inst_outputs)) ==>
  fresh_vars_wrt st t /\
  (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < st.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule grouped_registration_bounds_path >>
  disch_then (qspecl_then [`t`,`st`,
    `\u:venom_state. scope u.vs_current_bb u.vs_inst_idx`,
    `\u:venom_state. prefix u.vs_current_bb u.vs_inst_idx`] mp_tac) >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (qx_genl_tac [`u`,`k`,`v`] >> strip_tac >>
          drule grouped_registration_edge_pc >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          qpat_assum `!label index bb i target next. _`
            (qspecl_then [`u.vs_current_bb`,`u.vs_inst_idx`,`bb`,`i`,
               `v.vs_current_bb`,`v.vs_inst_idx`] mp_tac) >>
          simp[]) >>
      conj_tac
      >~ [`!u k v bb i.
        scope u.vs_current_bb u.vs_inst_idx /\ prefix v.vs_current_bb v.vs_inst_idx /\
        gas_path_edge ctx fn u k (OK v) /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME i ==>
        i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
        EVERY (not_fresh_at st) i.inst_outputs`]
      >- (qx_genl_tac [`u`,`k`,`v`,`fetch_bb`,`fetch_inst`] >> strip_tac >>
          drule grouped_registration_edge_pc >>
          impl_tac >- metis_tac[] >> strip_tac >> gvs[] >>
          rename1 `lookup_block u.vs_current_bb fn.fn_blocks = SOME actual_bb` >>
          qpat_assum `!label index bb i target next. _`
            (qspecl_then [`u.vs_current_bb`,`u.vs_inst_idx`,`actual_bb`,`fetch_inst`,
               `v.vs_current_bb`,`v.vs_inst_idx`] mp_tac) >> simp[]) >>
      metis_tac[]) >>
  simp[]
QED
