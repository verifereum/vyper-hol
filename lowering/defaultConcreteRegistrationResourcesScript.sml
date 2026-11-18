(* Endpoint-map transport for concrete registration resources. *)
Theory defaultConcreteRegistrationResources
Ancestors defaultConcreteRegistrationDefs abiAllocationHistory
  ctorDeployLoweringEntryRoom loweringStateRelDefs
  finite_map pred_set words arithmetic exprLoweringProps list

Theorem default_registration_abi_history_transport:
  abi_alloca_history code s /\
  (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==>
    FLOOKUP s.vs_allocas id = SOME (p,n) \/
    ?inst w. MEM inst code /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit w] /\ n = w2n w) ==>
  abi_alloca_history code t
Proof
  simp[abi_alloca_history_def] >> metis_tac[]
QED

Theorem default_registration_entry_frame_transport:
  default_registration_entry_frame initial s /\
  t = s with <|vs_vars := vars; vs_memory := mem; vs_allocas := allocas;
    vs_alloca_next := next; vs_inst_idx := idx|> ==>
  default_registration_entry_frame initial t
Proof
  simp[default_registration_entry_frame_def] >> metis_tac[]
QED

Theorem default_registration_resources_transport:
  default_registration_resources ctx fn site k st s tn /\
  st.cs_next_var <= st1.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
  (!v. v IN FDOM t.vs_vars ==>
    v IN FDOM s.vs_vars \/ not_fresh_at st1 v) /\
  (!id r. FLOOKUP t.vs_allocas id = SOME r ==>
    FLOOKUP s.vs_allocas id = SOME r \/ id < st1.cs_next_id) /\
  (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==>
    FLOOKUP s.vs_allocas id = SOME (p,n) \/
    ?inst w. MEM inst (fn_insts fn) /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit w] /\ n = w2n w) /\
  alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
  alloca_history fn t /\ allocas_from 0 t /\
  ~ctx_has_dalloca ctx /\ lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
  u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  ~t.vs_halted /\ t.vs_current_bb = st1.cs_current_bb /\
  t.vs_inst_idx = LENGTH st1.cs_current_insts ==>
  default_registration_resources ctx fn site k st1 t u
Proof
  strip_tac >>
  `abi_alloca_history (fn_insts fn) t` by
    (irule default_registration_abi_history_transport >> qexists `s` >>
     fs[default_registration_resources_def]) >>
  `fresh_vars_wrt st1 t` by
    (fs[default_registration_resources_def, fresh_vars_wrt_def, not_fresh_at_def, GREATER_EQ] >>
     rpt strip_tac >>
     `st.cs_next_var <= n` by decide_tac >>
     qpat_x_assum `!v. v IN FDOM t.vs_vars ==> _` drule >>
     metis_tac[]) >>
  fs[default_registration_resources_def] >>
  `alloca_room ctx fn t` by
    (irule deploy_ctor_frontier_alloca_room >> qexistsl [`k`,`site`] >> simp[]) >>
  `fmp_room ctx fn t` by
    (drule venomInstTheory.lookup_function_MEM >>
     gvs[ptrDisciplineTheory.ctx_has_dalloca_def, fmp_room_def, EXISTS_MEM] >>
     metis_tac[]) >>
  simp[] >> conj_tac >- (rpt strip_tac >> first_x_assum drule >>
    strip_tac >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  gvs[SUBSET_DEF, EXTENSION]
QED
