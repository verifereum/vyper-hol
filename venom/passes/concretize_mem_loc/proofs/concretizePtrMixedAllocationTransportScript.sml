Theory concretizePtrMixedAllocationTransport
Ancestors concretizePtrAllocationTransport concretizePtrOpaqueRetpc
  concretizePtrActivationChronology concretizePtrSourceOwnership concretizePtrValueTransport
  concretizeMemLocDefs ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words list pred_set

Theorem ptr_mixed_vars_birth_extension:
  (!owner site. FLOOKUP births owner = SOME site ==>
    FLOOKUP births' owner = SOME site) /\
  ptr_mixed_vars births positions TG tn f g s t ==>
  ptr_mixed_vars births' positions TG tn f g s t
Proof
  simp[ptr_mixed_vars_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  Cases_on `lookup_var x s` >> Cases_on `lookup_var x t` >>
  simp[ptr_lookup_transport_def] >>
  metis_tac[ptr_value_transport_birth_extension]
QED

Theorem ptr_mixed_alloca_transport:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  FLOOKUP layout (Allocation inst.inst_id) = SOME pos /\
  FLOOKUP positions (Allocation inst.inst_id) = SOME (pos,w2n sz) /\
  ptr_mixed_vars births positions TG tn f g s t /\
  (!base size. FLOOKUP s.vs_allocas inst.inst_id = SOME (base,size) ==>
    size = w2n sz) ==>
  ?s' base. step_inst fuel C inst s = OK s' /\
    FLOOKUP s'.vs_allocas inst.inst_id = SOME (base,w2n sz) /\
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_labels = s.vs_labels /\
    (!births' t'.
      (!owner site. FLOOKUP births owner = SOME site ==>
        FLOOKUP births' owner = SOME site) /\
      (!base size. FLOOKUP s'.vs_allocas inst.inst_id = SOME (base,size) ==>
        FLOOKUP births' (token,inst.inst_id) = SOME (base,size)) /\
      step_inst fuel C' (concretize_inst_with_positions layout inst) t = OK t' ==>
      ptr_mixed_vars births' positions (ptr_tagged_step token PT TG inst s')
        (step_taint inst s s' tn) f g s' t')
Proof
  strip_tac >> drule_all ptr_alloca_source_success >>
  disch_then (qspecl_then [`fuel`,`C`] strip_assume_tac) >>
  rename1 `FLOOKUP s'.vs_allocas inst.inst_id = SOME (addr,w2n sz)` >>
  qexistsl_tac [`s'`,`addr`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!base size. FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  `t' = update_var out (n2w pos) t` by
    (qpat_x_assum `step_inst fuel C' _ t = OK t'` mp_tac >>
     simp[concretize_inst_with_positions_def, passSharedDefsTheory.mk_assign_inst_def] >>
     simp[step_inst_non_invoke] >> pure_once_rewrite_tac [step_inst_base_def] >>
     simp[eval_operand_def]) >>
  drule_all ptr_mixed_vars_birth_extension >> strip_tac >>
  `ptr_value_transport births' positions (SOME (token,inst.inst_id)) {}
      (n2w addr) (n2w pos)` by
    (pure_rewrite_tac [ptr_value_transport_def, optionTheory.option_case_def,
       pairTheory.pair_case_thm] >> BETA_TAC >>
     pure_rewrite_tac [pairTheory.pair_case_thm] >> BETA_TAC >>
     qexistsl_tac [`addr`,`w2n sz`,`pos`] >>
     asm_rewrite_tac [WORD_SUB_REFL, WORD_ADD_0]) >>
  `ptr_mixed_vars births' positions (ptr_tagged_step token PT TG inst s')
    (step_taint inst s s' tn) f g
    (update_var out (n2w addr) s) (update_var out (n2w pos) t)` by
    (irule ptr_mixed_vars_update >>
     simp[ptr_tagged_step_def, step_taint_def, out_taint_def,
       eval_operand_def, set_prov_def, FLOOKUP_UPDATE] >>
     conj_tac
     >- (rpt strip_tac >>
         simp[op_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >>
         drule_all ptr_mixed_vars_lookup >> simp[op_taint_def]) >>
     conj_tac >- simp[op_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >>
     qexistsl_tac [`TG`,`tn`] >> simp[]) >>
  irule ptr_mixed_vars_fields >>
  goal_assum (drule_at Any) >> simp[update_var_def]
QED
