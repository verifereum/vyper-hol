Theory concretizePtrAllocationTransport
Ancestors concretizePtrValueTransport concretizePtrAffineTransport
  concretizePtrActivationChronology concretizePtrSourceOwnership concretizeStepStructure
  concretizeMemLocDefs ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words list pred_set

Theorem ptr_value_transport_birth_extension:
  (!owner site. FLOOKUP births owner = SOME site ==>
    FLOOKUP births' owner = SOME site) /\
  ptr_value_transport births positions tag mask x y ==>
  ptr_value_transport births' positions tag mask x y
Proof
  Cases_on `tag` >> simp[ptr_value_transport_def] >>
  PairCases_on `x'` >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_args_transport_birth_extension:
  (!owner site. FLOOKUP births owner = SOME site ==>
    FLOOKUP B owner = SOME site) /\
  ptr_args_transport births positions tags masks xs ys ==>
  ptr_args_transport B positions tags masks xs ys
Proof
  simp[ptr_args_transport_def, LIST_REL_EL_EQN] >> strip_tac >>
  gvs[] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `EL n (ZIP (tags,ZIP (masks,xs)))` >>
  Cases_on `r` >> simp[] >>
  metis_tac[ptr_value_transport_birth_extension]
QED

Theorem ptr_vars_transport_birth_extension:
  (!owner site. FLOOKUP births owner = SOME site ==>
    FLOOKUP births' owner = SOME site) /\
  ptr_vars_transport births positions TG tn s t ==>
  ptr_vars_transport births' positions TG tn s t
Proof
  simp[ptr_vars_transport_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `lookup_var v s` >> Cases_on `lookup_var v t` >>
  simp[ptr_lookup_transport_def] >>
  metis_tac[ptr_value_transport_birth_extension]
QED

(* Shared operational boundary for both unrestricted and opaque-safe transport. *)
Theorem ptr_alloca_source_success:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\
  (!base size. FLOOKUP s.vs_allocas inst.inst_id = SOME (base,size) ==>
    size = w2n sz) ==>
  ?s' base. step_inst fuel C inst s = OK s' /\
    FLOOKUP s'.vs_allocas inst.inst_id = SOME (base,w2n sz) /\
    s'.vs_vars = (update_var out (n2w base) s).vs_vars /\
    s'.vs_return_pc_token = s.vs_return_pc_token /\
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  asm_simp_tac bool_ss [step_inst_non_invoke] >>
  pure_once_rewrite_tac [step_inst_base_def] >>
  asm_rewrite_tac [opcode_case_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[exec_alloca_def] >>
      qexistsl_tac [`s.vs_alloca_next`] >> simp[update_var_def, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  qpat_x_assum `!base size. _` (mp_tac o Q.SPECL [`x0`,`x1`]) >>
  simp[] >> strip_tac >> simp[exec_alloca_def, update_var_def]
QED

Theorem ptr_alloca_transport:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\
  FLOOKUP layout (Allocation inst.inst_id) = SOME pos /\
  FLOOKUP positions (Allocation inst.inst_id) = SOME (pos,w2n sz) /\
  ptr_vars_transport births positions TG tn s t /\
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
      ptr_vars_transport births' positions (ptr_tagged_step token PT TG inst s')
        (step_taint inst s s' tn) s' t')
Proof
  strip_tac >>
  drule_all ptr_alloca_source_success >>
  disch_then (qspecl_then [`fuel`,`C`] strip_assume_tac) >>
  rename1 `FLOOKUP s'.vs_allocas inst.inst_id = SOME (addr,w2n sz)` >>
  qexistsl_tac [`s'`,`addr`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!base size. FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  `t' = update_var out (n2w pos) t` by
    (qpat_x_assum `step_inst fuel C' _ t = OK t'` mp_tac >>
     simp[concretize_inst_with_positions_def, passSharedDefsTheory.mk_assign_inst_def] >>
     simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac [step_inst_base_def] >>
     simp[eval_operand_def]) >>
  drule_all ptr_vars_transport_birth_extension >> strip_tac >>
  simp[ptr_tagged_step_def] >>
  `ptr_value_transport births' positions (SOME (token,inst.inst_id)) {}
      (n2w addr) (n2w pos)` by
    (pure_rewrite_tac [ptr_value_transport_def, optionTheory.option_case_def,
       pairTheory.pair_case_thm] >> BETA_TAC >>
     pure_rewrite_tac [pairTheory.pair_case_thm] >> BETA_TAC >>
     qexistsl_tac [`addr`,`w2n sz`,`pos`] >>
     asm_rewrite_tac [WORD_SUB_REFL, WORD_ADD_0]) >>
  `ptr_vars_transport births' positions
      (set_prov TG [out] (SOME (token,inst.inst_id)))
      (step_taint inst s s' tn)
      (update_var out (n2w addr) s) (update_var out (n2w pos) t)` by
    (irule ptr_vars_transport_update >>
     rpt (goal_assum (drule_at Any)) >>
     simp[step_taint_def, out_taint_def, eval_operand_def]) >>
  gvs[ptr_vars_transport_def, lookup_var_def]
QED
