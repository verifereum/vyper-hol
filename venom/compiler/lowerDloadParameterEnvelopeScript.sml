Theory lowerDloadParameterEnvelope
Ancestors
  lowerDloadCoverageInvariant lowerDloadParamProducer lowerDloadSharedState o1PassContract
  venomExecSemantics venomInst venomState ptrDiscipline list

Theorem ld_param_envelope_backward:
  MEM i (fn_insts fn) /\
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\
  i.inst_outputs = [out] /\
  ld_frame_data V U E L H AP BP AG BH tn un s t /\
  step_inst fuel CT i t = OK t' /\
  ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
      entry_fn_no_params fn) \/
   (LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
    LENGTH s.vs_params = LENGTH t.vs_params /\
    (!q. q < LENGTH s.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s.vs_params) (EL q t.vs_params)))) ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    s' = update_var out (EL (w2n idx) s.vs_params) s /\
    t' = update_var out (EL (w2n idx) t.vs_params) t /\
    ld_frame_data V U E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
        entry_fn_no_params fn) \/
     (LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
      LENGTH s'.vs_params = LENGTH t'.vs_params /\
      (!q. q < LENGTH s'.vs_params ==>
        ld_owned_value E (EL q AP) (EL q BP) {} {}
          (EL q s'.vs_params) (EL q t'.vs_params))))
Proof
  strip_tac
  >- (gvs[entry_fn_no_params_def, EVERY_MEM] >>
      metis_tac[is_param_opcode_def]) >>
  qpat_x_assum `ld_frame_data _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ld_frame_data_def] >> strip_tac >>
  drule_all ld_param_backward >>
  disch_then (qspecl_then [`L`, `H`, `CS`] strip_assume_tac) >>
  qexists_tac `s'` >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (irule ld_param_selection >> simp[] >> metis_tac[]) >>
  gvs[] >>
  simp[ld_frame_data_def, ld_frame_embedding_update_var] >>
  conj_tac
  >- (fs[ld_shared_state_def] >>
      simp[ld_shared_state_def, ld_param_taint_nonvar, update_var_def]) >>
  disj2_tac >> simp[update_var_def]
QED
