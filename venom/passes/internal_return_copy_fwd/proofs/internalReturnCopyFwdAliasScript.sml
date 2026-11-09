(* Allocation identity for available ircf aliases. *)
Theory internalReturnCopyFwdAlias
Ancestors
  internalReturnCopyFwdPlan ptrDiscipline venomWfProps venomInst list finite_map words
  venomExecSemantics venomState o1LowerDloadPairedAllocation
  venomMemProps basePtrProofs o1FrameLockstep ssaAvailablePred venomExecProofs venomWf rangeAnalysisProofs contextCodegenRel
  tailMergeStep venomInstProofs1 ptrDisciplineControl venomInstProps relation
  singleUseExpansionSupplySim occurrenceOrigin unitShapeDefs o1LowerDloadOccurrence occurrenceGeometry
  allocaRemapProofs

Definition ircf_alias_value_def:
  ircf_alias_value fn s G v <=>
    !ai root sz. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      ircf_alias fn root v ==>
      ?w. lookup_var v s = SOME w /\ lookup_var root s = SOME w /\
        FLOOKUP s.vs_allocas ai.inst_id = SOME (w2n w,w2n sz) /\
        FLOOKUP G v = SOME (w2n w,w2n sz)
End

Definition ircf_size_coherent_def:
  ircf_size_coherent fn s <=>
    !ai root sz b z. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      FLOOKUP s.vs_allocas ai.inst_id = SOME (b,z) ==> z = w2n sz
End

Theorem ircf_size_coherent_empty:
  s.vs_allocas = FEMPTY ==> ircf_size_coherent fn s
Proof
  simp[ircf_size_coherent_def]
QED

Theorem ircf_alias_output_inv:
  ssa_form fn /\ MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\
  ircf_alias fn root v ==>
  inst = ai \/
  ?u. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
      MEM (Var u) inst.inst_operands /\ ircf_alias fn root u
Proof
  strip_tac >>
  qpat_x_assum `ircf_alias _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [ircf_alias_cases])
  >- (disj1_tac >> irule ssa_outputs_same_inst >>
      gvs[fn_insts_def] >> metis_tac[MEM]) >>
  `inst = inst'` by
    (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
  gvs[] >> metis_tac[]
QED

(* The natural-number site base need not be a representable word. *)
Theorem ircf_alloca_wrap_probe:
  inst.inst_outputs = [root] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  s.vs_alloca_next = dimword (:256) ==>
  ?t. exec_alloca inst s (1w:bytes32) = OK t /\
      lookup_var root t = SOME 0w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (dimword (:256),1) /\
      ~(?w:bytes32. FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,1))
Proof
  strip_tac >>
  simp[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> qspec_then `w:bytes32` mp_tac w2n_lt >> decide_tac
QED

(* Sites use natural bases; variables contain their word representations. *)
Definition ircf_alias_site_value_def:
  ircf_alias_site_value fn s G v <=>
    !ai root sz. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      ircf_alias fn root v ==>
      ?b. lookup_var v s = SOME (n2w b) /\
        lookup_var root s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas ai.inst_id = SOME (b,w2n sz) /\
        FLOOKUP G v = SOME (b,w2n sz)
End

Theorem ircf_alias_site_alloca:
  ssa_form fn /\ ircf_size_coherent fn s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_operands = [Lit amount] /\
  exec_alloca inst s amount = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) out
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `root = out` by
    (irule ircf_alloca_alias_root >>
     metis_tac[ircf_alloca_of_def]) >>
  `ai = inst` by
    (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
  gvs[] >> rename1 `MEM inst (fn_insts fn)` >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[update_var_def] >> strip_tac >> gvs[] >>
      simp[lookup_var_def, step_prov_def, set_prov_def,
           out_prov_def, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  `x1 = w2n amount` by metis_tac[ircf_size_coherent_def] >>
  simp[update_var_def] >> strip_tac >> gvs[] >>
  simp[lookup_var_def, step_prov_def,
       set_prov_def, out_prov_def, FLOOKUP_UPDATE]
QED

Theorem ircf_alias_site_assign:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Var src] /\
  ircf_alias_site_value fn s G src /\
  step_inst_base inst s = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) out
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `ircf_alias fn root src` by
    (metis_tac[ircf_alias_assign_inv, ircf_alloca_of_def]) >>
  `root <> out` by
    (strip_tac >>
     `ai = inst` by
       (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
     gvs[]) >>
  qpat_x_assum `ircf_alias_site_value _ _ _ _` mp_tac >>
  simp[ircf_alias_site_value_def] >>
  disch_then (qspecl_then [`ai`,`root`,`sz`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, eval_operand_def] >>
  strip_tac >> gvs[] >>
  gvs[update_var_def, lookup_var_def, step_prov_def, set_prov_def,
      out_prov_def, first_prov_def, op_prov_def, FLOOKUP_UPDATE]
QED

Theorem ircf_alias_site_nonalloca:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ALLOCA /\ ~MEM v inst.inst_outputs /\
  ircf_alias_site_value fn s G v /\ step_inst fuel C inst s = OK t /\
  t.vs_allocas = s.vs_allocas ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) v
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `~MEM root inst.inst_outputs` by
    (strip_tac >>
     `ai = inst` by
       (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
     gvs[]) >>
  `lookup_var v t = lookup_var v s` by
    metis_tac[basePtrProofsTheory.step_inst_preserves_lookup] >>
  `lookup_var root t = lookup_var root s` by
    metis_tac[basePtrProofsTheory.step_inst_preserves_lookup] >>
  `FLOOKUP (step_prov PG G inst t) v = FLOOKUP G v` by
    simp[step_prov_def, o1FrameLockstepTheory.FLOOKUP_set_prov] >>
  metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_size_coherent_allocas_eq:
  ircf_size_coherent fn s /\ t.vs_allocas = s.vs_allocas ==>
  ircf_size_coherent fn t
Proof
  strip_tac >> gvs[ircf_size_coherent_def] >> metis_tac[]
QED

Theorem ircf_alias_site_alloca_preserves:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  ~MEM v inst.inst_outputs /\ ircf_alias_site_value fn s G v /\
  exec_alloca inst s amount = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) v
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  qpat_x_assum `ircf_alias_site_value _ _ _ _` mp_tac >>
  simp[ircf_alias_site_value_def] >>
  disch_then (qspecl_then [`ai`,`root`,`sz`] mp_tac) >>
  simp[] >> strip_tac >>
  `root = out ==> ai = inst` by
    (strip_tac >> irule ssa_outputs_same_inst >>
     gvs[fn_insts_def] >> metis_tac[MEM]) >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[update_var_def] >> strip_tac >> gvs[] >>
      `inst.inst_id <> ai.inst_id` by (strip_tac >> gvs[]) >>
      `root <> out` by metis_tac[] >>
      qexists_tac `b` >>
      gvs[lookup_var_def, step_prov_def,
          o1FrameLockstepTheory.FLOOKUP_set_prov, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[] >>
  Cases_on `root = out` >> gvs[] >>
  gvs[lookup_var_def, step_prov_def,
      o1FrameLockstepTheory.FLOOKUP_set_prov, FLOOKUP_UPDATE]
QED

Theorem ircf_alias_site_nonalloca_step:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ALLOCA /\ ~MEM v inst.inst_outputs /\
  ircf_alias_site_value fn s G v /\ step_inst fuel C inst s = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) v
Proof
  strip_tac >> irule ircf_alias_site_nonalloca >>
  `t.vs_allocas = s.vs_allocas` by
    (simp[FLOOKUP_EXT, FUN_EQ_THM] >>
     metis_tac[basePtrProofsTheory.step_inst_alloca_flookup]) >>
  metis_tac[]
QED

Theorem ircf_size_coherent_alloca:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit amount] /\ ircf_size_coherent fn s /\
  exec_alloca inst s amount = OK t ==>
  ircf_size_coherent fn t
Proof
  strip_tac >>
  `!is. FLAT (MAP (\i:instruction. [i.inst_id]) is) =
        MAP (\i. i.inst_id) is` by (Induct >> simp[]) >>
  simp[ircf_size_coherent_def] >> rpt strip_tac >>
  Cases_on `ai.inst_id = inst.inst_id`
  >- (`ai = inst` by
        (irule (INST_TYPE [``:'a`` |-> ``:num``] all_distinct_flat_map_inj) >>
         qexistsl_tac [`\i. [i.inst_id]`, `fn_insts fn`, `ai.inst_id`] >>
         gvs[venomWfTheory.fn_inst_ids_distinct_def, fn_insts_def,
             fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
      gvs[] >> rename1 `MEM inst (fn_insts fn)` >>
      qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def] >>
      Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
      >- (simp[update_var_def] >> strip_tac >>
          gvs[FLOOKUP_UPDATE]) >>
      PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[] >>
      metis_tac[ircf_size_coherent_def]) >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[update_var_def] >> strip_tac >> gvs[FLOOKUP_UPDATE] >>
      metis_tac[ircf_size_coherent_def]) >>
  PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[] >>
  metis_tac[ircf_size_coherent_def]
QED

Theorem ircf_alias_site_output:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ venomWf$inst_wf inst /\
  ircf_size_coherent fn s /\ MEM v inst.inst_outputs /\
  (!u. MEM (Var u) inst.inst_operands ==> ircf_alias_site_value fn s G u) /\
  step_inst fuel C inst s = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) v
Proof
  strip_tac >> simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  drule_all ircf_alias_output_inv >> strip_tac
  >- (gvs[] >> rename1 `MEM inst (fn_insts fn)` >>
      `exec_alloca inst s sz = OK t` by
        gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def] >>
      `ircf_alias_site_value fn t (step_prov PG G inst t) root` by
        (irule ircf_alias_site_alloca >> metis_tac[]) >>
      metis_tac[ircf_alias_site_value_def]) >>
  `inst.inst_operands = [Var u]` by
    (gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_1] >> gvs[]) >>
  `step_inst_base inst s = OK t` by
    gvs[step_inst_non_invoke] >>
  `ircf_alias_site_value fn t (step_prov PG G inst t) v` by
    (irule ircf_alias_site_assign >> metis_tac[MEM]) >>
  metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_alias_site_preserves:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ venomWf$inst_wf inst /\
  ~MEM v inst.inst_outputs /\ ircf_alias_site_value fn s G v /\
  step_inst fuel C inst s = OK t ==>
  ircf_alias_site_value fn t (step_prov PG G inst t) v
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (`?out. inst.inst_outputs = [out]` by
        gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_1] >>
      `?amount:bytes32. exec_alloca inst s amount = OK t` by
        (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
         metis_tac[]) >>
      drule_all ircf_alias_site_alloca_preserves >> simp[]) >>
  irule ircf_alias_site_nonalloca_step >> metis_tac[]
QED

Theorem ircf_size_coherent_step:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  ircf_size_coherent fn s /\ step_inst fuel C inst s = OK t ==>
  ircf_size_coherent fn t
Proof
  strip_tac >>
  `!is. FLAT (MAP (\i:instruction. [i.inst_id]) is) =
        MAP (\i. i.inst_id) is` by (Induct >> simp[]) >>
  simp[ircf_size_coherent_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA /\ ai.inst_id = inst.inst_id`
  >- (gvs[] >>
      `ai = inst` by
        (irule (INST_TYPE [``:'a`` |-> ``:num``] all_distinct_flat_map_inj) >>
         qexistsl_tac [`\i. [i.inst_id]`, `fn_insts fn`, `ai.inst_id`] >>
         gvs[venomWfTheory.fn_inst_ids_distinct_def, fn_insts_def,
             fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
      gvs[] >> rename1 `MEM inst (fn_insts fn)` >>
      `exec_alloca inst s sz = OK t` by
        gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def] >>
      `ircf_size_coherent fn t` by
        (drule_all ircf_size_coherent_alloca >> simp[]) >>
      metis_tac[ircf_size_coherent_def]) >>
  `FLOOKUP t.vs_allocas ai.inst_id = FLOOKUP s.vs_allocas ai.inst_id` by
    (irule basePtrProofsTheory.step_inst_alloca_flookup >> metis_tac[]) >>
  metis_tac[ircf_size_coherent_def]
QED

Theorem ircf_alias_site_boundary_step:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  inst = EL n bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  boundary_pred fn bb n (ircf_alias_site_value fn s G) /\
  ircf_size_coherent fn s /\ step_inst fuel C inst s = OK t ==>
  boundary_pred fn bb (SUC n) (ircf_alias_site_value fn t (step_prov PG G inst t))
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[fn_insts_def] >> metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]) >>
  `venomWf$inst_wf inst` by metis_tac[fn_inst_wf_every_bb, EVERY_MEM, EL_MEM] >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `!u. MEM (Var u) inst.inst_operands ==> ircf_alias_site_value fn s G u` by
    metis_tac[boundary_pred_operand] >>
  `!v. MEM v inst.inst_outputs ==>
    ircf_alias_site_value fn t (step_prov PG G inst t) v` by
    metis_tac[ircf_alias_site_output] >>
  `!v. ircf_alias_site_value fn s G v ==>
    ircf_alias_site_value fn t (step_prov PG G inst t) v` by
    (rpt strip_tac >> Cases_on `MEM v inst.inst_outputs` >>
     metis_tac[ircf_alias_site_preserves]) >>
  simp[boundary_pred_def] >> conj_tac
  >- metis_tac[boundary_pred_def, dom_pred_mono] >>
  irule prefix_pred_suc >> metis_tac[boundary_pred_def, prefix_pred_mono]
QED

Theorem ircf_alias_other_output:
  ssa_form fn /\ MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> ASSIGN /\ MEM v inst.inst_outputs ==>
  ~ircf_alias fn root v
Proof
  metis_tac[ircf_alias_output_inv]
QED

Theorem ircf_alias_site_state_eq:
  s.vs_vars = t.vs_vars /\ s.vs_allocas = t.vs_allocas ==>
  (ircf_alias_site_value fn s G v <=> ircf_alias_site_value fn t G v)
Proof
  simp[ircf_alias_site_value_def, lookup_var_def]
QED

Theorem ircf_alias_site_phis_prov:
  !insts. ssa_form fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  ircf_alias_site_value fn s G v ==>
  ircf_alias_site_value fn s (phis_prov prev G insts) v
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `ircf_alias_site_value fn s (phis_prov prev G insts) v` by metis_tac[EVERY_DEF] >>
  simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `~MEM v h.inst_outputs` by
    (strip_tac >> drule_all ircf_alias_output_inv >> strip_tac >> gvs[]) >>
  simp[FLOOKUP_set_prov] >> metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_alias_site_eval_phis:
  ssa_form fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  ircf_alias_site_value fn s G v /\ eval_phis s insts = OK t ==>
  ircf_alias_site_value fn t (phis_prov s.vs_prev_bb G insts) v
Proof
  strip_tac >>
  `ircf_alias_site_value fn s (phis_prov s.vs_prev_bb G insts) v` by
    metis_tac[ircf_alias_site_phis_prov] >>
  `t.vs_allocas = s.vs_allocas` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `!pinst x. MEM pinst insts /\ pinst.inst_opcode = PHI /\
     (x = v \/ x = root) ==> ~MEM x pinst.inst_outputs` by
    (rpt strip_tac >> gvs[] >>
     `MEM pinst (fn_insts fn)` by gvs[EVERY_MEM] >>
     `ircf_alias fn root root` by simp[ircf_alias_refl] >>
     drule_all ircf_alias_output_inv >> strip_tac >> gvs[]) >>
  `lookup_var v t = lookup_var v s` by
    (drule eval_phis_lookup_cases >> disch_then (qspec_then `v` mp_tac) >>
     metis_tac[MEM]) >>
  `lookup_var root t = lookup_var root s` by
    (drule eval_phis_lookup_cases >> disch_then (qspec_then `root` mp_tac) >>
     metis_tac[MEM]) >>
  metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_alias_site_other_output:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> ASSIGN /\
  MEM v inst.inst_outputs ==> ircf_alias_site_value fn s G v
Proof
  simp[ircf_alias_site_value_def] >> metis_tac[ircf_alias_other_output]
QED

Theorem ircf_alias_site_phi_prefix:
  ssa_form fn /\ MEM bb fn.fn_blocks ==>
  prefix_pred bb (phi_prefix_length bb.bb_instructions) (ircf_alias_site_value fn s G)
Proof
  rw[prefix_pred_def] >>
  `(EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[rangeAnalysisProofsTheory.phi_prefix_length_el_phi] >>
  irule ircf_alias_site_other_output >> simp[] >>
  qexists_tac `EL j bb.bb_instructions` >> simp[] >>
  gvs[fn_insts_def] >> metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]
QED

Theorem ircf_alias_site_block_entry:
  ssa_form fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK t /\
  dom_pred fn bb.bb_label (ircf_alias_site_value fn s G) ==>
  boundary_pred fn bb (phi_prefix_length bb.bb_instructions)
    (ircf_alias_site_value fn (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (entry_prov fn s G))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
  simp[boundary_pred_def] >> reverse conj_tac
  >- metis_tac[ircf_alias_site_phi_prefix] >>
  irule dom_pred_mono >> qexists_tac `ircf_alias_site_value fn s G` >> simp[] >>
  rpt strip_tac >>
  `ircf_alias_site_value fn t (phis_prov s.vs_prev_bb G bb.bb_instructions) v` by
    metis_tac[ircf_alias_site_eval_phis] >>
  gvs[entry_prov_def] >>
  gvs[ircf_alias_site_value_def, lookup_var_def]
QED

Theorem ircf_alias_site_entry:
  ssa_form fn /\ fn_entry_label fn = SOME s.vs_current_bb /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  enters_block fn s t ==>
  boundary_pred fn bb t.vs_inst_idx (ircf_alias_site_value fn t G)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[enters_block_def] >>
  simp[boundary_pred_def] >> conj_tac
  >- (`bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
      metis_tac[dom_pred_entry]) >>
  metis_tac[ircf_alias_site_phi_prefix]
QED

Theorem ircf_alias_site_call_entry:
  ssa_form callee /\ setup_callee callee args s = SOME cs /\
  lookup_block cs.vs_current_bb callee.fn_blocks = SOME bb /\
  enters_block callee cs t ==>
  boundary_pred callee bb t.vs_inst_idx (ircf_alias_site_value callee t G)
Proof
  strip_tac >> irule ircf_alias_site_entry >> simp[] >>
  qexists_tac `cs` >> simp[] >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def]
QED

Theorem ircf_size_coherent_enters_block:
  ircf_size_coherent fn s /\ enters_block fn s t ==>
  ircf_size_coherent fn t
Proof
  rw[enters_block_def] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  gvs[ircf_size_coherent_def] >> metis_tac[]
QED

Theorem ircf_size_coherent_call_entry:
  setup_callee callee args s = SOME cs /\ enters_block callee cs t ==>
  ircf_size_coherent callee t
Proof
  strip_tac >> irule ircf_size_coherent_enters_block >>
  qexists_tac `cs` >> simp[] >> irule ircf_size_coherent_empty >>
  gvs[setup_callee_def]
QED

Theorem ircf_alias_site_bind_invoke:
  ssa_form fn /\ MEM callinst (fn_insts fn) /\ callinst.inst_opcode = INVOKE /\
  ircf_alias_site_value fn s G v /\
  bind_outputs callinst.inst_outputs vals s = SOME t ==>
  ircf_alias_site_value fn t (DRESTRICT G (COMPL (set callinst.inst_outputs))) v
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  simp[ircf_alias_site_value_def] >> rpt strip_tac >>
  `~MEM v callinst.inst_outputs /\ ~MEM root callinst.inst_outputs` by
    (conj_tac >> strip_tac >>
     `ircf_alias fn root root` by simp[ircf_alias_refl] >>
     drule_all ircf_alias_output_inv >> strip_tac >> gvs[]) >>
  `lookup_var v t = lookup_var v s` by
    metis_tac[tailMergeStepTheory.bind_outputs_lookup_outside] >>
  `lookup_var root t = lookup_var root s` by
    metis_tac[tailMergeStepTheory.bind_outputs_lookup_outside] >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_alias_site_return:
  ssa_form fn /\ MEM callinst (fn_insts fn) /\ callinst.inst_opcode = INVOKE /\
  ircf_alias_site_value fn s G v /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s e)) = SOME t ==>
  ircf_alias_site_value fn (t with vs_inst_idx := n)
    (DRESTRICT G (COMPL (set callinst.inst_outputs))) v
Proof
  strip_tac >>
  `ircf_alias_site_value fn (adopt_return_fmp ret (merge_callee_state s e)) G v` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def,
         ircf_alias_site_value_def, lookup_var_def] >> metis_tac[]) >>
  drule_all ircf_alias_site_bind_invoke >>
  simp[ircf_alias_site_value_def, lookup_var_def]
QED

Theorem ircf_size_coherent_return:
  ircf_size_coherent fn s /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s e)) = SOME t ==>
  ircf_size_coherent fn (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `t.vs_allocas = (adopt_return_fmp ret (merge_callee_state s e)).vs_allocas` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (Cases_on `ret.iret_adopt_fmp` >> gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  gvs[ircf_size_coherent_def] >> metis_tac[]
QED

Theorem ircf_alias_site_boundary_return:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  callinst = EL n bb.bb_instructions /\ callinst.inst_opcode = INVOKE /\
  boundary_pred fn bb n (ircf_alias_site_value fn s G) /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s e)) = SOME t ==>
  boundary_pred fn bb (SUC n)
    (ircf_alias_site_value fn (t with vs_inst_idx := SUC n)
      (DRESTRICT G (COMPL (set callinst.inst_outputs))))
Proof
  strip_tac >>
  `MEM callinst (fn_insts fn)` by
    (gvs[fn_insts_def] >> metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]) >>
  `!v. ircf_alias_site_value fn s G v ==>
     ircf_alias_site_value fn (t with vs_inst_idx := SUC n)
       (DRESTRICT G (COMPL (set callinst.inst_outputs))) v` by
    metis_tac[ircf_alias_site_return] >>
  simp[boundary_pred_def] >> conj_tac
  >- metis_tac[boundary_pred_def, dom_pred_mono] >>
  irule prefix_pred_suc >> reverse conj_tac
  >- metis_tac[boundary_pred_def, prefix_pred_mono] >>
  rpt strip_tac >> irule ircf_alias_site_other_output >> simp[] >>
  qexists_tac `callinst` >> simp[]
QED

Theorem ircf_alias_site_boundary_exit:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ bb_well_formed bb /\ n < LENGTH bb.bb_instructions /\
  callinst = EL n bb.bb_instructions /\ is_terminator callinst.inst_opcode /\
  fn_reachable fn bb.bb_label /\ fn_cfg_edge fn bb.bb_label lbl /\
  boundary_pred fn bb n (ircf_alias_site_value fn s G) /\
  ircf_size_coherent fn s /\ step_inst fuel C callinst s = OK t ==>
  dom_pred fn lbl (ircf_alias_site_value fn t (step_prov PG G callinst t))
Proof
  strip_tac >>
  `callinst.inst_opcode <> PHI` by
    (Cases_on `callinst.inst_opcode` >> gvs[is_terminator_def]) >>
  `boundary_pred fn bb (SUC n) (ircf_alias_site_value fn t (step_prov PG G callinst t))` by
    metis_tac[ircf_alias_site_boundary_step] >>
  irule boundary_pred_exit >> simp[] >>
  qexistsl_tac [`bb`, `n`] >> simp[] >>
  gvs[boundary_pred_def, prefix_pred_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> goal_assum drule >> simp[]
QED

Definition ircf_alias_boundary_def:
  ircf_alias_boundary fn s G <=>
    ircf_size_coherent fn s /\ fn_reachable fn s.vs_current_bb /\
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      boundary_pred fn bb s.vs_inst_idx (ircf_alias_site_value fn s G)
End

Definition ircf_alias_saved_def:
  ircf_alias_saved C f <=>
    MEM f.cf_fn C.ctx_functions /\ f.cf_inst.inst_opcode = INVOKE /\
    active_inst f.cf_fn f.cf_inst f.cf_state /\
    ircf_alias_boundary f.cf_fn f.cf_state f.cf_prov
End

Definition ircf_alias_frames_def:
  ircf_alias_frames C stk fn inst s G <=>
    MEM fn C.ctx_functions /\ active_inst fn inst s /\
    ircf_alias_boundary fn s G /\ EVERY (ircf_alias_saved C) stk
End

Theorem ircf_alias_frames_current:
  ircf_alias_frames C stk fn inst s G ==>
  MEM fn C.ctx_functions /\ active_inst fn inst s /\ ircf_alias_boundary fn s G
Proof
  simp[ircf_alias_frames_def]
QED

Theorem ircf_alias_frames_stack:
  ircf_alias_frames C stk fn inst s G ==> EVERY (ircf_alias_saved C) stk
Proof
  simp[ircf_alias_frames_def]
QED

Theorem ircf_alias_saved_cons:
  EVERY (ircf_alias_saved C) (f::stk) <=>
  ircf_alias_saved C f /\ EVERY (ircf_alias_saved C) stk
Proof
  simp[]
QED

Theorem ircf_alias_boundary_operand:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  ircf_alias_site_value fn s G v
Proof
  rw[ircf_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >> irule boundary_pred_operand >> metis_tac[lookup_block_MEM]
QED

Theorem ircf_alias_boundary_entry:
  ssa_form fn /\ s.vs_allocas = FEMPTY /\
  fn_entry_label fn = SOME s.vs_current_bb /\ enters_block fn s t ==>
  ircf_alias_boundary fn t G
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[enters_block_current_bb] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[enters_block_def] >>
  simp[ircf_alias_boundary_def] >> conj_tac
  >- metis_tac[ircf_size_coherent_empty, ircf_size_coherent_enters_block] >>
  conj_tac >- (simp[fn_reachable_def] >> metis_tac[RTC_REFL]) >>
  metis_tac[ircf_alias_site_entry]
QED

Theorem ircf_alias_boundary_call:
  ssa_form callee /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs t ==> ircf_alias_boundary callee t G
Proof
  strip_tac >> irule ircf_alias_boundary_entry >> simp[] >>
  qexists_tac `cs` >> simp[] >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def]
QED

Theorem ircf_alias_boundary_next:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK t ==>
  ircf_alias_boundary fn (t with vs_inst_idx := SUC s.vs_inst_idx)
    (step_prov PG G inst t)
Proof
  rw[ircf_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `ircf_size_coherent fn t` by
    (irule ircf_size_coherent_step >> conj_tac
     >- gvs[wf_function_def] >>
     qexistsl_tac [`C`, `fuel`, `EL s.vs_inst_idx bb.bb_instructions`, `s`] >>
     simp[] >> gvs[fn_insts_def] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]) >>
  simp[]
  >- (gvs[ircf_size_coherent_def] >> gvs[]) >>
  irule boundary_pred_mono >>
  qexists_tac `ircf_alias_site_value fn t
    (step_prov PG G (EL s.vs_inst_idx bb.bb_instructions) t)` >>
  simp[ircf_alias_site_value_def, lookup_var_def] >>
  irule ircf_alias_site_boundary_step >> metis_tac[lookup_block_MEM]
QED

Theorem ircf_alias_saved_return:
  ssa_form f.cf_fn /\ wf_function f.cf_fn /\ ircf_alias_saved C f /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state e)) = SOME t ==>
  ircf_alias_boundary f.cf_fn (t with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
Proof
  rw[ircf_alias_saved_def, ircf_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `t.vs_current_bb = f.cf_state.vs_current_bb` by
    metis_tac[bind_return_current_bb] >>
  simp[]
  >- metis_tac[ircf_size_coherent_return] >>
  irule ircf_alias_site_boundary_return >> simp[] >>
  goal_assum drule >> simp[]
QED

Theorem ircf_alias_boundary_block:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK t /\
  ~t.vs_halted /\ enters_block fn t u ==>
  ircf_alias_boundary fn u (entry_prov fn t G)
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst = EL s.vs_inst_idx bb.bb_instructions /\
    boundary_pred fn bb s.vs_inst_idx (ircf_alias_site_value fn s G)` by
    (gvs[ircf_alias_boundary_def, active_inst_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block]) >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    metis_tac[sue_terminator_cfg_edge] >>
  `fn_reachable fn t.vs_current_bb` by
    metis_tac[ircf_alias_boundary_def, fn_reachable_step] >>
  `inst_wf inst` by metis_tac[EVERY_EL] >>
  `step_prov PG G inst t = G` by metis_tac[step_prov_terminator] >>
  `ircf_size_coherent fn s /\ fn_reachable fn bb.bb_label /\
    fn_cfg_edge fn bb.bb_label t.vs_current_bb` by
    gvs[ircf_alias_boundary_def] >>
  `dom_pred fn t.vs_current_bb (ircf_alias_site_value fn t G)` by
    (drule_all ircf_alias_site_boundary_exit >> metis_tac[]) >>
  `ircf_size_coherent fn t` by
    (irule ircf_size_coherent_step >> conj_tac
     >- gvs[wf_function_def] >>
     qexistsl_tac [`C`, `fuel`, `inst`, `s`] >>
     gvs[ircf_alias_boundary_def, fn_insts_def] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]) >>
  `u.vs_current_bb = t.vs_current_bb` by metis_tac[enters_block_current_bb] >>
  simp[ircf_alias_boundary_def] >> conj_tac
  >- metis_tac[ircf_size_coherent_enters_block] >>
  gvs[enters_block_def] >>
  metis_tac[ircf_alias_site_block_entry, wf_ssa_def, lookup_block_label]
QED

Theorem ircf_alias_frames_reachable:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
    EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY ==>
    ircf_alias_frames C stk fn inst s G
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
      simp[ircf_alias_frames_def] >>
      irule ircf_alias_boundary_entry >> simp[] >>
      conj_tac >- metis_tac[EVERY_MEM, wf_ssa_def] >>
      qexists_tac `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
      simp[])
  >- (rpt strip_tac >>
      `ircf_alias_frames C stk fn inst s G` by metis_tac[] >>
      gvs[ircf_alias_frames_def] >>
      irule ircf_alias_boundary_next >> simp[] >>
      metis_tac[EVERY_MEM])
  >- (rpt strip_tac >>
      `ircf_alias_frames C stk fn inst s G` by metis_tac[] >>
      gvs[ircf_alias_frames_def] >>
      irule ircf_alias_boundary_block >> simp[] >>
      metis_tac[EVERY_MEM])
  >- (rpt strip_tac >>
      `ircf_alias_frames C stk fn inst s G` by metis_tac[] >>
      `MEM fn' C.ctx_functions` by metis_tac[lookup_function_MEM] >>
      gvs[ircf_alias_frames_def, ircf_alias_saved_def] >>
      irule ircf_alias_boundary_call >> simp[] >>
      metis_tac[EVERY_MEM, wf_ssa_def])
  >> rpt strip_tac >>
  `ircf_alias_frames C (f::stk) fn inst s G` by metis_tac[] >>
  `ircf_alias_saved C f` by metis_tac[ircf_alias_frames_stack, ircf_alias_saved_cons] >>
  gvs[ircf_alias_frames_def] >>
  `MEM f.cf_fn C.ctx_functions` by metis_tac[ircf_alias_saved_def] >>
  simp[] >> irule ircf_alias_saved_return >> simp[] >>
  metis_tac[EVERY_MEM, wf_ssa_def]
QED

Theorem ircf_alias_reachable_operand:
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  ircf_alias_site_value fn s G v
Proof
  strip_tac >> drule_all ircf_alias_frames_reachable >> strip_tac >>
  drule ircf_alias_frames_current >> strip_tac >>
  irule ircf_alias_boundary_operand >> metis_tac[EVERY_MEM]
QED

Theorem ircf_alias_reachable_saved_operand:
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  MEM f stk /\ MEM (Var v) f.cf_inst.inst_operands ==>
  ircf_alias_site_value f.cf_fn f.cf_state f.cf_prov v
Proof
  strip_tac >> drule_all ircf_alias_frames_reachable >> strip_tac >>
  drule ircf_alias_frames_stack >> strip_tac >>
  `ircf_alias_saved C f` by metis_tac[EVERY_MEM] >>
  gvs[ircf_alias_saved_def] >>
  `wf_ssa f.cf_fn /\ wf_function f.cf_fn /\ fn_inst_wf f.cf_fn` by
    metis_tac[EVERY_MEM] >>
  irule ircf_alias_boundary_operand >> simp[] >>
  qexists_tac `f.cf_inst` >> simp[]
QED

Theorem ircf_alias_boundary_earlier_operand:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  j <= s.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL j bb.bb_instructions).inst_operands ==>
  ircf_alias_site_value fn s G v
Proof
  rw[ircf_alias_boundary_def] >>
  irule boundary_pred_operand >> simp[] >>
  qexistsl_tac [`bb`, `fn`, `j`] >> simp[] >>
  gvs[] >> conj_tac >- metis_tac[lookup_block_MEM] >>
  irule boundary_pred_index_le >> goal_assum drule >> simp[]
QED

Theorem ircf_alias_reachable_earlier_operand:
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  j <= s.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL j bb.bb_instructions).inst_operands ==>
  ircf_alias_site_value fn s G v
Proof
  strip_tac >> drule_all ircf_alias_frames_reachable >> strip_tac >>
  drule ircf_alias_frames_current >> strip_tac >>
  irule ircf_alias_boundary_earlier_operand >> metis_tac[EVERY_MEM]
QED

Theorem ircf_alias_site_value_elim:
  ircf_alias_site_value fn s G v /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  ircf_alias fn root v ==>
  ?b. lookup_var v s = SOME (n2w b) /\
    lookup_var root s = SOME (n2w b) /\
    FLOOKUP s.vs_allocas ai.inst_id = SOME (b,w2n sz) /\
    FLOOKUP G v = SOME (b,w2n sz)
Proof
  metis_tac[ircf_alias_site_value_def]
QED

Theorem ircf_fwd_operand_sites:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = k /\ ircf_fwd_ok fn bb k d r sz ==>
  ?dv rv dai rai db rb.
    (EL k bb.bb_instructions).inst_operands = [Var dv; Var rv; Lit sz] /\
    MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\
    dai.inst_outputs = [d] /\ dai.inst_operands = [Lit sz] /\
    MEM rai (fn_insts fn) /\ rai.inst_opcode = ALLOCA /\
    rai.inst_outputs = [r] /\ rai.inst_operands = [Lit sz] /\
    lookup_var dv s = SOME (n2w db) /\ lookup_var d s = SOME (n2w db) /\
    lookup_var rv s = SOME (n2w rb) /\ lookup_var r s = SOME (n2w rb) /\
    FLOOKUP s.vs_allocas dai.inst_id = SOME (db,w2n sz) /\
    FLOOKUP s.vs_allocas rai.inst_id = SOME (rb,w2n sz) /\
    FLOOKUP G dv = SOME (db,w2n sz) /\ FLOOKUP G rv = SOME (rb,w2n sz)
Proof
  strip_tac >>
  `?dv rv. (EL k bb.bb_instructions).inst_operands = [Var dv; Var rv; Lit sz] /\
    ircf_alias fn d dv /\ ircf_alias fn r rv` by metis_tac[ircf_fwd_ok_def] >>
  `active_inst fn (EL k bb.bb_instructions) s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     metis_tac[lookup_block_MEM, lookup_block_label, ircf_fwd_ok_def]) >>
  `ircf_alias_site_value fn s G dv /\ ircf_alias_site_value fn s G rv` by
    (conj_tac >> irule ircf_alias_boundary_operand >> simp[] >>
     qexists_tac `EL k bb.bb_instructions` >> simp[] >>
     gvs[ircf_fwd_ok_def]) >>
  gvs[ircf_fwd_ok_def, ircf_alloca_of_def] >>
  drule_all ircf_alias_site_value_elim >> strip_tac >>
  drule_all ircf_alias_site_value_elim >> strip_tac >>
  metis_tac[ircf_alias_site_value_elim]
QED

Theorem ircf_fwd_access_ranges:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = k /\ ircf_fwd_ok fn bb k d r sz /\
  access_ok lo G fn (EL k bb.bb_instructions) s /\
  ~in_revert_forward fn s /\ w2n sz <> 0 ==>
  ?db rb.
    lookup_var d s = SOME (n2w db) /\ lookup_var r s = SOME (n2w rb) /\
    w2n (n2w db : bytes32) = db /\ w2n (n2w rb : bytes32) = rb /\
    source_memory_read_ranges (EL k bb.bb_instructions) s = [(rb,w2n sz)] /\
    source_memory_write_ranges (EL k bb.bb_instructions) s = [(db,w2n sz)]
Proof
  strip_tac >> drule_all ircf_fwd_operand_sites >> strip_tac >>
  `eval_operand (Var dv) s = SOME (n2w db) /\
   eval_operand (Var rv) s = SOME (n2w rb)` by simp[eval_operand_def] >>
  `eval_operand (Lit sz) s = SOME sz` by simp[eval_operand_def] >>
  `(EL k bb.bb_instructions).inst_opcode = MCOPY` by metis_tac[ircf_fwd_ok_def] >>
  `w2n (n2w db : bytes32) = db /\ w2n (n2w rb : bytes32) = rb` by
    (drule_all access_ok_mcopy_site_bases >> simp[]) >>
  qexistsl_tac [`db`, `rb`] >>
  simp[source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def]
QED

(* A nonempty read through an alias is at the natural allocation base. *)
Theorem ircf_alias_read_site:
  ircf_alias_site_value fn s G v /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  ircf_alias fn root v /\ lookup_var v s = SOME w /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (w2n w,len) (source_memory_read_ranges inst s) /\ len <> 0 ==>
  lookup_var root s = SOME w /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (w2n w,w2n sz) /\
  FLOOKUP G v = SOME (w2n w,w2n sz) /\ len <= w2n sz
Proof
  strip_tac >> drule_all ircf_alias_site_value_elim >> strip_tac >> gvs[] >>
  drule_all access_ok_read_site_bounds >> strip_tac >>
  `w2n (n2w b : bytes32) = b` by
    simp[wordsTheory.word_n2w_le2, arithmeticTheory.LESS_EQUAL_ANTISYM] >>
  gvs[]
QED

Theorem ircf_fwd_source_root_later:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  k <= s.vs_inst_idx /\ ircf_fwd_ok fn bb k d r sz ==>
  ?rai rb. MEM rai (fn_insts fn) /\ rai.inst_opcode = ALLOCA /\
    rai.inst_outputs = [r] /\ rai.inst_operands = [Lit sz] /\
    lookup_var r s = SOME (n2w rb) /\
    FLOOKUP s.vs_allocas rai.inst_id = SOME (rb,w2n sz)
Proof
  strip_tac >>
  `?dv rv. (EL k bb.bb_instructions).inst_operands = [Var dv; Var rv; Lit sz] /\
    ircf_alias fn r rv` by metis_tac[ircf_fwd_ok_def] >>
  `ircf_alias_site_value fn s G rv` by
    (irule ircf_alias_boundary_earlier_operand >> simp[] >>
     qexists_tac `k` >> gvs[ircf_fwd_ok_def]) >>
  `ircf_alloca_of fn r sz` by metis_tac[ircf_fwd_ok_def] >>
  gvs[ircf_alloca_of_def] >>
  drule_all ircf_alias_site_value_elim >> strip_tac >>
  qexistsl_tac [`ai`, `b`] >> simp[]
QED

(* Zero-size forwards need no representability or revert qualification. *)
Theorem ircf_fwd_zero_ranges:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = k /\ ircf_fwd_ok fn bb k d r sz /\ w2n sz = 0 ==>
  (!off len. MEM (off,len) (source_memory_read_ranges (EL k bb.bb_instructions) s) ==>
    len = 0) /\
  (!off len. MEM (off,len) (source_memory_write_ranges (EL k bb.bb_instructions) s) ==>
    len = 0)
Proof
  strip_tac >> drule_all ircf_fwd_operand_sites >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = MCOPY` by metis_tac[ircf_fwd_ok_def] >>
  simp[source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def, eval_operand_def]
QED

Theorem ircf_fwd_src_call_args_absent:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\ occurrence_syntax_origin fn a H /\
  k < i /\ i < LENGTH bb.bb_instructions /\
  call_inst = EL i bb.bb_instructions /\ call_inst.inst_opcode = INVOKE /\
  decode_invoke call_inst = SOME (nm,ops) /\
  MEM sai (fn_insts fn) /\ sai.inst_opcode = ALLOCA /\
  sai.inst_outputs = [sr] ==>
  ~MEM (SOME (a,sai.inst_id)) (MAP (op_prov H) ops)
Proof
  strip_tac >> strip_tac >>
  drule_all decode_invoke_prov_mem >> strip_tac >>
  `v IN pointer_derived_vars fn {sr}` by
    (drule_all occurrence_syntax_origin_planned_root >> simp[]) >>
  `ircf_alias fn sr v` by
    (drule_all ircf_fwd_src_pointer_closure >> simp[pred_setTheory.SUBSET_DEF]) >>
  drule_all ircf_fwd_later_invoke_not_src_alias >> simp[]
QED

Theorem ircf_fwd_dst_call_args_absent:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  ircf_no_dst_write_alias fn /\ occurrence_syntax_origin fn a H /\
  k < i /\ i < LENGTH bb.bb_instructions /\
  call_inst = EL i bb.bb_instructions /\ call_inst.inst_opcode = INVOKE /\
  decode_invoke call_inst = SOME (nm,ops) /\
  MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\
  dai.inst_outputs = [d] ==>
  ~MEM (SOME (a,dai.inst_id)) (MAP (op_prov H) ops)
Proof
  strip_tac >> strip_tac >>
  drule_all decode_invoke_prov_mem >> strip_tac >>
  `v IN pointer_derived_vars fn {d}` by
    (drule_all occurrence_syntax_origin_planned_root >> simp[]) >>
  `ircf_alias fn d v` by
    (drule_all ircf_fwd_dst_pointer_closure >> simp[pred_setTheory.SUBSET_DEF]) >>
  drule_all ircf_fwd_later_invoke_not_dst_alias >> simp[]
QED

Theorem ircf_fwd_revert_use_later:
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d r sz /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = REVERT /\
  MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
  ircf_alias fn d v ==> k < i
Proof
  strip_tac >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn) /\
   MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (conj_tac >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists_tac `bb` >> simp[] >> metis_tac[EL_MEM, ircf_fwd_ok_def]) >>
  `(EL i bb.bb_instructions).inst_id <> (EL k bb.bb_instructions).inst_id` by
    (strip_tac >>
     `EL i bb.bb_instructions = EL k bb.bb_instructions` by
       metis_tac[fn_inst_ids_distinct_inj] >>
     gvs[ircf_fwd_ok_def]) >>
  qpat_x_assum `ircf_fwd_ok _ _ _ _ _ _` mp_tac >>
  simp[ircf_fwd_ok_def] >> strip_tac >>
  `?j. k < j /\ j < LENGTH bb.bb_instructions /\
       EL j bb.bb_instructions = EL i bb.bb_instructions` by
    (qpat_x_assum `!inst v. _ /\ _ /\ _ /\ _ /\ _ ==> _`
       (qspecl_then [`EL i bb.bb_instructions`, `v`] mp_tac) >> simp[]) >>
  `j = i` by metis_tac[inst_ids_el_eq] >> gvs[]
QED

Theorem ircf_redirect_plan_cases:
  ircf_block_plan fn bb bb2 ==>
  ircf_redirect fn bb bb2 v = v \/
  ?k d r sz. ircf_redirect fn bb bb2 v = r /\
    ircf_fwd_ok fn bb k d r sz /\ ircf_alias fn d v
Proof
  strip_tac >> simp[ircf_redirect_def] >> IF_CASES_TAC
  >- (disj2_tac >> SELECT_ELIM_TAC >> conj_tac
      >- metis_tac[] >>
      rpt strip_tac >> gvs[ircf_block_plan_def] >>
      metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  simp[]
QED

Theorem ircf_redirect_revert_operand_available:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ircf_block_plan fn bb bb2 /\
  i = s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = REVERT /\
  MEM op (EL i bb.bb_instructions).inst_operands /\
  IS_SOME (eval_operand op s) ==>
  IS_SOME (eval_operand (ircf_redirect_op fn bb bb2 op) s)
Proof
  strip_tac >> Cases_on `op` >> simp[ircf_redirect_op_def] >>
  rename1 `MEM (Var v) _` >>
  drule ircf_redirect_plan_cases >>
  disch_then (qspec_then `v` strip_assume_tac)
  >- gvs[eval_operand_def] >>
  `fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks` by
    metis_tac[wf_function_def, lookup_block_MEM] >>
  `k < i` by metis_tac[ircf_fwd_revert_use_later] >>
  `k <= s.vs_inst_idx` by simp[] >>
  drule_all ircf_fwd_source_root_later >> strip_tac >>
  gvs[eval_operand_def]
QED

Theorem ircf_redirect_reachable_revert_operand:
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ircf_block_plan fn bb bb2 /\
  i = s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = REVERT /\
  MEM op (EL i bb.bb_instructions).inst_operands /\
  IS_SOME (eval_operand op s) ==>
  IS_SOME (eval_operand (ircf_redirect_op fn bb bb2 op) s)
Proof
  strip_tac >> drule_all ircf_alias_frames_reachable >> strip_tac >>
  drule ircf_alias_frames_current >> strip_tac >>
  irule ircf_redirect_revert_operand_available >>
  metis_tac[EVERY_MEM]
QED

Theorem ircf_saved_forward_suffix_absent:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C ==>
    !j bb k d sr sz ai root.
      j < LENGTH stk /\
      lookup_block (EL j stk).cf_state.vs_current_bb
        (EL j stk).cf_fn.fn_blocks = SOME bb /\
      wf_function (EL j stk).cf_fn /\ fn_inst_wf (EL j stk).cf_fn /\
      fn_inst_ids_distinct (EL j stk).cf_fn /\
      ircf_no_dst_write_alias (EL j stk).cf_fn /\
      ircf_fwd_ok (EL j stk).cf_fn bb k d sr sz /\
      ircf_copy_roots (EL j stk).cf_fn (EL k bb.bb_instructions) =
        SOME (d,sr,sz) /\
      k < (EL j stk).cf_state.vs_inst_idx /\
      MEM ai (fn_insts (EL j stk).cf_fn) /\
      ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] /\
      (root = d \/ root = sr) ==>
      occurrence_suffix_absent ((EL j U).of_owner,ai.inst_id) j H HP U
Proof
  ho_match_mp_tac occ_frame_reachable_strongind >> rpt conj_tac
  >- simp[]
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ircf_saved_forward_suffix_absent[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule occurrence_suffix_absent_next >>
  drule occ_frame_reachable_owner_fresh >> strip_tac >>
  drule occ_frame_reachable_stack_length >> strip_tac >>
  fs[ALL_DISTINCT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Resume ircf_saved_forward_suffix_absent[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule occurrence_suffix_absent_block >> first_x_assum irule >>
  simp[] >> metis_tac[]
QED

Resume ircf_saved_forward_suffix_absent[call]:
  rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
  Cases_on `j`
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      irule occurrence_suffix_absent_start >>
      drule occ_frame_reachable_origin_certificate >> simp[] >>
      strip_tac >> drule occurrence_origin_certificate_current >> strip_tac >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      fs[active_inst_def] >>
      `bb' = bb` by
        metis_tac[lookup_block_label, same_label_same_block] >> gvs[]
      >- (irule ircf_fwd_dst_call_args_absent >>
          simp[] >> metis_tac[]) >>
      irule ircf_fwd_src_call_args_absent >> simp[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  irule occurrence_suffix_absent_push >> first_x_assum irule >>
  simp[] >> metis_tac[]
QED

Resume ircf_saved_forward_suffix_absent[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ ==> !j. _` mp_tac >> simp[] >>
  disch_then (qspec_then `SUC j` mp_tac) >> simp[] >>
  metis_tac[occurrence_suffix_absent_pop]
QED

Finalise ircf_saved_forward_suffix_absent

Theorem ircf_saved_forward_sites_exclusion:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ j < LENGTH stk /\
  lookup_block (EL j stk).cf_state.vs_current_bb
    (EL j stk).cf_fn.fn_blocks = SOME bb /\
  wf_function (EL j stk).cf_fn /\ fn_inst_wf (EL j stk).cf_fn /\
  fn_inst_ids_distinct (EL j stk).cf_fn /\
  ircf_no_dst_write_alias (EL j stk).cf_fn /\
  ircf_fwd_ok (EL j stk).cf_fn bb k d sr sz /\
  ircf_copy_roots (EL j stk).cf_fn (EL k bb.bb_instructions) =
    SOME (d,sr,sz) /\
  k < (EL j stk).cf_state.vs_inst_idx /\
  MEM ai (fn_insts (EL j stk).cf_fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] /\
  (root = d \/ root = sr) /\
  FLOOKUP (EL j stk).cf_state.vs_allocas ai.inst_id = SOME (b,z) /\
  FLOOKUP G v = SOME (c,w) /\ 0 < z /\ 0 < w ==>
  b + z <= c \/ c + w <= b
Proof
  strip_tac >>
  `occurrence_suffix_absent ((EL j U).of_owner,ai.inst_id) j H HP U` by
    (drule ircf_saved_forward_suffix_absent >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule occurrence_suffix_absent_current >> strip_tac >>
  drule occ_frame_reachable_annotation >> simp[] >> strip_tac >>
  drule occ_frame_reachable_geometry >> simp[] >>
  disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
  `FLOOKUP B ((EL j U).of_owner,ai.inst_id) = SOME (b,z)` by
    (fs[occurrence_annotation_ok_def] >>
     metis_tac[occurrence_saved_ok_allocas]) >>
  fs[occurrence_annotation_ok_def] >>
  drule_all occurrence_env_site_exclusion >> simp[]
QED

Theorem ircf_saved_forward_write_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ j < LENGTH stk /\
  lookup_block (EL j stk).cf_state.vs_current_bb
    (EL j stk).cf_fn.fn_blocks = SOME bb /\
  wf_function (EL j stk).cf_fn /\ fn_inst_wf (EL j stk).cf_fn /\
  fn_inst_ids_distinct (EL j stk).cf_fn /\
  ircf_no_dst_write_alias (EL j stk).cf_fn /\
  ircf_fwd_ok (EL j stk).cf_fn bb k d sr sz /\
  ircf_copy_roots (EL j stk).cf_fn (EL k bb.bb_instructions) =
    SOME (d,sr,sz) /\
  k < (EL j stk).cf_state.vs_inst_idx /\
  MEM ai (fn_insts (EL j stk).cf_fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] /\
  (root = d \/ root = sr) /\
  FLOOKUP (EL j stk).cf_state.vs_allocas ai.inst_id = SOME (b,z) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ b <= i /\ i < b+z ==>
  ~(off <= i /\ i < off+len)
Proof
  strip_tac >> strip_tac >>
  `0 < z /\ len <> 0` by decide_tac >>
  drule_then strip_assume_tac occ_frame_reachable_annotation >> fs[] >>
  drule_then assume_tac occ_frame_reachable_geometry >> fs[] >>
  qpat_x_assum `!lo. _` (qspec_then `lo` assume_tac) >> fs[] >>
  `FLOOKUP B ((EL j U).of_owner,ai.inst_id) = SOME (b,z)` by
    (fs[occurrence_annotation_ok_def] >>
     metis_tac[occurrence_saved_ok_allocas]) >>
  `lo <= b` by metis_tac[occurrence_geometry_site_bounds] >>
  `lo < off+len` by decide_tac >>
  `?ops v c w. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
     FLOOKUP G v = SOME (c,w) /\ c <= off /\ off+len <= c+w` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `0 < w` by decide_tac >>
  `b+z <= c \/ c+w <= b` by
    (irule ircf_saved_forward_sites_exclusion >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem ircf_fwd_later_writer_occurrence_exclusion:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
  ircf_fwd_ok fn bb k d sr sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  ircf_no_dst_write_alias fn /\ k < i /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ occurrence_syntax_origin fn a H /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ (root = d \/ root = sr) ==>
  FLOOKUP H v <> SOME (a,ai.inst_id)
Proof
  strip_tac >> strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    (metis_tac[allocaRemapProofsTheory.mem_ops_ofst_is_operand]) >>
  `v IN pointer_derived_vars fn {root}` by
    (drule_all occurrence_syntax_origin_planned_root >> simp[]) >>
  Cases_on `root = d`
  >- (`ircf_alias fn d v` by
        (drule_all ircf_fwd_dst_pointer_closure >>
         fs[pred_setTheory.SUBSET_DEF]) >>
      drule_all ircf_fwd_later_writer_not_dst_alias >> simp[]) >>
  `root = sr` by metis_tac[] >>
  `ircf_alias fn sr v` by
    (drule_all ircf_fwd_src_pointer_closure >>
     gvs[pred_setTheory.SUBSET_DEF]) >>
  drule_all ircf_fwd_later_writer_not_src_alias >> simp[]
QED

Theorem ircf_current_forward_sites_exclusion:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_fwd_ok fn bb k d sr sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  k < s.vs_inst_idx /\ MEM ai (fn_insts fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] /\
  (root = d \/ root = sr) /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,z) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (c,w) /\ 0 < z /\ 0 < w ==>
  b+z <= c \/ c+w <= b
Proof
  strip_tac >>
  `active_inst fn inst s` by
    (qpat_assum `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[occ_frame_reachable_cases] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    (`MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     fs[active_inst_def] >>
     `bb' = bb` by
       metis_tac[lookup_block_label, same_label_same_block] >> gvs[]) >>
  `occurrence_syntax_origin fn a H` by
    (drule_then assume_tac occ_frame_reachable_origin_certificate >> fs[] >>
     metis_tac[occurrence_origin_certificate_current]) >>
  `FLOOKUP H v <> SOME (a,ai.inst_id)` by
    (irule ircf_fwd_later_writer_occurrence_exclusion >> metis_tac[]) >>
  drule_then strip_assume_tac occ_frame_reachable_annotation >> fs[] >>
  drule_then assume_tac occ_frame_reachable_geometry >> fs[] >>
  qpat_x_assum `!lo. _` (qspec_then `lo` assume_tac) >> fs[] >>
  `FLOOKUP B (a,ai.inst_id) = SOME (b,z)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  `?jd. FLOOKUP H v = SOME jd /\ FLOOKUP B jd = SOME (c,w)` by
    (fs[occurrence_annotation_ok_def, occurrence_env_ok_def] >>
     metis_tac[FLOOKUP_DEF]) >>
  metis_tac[occurrence_geometry_sites_disjoint]
QED

Theorem ircf_current_forward_write_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_fwd_ok fn bb k d sr sz /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  k < s.vs_inst_idx /\ MEM ai (fn_insts fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] /\
  (root = d \/ root = sr) /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,z) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ b <= i /\ i < b+z ==>
  ~(off <= i /\ i < off+len)
Proof
  strip_tac >> strip_tac >>
  `0 < z /\ len <> 0` by decide_tac >>
  drule_then strip_assume_tac occ_frame_reachable_annotation >> fs[] >>
  drule_then assume_tac occ_frame_reachable_geometry >> fs[] >>
  qpat_x_assum `!lo. _` (qspec_then `lo` assume_tac) >> fs[] >>
  `FLOOKUP B (a,ai.inst_id) = SOME (b,z)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  `lo <= b` by metis_tac[occurrence_geometry_site_bounds] >>
  `lo < off+len` by decide_tac >>
  `?ops v c w. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
     FLOOKUP G v = SOME (c,w) /\ c <= off /\ off+len <= c+w` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `0 < w` by decide_tac >>
  `b+z <= c \/ c+w <= b` by
    (irule ircf_current_forward_sites_exclusion >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem ircf_alloca_of_coherent_size:
  ssa_form fn /\ ircf_size_coherent fn s /\ ircf_alloca_of fn root amount /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,z) ==>
  z = w2n amount
Proof
  strip_tac >>
  `ai.inst_operands = [Lit amount]` by
    (fs[ircf_alloca_of_def] >>
     `ai = ai'` by
       (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
     gvs[]) >>
  metis_tac[ircf_size_coherent_def]
QED
