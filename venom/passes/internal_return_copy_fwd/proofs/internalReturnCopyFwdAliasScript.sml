(* Allocation identity for available ircf aliases. *)
Theory internalReturnCopyFwdAlias
Ancestors
  internalReturnCopyFwdPlan ptrDiscipline venomWfProps venomInst list finite_map words
  venomExecSemantics venomState o1LowerDloadPairedAllocation
  venomMemProps basePtrProofs o1FrameLockstep

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
