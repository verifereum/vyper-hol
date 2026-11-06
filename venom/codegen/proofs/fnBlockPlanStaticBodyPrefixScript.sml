Theory fnBlockPlanStaticBodyPrefix
Ancestors
  fnBlockPlanStaticRegion fnPlanPrefix genBlockSim stackPlanGen asmIR
  venomInst venomWf livenessProofs livenessTransferProofs livenessDefs dfgDefs
  removeUnusedSsaProofs stackPlanTypes list rich_list arithmetic finite_map pred_set

Definition regional_body_lower_inv_def:
  regional_body_lower_inv lv dfg sb bb i ps <=>
    generated_plan_state_wf_marked sb ps /\
    (!v. MEM v (live_vars_at lv bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!j op v. i <= j /\ j < LENGTH bb.bb_instructions /\
      (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (EL j bb.bb_instructions).inst_outputs)
End

Theorem regional_compute_var_use[local]:
  MEM (Var v) (compute_operands inst) ==> MEM v (inst_uses inst)
Proof
  simp[compute_operands_def, LET_THM] >> rpt IF_CASES_TAC >>
  simp[get_non_label_operands_def, MEM_FILTER, inst_uses_def] >>
  rpt strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    (Cases_on `inst.inst_operands` >> gvs[] >> metis_tac[]) >>
  simp[passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Theorem regional_body_lower_inv_step:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb i ps /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) (cfg:cfg_analysis) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (SUC i) qs
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `wf_function fn /\ inst_wf inst /\ LENGTH (compute_operands inst) <= 16` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT inst.inst_outputs` by metis_tac[codegen_ready_inst_outputs_distinct] >>
  gvs[regional_body_lower_inv_def] >>
  `!op. MEM op (compute_operands (EL i bb.bb_instructions)) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt gen_tac >> strip_tac >> Cases_on `op` >> gvs[is_var_operand_def] >>
     rename1 `MEM (Var v) (compute_operands _)` >>
     `MEM v (inst_uses (EL i bb.bb_instructions))` by metis_tac[regional_compute_var_use] >>
     `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
       (drule live_vars_at_uses >> simp[LET_THM] >> disch_then irule >> metis_tac[]) >>
     metis_tac[]) >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    (EL i bb.bb_instructions).inst_outputs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_x_assum `!j op v. _` (qspecl_then [`i`, `Var v`, `v`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- (irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_body_marked_wf) >>
    goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_indexed_body_marked_live_coverage) >>
      goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
      qexists_tac `sb` >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_indexed_body_suffix_freshness) >>
  simp[] >> goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `op` >> simp[] >> metis_tac[]
QED

Theorem regional_body_lower_inv_prefix:
  !n a ps0 ops psn start fn bb sb cfg.
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  start <= a /\ a + n <= LENGTH bb.bb_instructions /\
  (!i. a <= i /\ i < a + n ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode) /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb a ps0 /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg:cfg_analysis) fn bb.bb_label (bb_is_halting bb) start
    (LENGTH bb.bb_instructions) (a-start) n (DROP a bb.bb_instructions) ps0 =
    SOME (ops,psn) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (a+n) psn
Proof
  Induct_on `n`
  >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `a < LENGTH bb.bb_instructions` by simp[] >>
  `DROP a bb.bb_instructions = EL a bb.bb_instructions :: DROP (SUC a) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[generate_block_insts_prefix_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  ` (if LENGTH bb.bb_instructions <= SUC a then
       live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label (a+1)) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC a)` by
    (IF_CASES_TAC
     >- (`LENGTH bb.bb_instructions = SUC a` by decide_tac >> simp[]) >> simp[ADD1]) >>
  gvs[] >>
  `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (SUC a) ps'` by
    (irule regional_body_lower_inv_step >> simp[] >>
     goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[LESS_EQ_REFL, LESS_EQ_LESS_TRANS]) >>
  `a + SUC n = SUC a + n` by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> gvs[ADD1] >>
  goal_assum (drule_at (Pat `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]
QED
