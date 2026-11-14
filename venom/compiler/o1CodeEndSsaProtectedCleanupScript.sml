Theory o1CodeEndSsaProtectedCleanup
Ancestors
  o1LabelFlowMiddleCleanupFlow o1LabelFlowMiddleTraversal
  o1LabelFlowMiddleInsertion o1LabelFlowMiddleSsa
  codegenSymRel o1LabelFlowMiddleCleanup makeSsaCurrentLockstepShape list
  o1MakeSsaVisitTrace makeSsaCurrentProps o1MakeSsaOwnership pred_set
  makeSsaCurrentNonDegShape makeSsaCurrentNonDegCleanup o1MakeSsaActualMaps
  o1MakeSsaRootedTree venomWf venomInst
  o1MakeSsaEventOwnership makeSsaCurrentTraceCertificate makeSsaCurrentLockstep
  makeSsaCurrentWfSsa makeSsaCurrentTreeTrace pair

Theorem renamed_protected_cleanup_owner[local]:
  visit_blocks path s rs f.fn_blocks sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q f.fn_blocks)) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  EVERY current_nondeg_block_shape f.fn_blocks /\
  current_name_owner V R u /\
  (!e. MEM e events ==>
    current_stack_owner V R (SND e.sve_in) /\
    current_stack_owner V R (SND e.sve_out) /\
    LIST_REL (\i j. LIST_REL (\v n. (n,v) IN R)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) /\
  (!bb i v. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions ==>
    (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs ==> v IN V)) /\
  (!x bb i. code_end_var f x /\ MEM bb f.fn_blocks /\
    MEM i bb.bb_instructions /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x) ==>
  (!enabled n. code_end_var
    (f with fn_blocks := simplify_current_phis_if enabled final) n ==>
    ?x. (n,x) IN R /\ code_end_var f x) /\
  (!enabled n i. code_end_var
    (f with fn_blocks := simplify_current_phis_if enabled final) n /\
    MEM i (fn_insts (f with fn_blocks := simplify_current_phis_if enabled final)) /\
    MEM (Var n) i.inst_operands ==> i.inst_opcode = CODECOPY)
Proof
  strip_tac >>
  `rename_current_blocks s rs f.fn_blocks sm tree = (ct,t,final)` by
    metis_tac[o1MakeSsaVisitTraceTheory.visit_erasure, pairTheory.FST] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) final)` by
    metis_tac[cj 1 makeSsaCurrentPropsTheory.rename_current_blocks_labels] >>
  `!j n x. MEM j (fn_insts (f with fn_blocks := final)) /\
    MEM (Var n) j.inst_operands /\ (n,x) IN R /\ code_end_var f x ==>
    j.inst_opcode = CODECOPY` by
    (rpt strip_tac >>
     `?q bb k. lookup_block q final = SOME bb /\
        k < LENGTH bb.bb_instructions /\ j = EL k bb.bb_instructions` by
       (mp_tac (Q.INST [`f` |-> `f with fn_blocks := final`] fn_insts_lookup_index) >>
        simp[] >> metis_tac[]) >>
     drule visit_blocks_protected_read >>
     disch_then (qspecl_then [`x`,`u`,`n`,`V`,`R`,`q`,`bb`,`j`] mp_tac) >>
     (impl_tac >- metis_tac[EL_MEM]) >> metis_tac[]) >>
  `!n. code_end_var (f with fn_blocks := final) n ==>
    ?x. (n,x) IN R /\ code_end_var f x` by
    (rpt strip_tac >> drule code_end_var_owned_bound >>
     disch_then (qspecl_then [`f`,`R`] mp_tac) >>
     (impl_tac >- (conj_tac >- (rpt strip_tac >>
        drule visit_blocks_owned_inst >>
        disch_then (qspecl_then [`u`,`V`,`R`] mp_tac) >>
        simp[] >> disch_then (qspec_then `j` mp_tac) >>
        (impl_tac >- metis_tac[]) >> strip_tac >>
        qexists `i` >> gvs[]) >> metis_tac[])) >> simp[]) >>
  `!i x. MEM i (fn_insts (f with fn_blocks := final)) /\
    i.inst_opcode = PHI /\ code_end_var (f with fn_blocks := final) x ==>
    ~MEM (Var x) i.inst_operands` by
    (rpt strip_tac >>
     qpat_x_assum `!n. code_end_var _ n ==> _` drule >> strip_tac >>
     `i.inst_opcode = CODECOPY` by metis_tac[] >> gvs[]) >>
  `!enabled n. code_end_var
    (f with fn_blocks := simplify_current_phis_if enabled final) n ==>
    code_end_var (f with fn_blocks := final) n` by
    (rpt strip_tac >> irule cleanup_code_end_backward_no_phi >>
     simp[] >> goal_assum $ drule_at Any >> simp[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `code_end_var (f with fn_blocks := final) n` by metis_tac[] >>
  drule (SRULE [] (Q.INST [`f` |-> `f with fn_blocks := final`]
    cleanup_if_origin)) >> strip_tac >>
  gvs[] >> metis_tac[simplified_phi_operand]
QED

Theorem code_end_ssa_protected_facts:
  wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f /\
  fn_entry_label f = SOME entry /\ ir_supply_covers_fn s f /\
  ir_supply_inst_ok s /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f) f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,s1) /\
  visit_blocks path s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs (current_succ_map f) (current_dom_tree f) = ((ct,t,final),events) /\
  current_name_owner (set (fn_ir_vars f)) R u /\
  (!e. MEM e events ==>
    current_stack_owner (set (fn_ir_vars f)) R (SND e.sve_in) /\
    current_stack_owner (set (fn_ir_vars f)) R (SND e.sve_out) /\
    LIST_REL (\i j. LIST_REL (\v n. (n,v) IN R)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) /\
  g = f with fn_blocks := simplify_current_phis_if enabled final ==>
  (!n. code_end_var g n ==> ?x. (n,x) IN R /\ code_end_var f x) /\
  (!n i. code_end_var g n /\ MEM i (fn_insts g) /\
    MEM (Var n) i.inst_operands ==> i.inst_opcode = CODECOPY)
Proof
  strip_tac >>
  `wf_function (f with fn_blocks := bbs)` by
    metis_tac[inserted_function_wf, compute_defs_original_key_domain] >>
  `EVERY current_nondeg_block_shape bbs` by
    (irule makeSsaCurrentNonDegShapeTheory.current_nondeg_add_placement_shape >>
     goal_assum $ drule_at Any >> metis_tac[current_nondeg_input_shape]) >>
  drule_all prepared_actual_tree >> strip_tac >>
  drule_at (Pat `add_phi_nodes_supply _ _ _ _ _ _ = _`)
    local_adjacent_insertion_lifetime >> simp[] >> strip_tac >>
  `(!n. code_end_var (f with fn_blocks := simplify_current_phis_if enabled final) n ==>
    ?x. (n,x) IN R /\ code_end_var (f with fn_blocks := bbs) x) /\
   (!n i. code_end_var (f with fn_blocks := simplify_current_phis_if enabled final) n /\
    MEM i (fn_insts (f with fn_blocks := simplify_current_phis_if enabled final)) /\
    MEM (Var n) i.inst_operands ==> i.inst_opcode = CODECOPY)` by
    (drule (SRULE [] (Q.INST [`f` |-> `f with fn_blocks := bbs`]
      renamed_protected_cleanup_owner)) >>
     disch_then (qspecl_then [`u`,`f`,`set (fn_ir_vars f)`,`R`] mp_tac) >>
     simp[] >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs)` by
       fs[wf_function_def, fn_labels_def] >>
     `!l ss. ALOOKUP (current_succ_map f) l = SOME ss ==> ALL_DISTINCT ss` by
       metis_tac[current_actual_succs_distinct] >>
     drule prepared_original_variable_domain >> strip_tac >>
     `!x bb i. code_end_var (f with fn_blocks := bbs) x /\
        MEM bb bbs /\ MEM i bb.bb_instructions /\ MEM (Var x) i.inst_operands ==>
        i.inst_opcode = CODECOPY /\ ?dst sz.
          i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x` by
       (rpt strip_tac >>
        qpat_x_assum `!x. code_end_var (f with fn_blocks := bbs) x ==> _` drule >>
        strip_tac >> metis_tac[]) >>
     (impl_tac >- (simp[] >> conj_tac >- metis_tac[] >>
       conj_tac >- metis_tac[] >> metis_tac[])) >> metis_tac[]) >>
  `!x. code_end_var (f with fn_blocks := bbs) x ==> code_end_var f x` by
    (rpt strip_tac >> irule phi_prefix_code_end_var >>
     goal_assum $ drule_at Any >>
     drule_at (Pat `add_phi_nodes_supply _ _ _ _ _ _ = _`)
       local_adjacent_insertion_prefix >>
     (impl_tac >- metis_tac[]) >>
     strip_tac >>
     qspec_then `\i. !x. code_end_var f x ==>
       ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs`
       mp_tac phi_prefix_nonphi_insts >>
     simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem code_end_ssa_context_protected_uses:
  current_wf_phi_context supply f renamed supply' A H events /\
  make_ssa_input_ok f /\ fn_entry_label f = SOME entry /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  g = f with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi f.fn_blocks) renamed ==>
  !n i. code_end_var g n /\ MEM i (fn_insts g) /\
    MEM (Var n) i.inst_operands ==> i.inst_opcode = CODECOPY
Proof
  strip_tac >>
  qpat_x_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
  simp[current_wf_phi_context_def, current_wf_precleanup_certificate_def] >>
  strip_tac >> gvs[] >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >>
  qabbrev_tac `ve = SND (visit_blocks [] si
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) (current_dom_postorder f))))))
    ins (current_succ_map f) (current_dom_tree f))` >>
  `visit_blocks [] si
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) (current_dom_postorder f))))))
    ins (current_succ_map f) (current_dom_tree f) = ((ctrs,supply',renamed),ve)` by
    (simp[Abbr `ve`] >> metis_tac[visit_erasure, PAIR, FST]) >>
  drule_all prepared_actual_tree >> strip_tac >>
  drule_all prepared_visit_common_owner >>
  disch_then (qx_choose_then `Hf` strip_assume_tac) >>
  drule_all (SRULE [] (Q.INST [`g` |->
    `f with fn_blocks := simplify_current_phis_if enabled final`]
    code_end_ssa_protected_facts)) >>
  disch_then (qspec_then `blocks_have_leading_phi f.fn_blocks` strip_assume_tac) >>
  simp[]
QED
