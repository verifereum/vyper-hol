Theory o1LabelFlowOwnSecondSsa
Ancestors
  codegenSymOwnRel o1LabelFlowMiddle o1LabelFlowMiddleSsa
  o1LabelFlowMiddleInsertion o1LabelFlowMiddleTraversal
  o1LabelFlowMiddleCleanupFlow o1ContractMakeSsaReplay
  o1ContractMakeSsaStep o1PassContract makeSsaDefs
  unitShapeDefs venomFnScheduleRunnerProps venomPassSchedule
  venomPassDispatcher venomInst list

(* The middle lifetime protects every code-end-pointer read. Insertion
   preserves that lifetime; common trace ownership transports the protected
   reads through renaming. PHI cleanup cannot introduce a protected read.
   Output shape supplies the relaxed own-code CODECOPY source clause. *)

Theorem prepared_renaming_code_end_use:
  wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f /\
  fn_entry_label f = SOME entry /\ ir_supply_covers_fn s f /\
  ir_supply_inst_ok s /\ middle_code_end_lifetime f /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f) f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,s1) /\
  rename_current_blocks s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs (current_succ_map f) (current_dom_tree f) = (ct,t,final) ==>
  !j n. MEM j (fn_insts (f with fn_blocks := final)) /\
    MEM (Var n) j.inst_operands /\
    code_end_var (f with fn_blocks := final) n ==>
    j.inst_opcode = CODECOPY /\
    ?dst sz. j.inst_operands = [dst; Var n; sz] /\
      dst <> Var n /\ sz <> Var n
Proof
  strip_tac >>
  `wf_function (f with fn_blocks := bbs)` by
    metis_tac[inserted_function_wf,
      o1MakeSsaEventOwnershipTheory.compute_defs_original_key_domain] >>
  `EVERY current_nondeg_block_shape bbs` by
    (irule makeSsaCurrentNonDegShapeTheory.current_nondeg_add_placement_shape >>
     goal_assum $ drule_at Any >>
     metis_tac[makeSsaCurrentNonDegCleanupTheory.current_nondeg_input_shape]) >>
  drule_all prepared_actual_tree >> strip_tac >>
  qabbrev_tac `trace = visit_blocks [] s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs (current_succ_map f) (current_dom_tree f)` >>
  `FST trace = (ct,t,final)` by
    simp[Abbr `trace`, o1MakeSsaVisitTraceTheory.visit_erasure] >>
  `trace = ((ct,t,final),SND trace)` by metis_tac[pairTheory.PAIR] >>
  qunabbrev_tac `trace` >>
  drule_all prepared_visit_common_owner >> strip_tac >>
  drule prepared_original_variable_domain >> strip_tac >>
  `!x. code_end_var (f with fn_blocks := bbs) x ==>
    !bb j. MEM bb bbs /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      ?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x` by
    (drule_at (Pat `add_phi_nodes_supply _ _ _ _ _ _ = _`)
       local_adjacent_insertion_lifetime >>
     fs[middle_code_end_lifetime_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs)` by
    fs[venomWfTheory.wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) final)` by
    metis_tac[cj 1 makeSsaCurrentPropsTheory.rename_current_blocks_labels] >>
  `!j. MEM j (fn_insts (f with fn_blocks := final)) ==>
    ?i. MEM i (fn_insts (f with fn_blocks := bbs)) /\
      j.inst_opcode = i.inst_opcode /\
      LIST_REL (\v n. (n,v) IN H) i.inst_outputs j.inst_outputs /\
      (i.inst_opcode <> PHI ==>
       LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                        | _ => b = a) i.inst_operands j.inst_operands)` by
    (gen_tac >> strip_tac >>
     drule (SRULE [] (Q.INST [`f` |-> `f with fn_blocks := bbs`]
       visit_blocks_owned_inst)) >> disch_then irule >>
     goal_assum $ drule_at Any >> simp[] >>
     qexistsl [`set (fn_ir_vars f)`,`t`] >> simp[] >> metis_tac[]) >>
  `!j n x. MEM j (fn_insts (f with fn_blocks := final)) /\
    MEM (Var n) j.inst_operands /\ (n,x) IN H /\
    code_end_var (f with fn_blocks := bbs) x ==>
    j.inst_opcode = CODECOPY /\
    ?dst sz. j.inst_operands = [dst; Var n; sz] /\
      dst <> Var n /\ sz <> Var n` by
    (rpt gen_tac >> strip_tac >>
     `?q bb k. lookup_block q final = SOME bb /\
       k < LENGTH bb.bb_instructions /\ j = EL k bb.bb_instructions` by
       (metis_tac[SRULE [] (Q.INST
          [`f` |-> `f with fn_blocks := final`] fn_insts_lookup_index)]) >>
     drule visit_blocks_protected_read >> disch_then irule >>
     goal_assum $ drule_at Any >> simp[] >>
     conj_tac
     >- metis_tac[makeSsaCurrentTraceCertificateTheory.current_actual_succs_distinct] >>
     conj_tac >- metis_tac[EL_MEM] >>
     qexistsl [`H`,`set (fn_ir_vars f)`,`t`,`x`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `?x. (n,x) IN H /\ code_end_var (f with fn_blocks := bbs) x` by
    (drule code_end_var_owned_bound >>
     disch_then (qspecl_then [`f with fn_blocks := bbs`,`H`] irule) >>
     conj_tac >- metis_tac[] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!j. MEM j (fn_insts _) ==> _` drule >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem cleanup_code_end_use:
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    i.inst_opcode = CODECOPY /\
    ?dst sz. i.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x) ==>
  !i x.
    MEM i (fn_insts (f with fn_blocks :=
      simplify_current_phis_if enabled f.fn_blocks)) /\
    MEM (Var x) i.inst_operands /\
    code_end_var (f with fn_blocks :=
      simplify_current_phis_if enabled f.fn_blocks) x ==>
    i.inst_opcode = CODECOPY /\
    ?dst sz. i.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x
Proof
  strip_tac >>
  `!j y. MEM j (fn_insts f) /\ j.inst_opcode = PHI /\
    code_end_var f y ==> ~MEM (Var y) j.inst_operands` by
    (rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `code_end_var f x` by
    (drule cleanup_code_end_backward_no_phi >>
     disch_then irule >> simp[] >> qexists `enabled` >> simp[]) >>
  drule cleanup_if_origin >> strip_tac
  >- metis_tac[] >>
  `MEM (Var x) j.inst_operands` by
    metis_tac[simplified_phi_operand] >>
  metis_tac[]
QED

Theorem compose_second_ssa_own:
  !rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 4 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (4 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 4 /\ 4 <= 4 ==> middle_code_end_lifetime f) /\
  (4 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (5 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 5 /\ 5 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (5 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)

Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >>
     simp[fn_pass_tag_def]) >>
  simp[] >>
  `MEM f observed.cu_context.ctx_functions` by
    (fs[fn_pass_step_def] >>
     drule lookup_unique_function_member >> simp[]) >>
  `o1_fn_shape observed.cu_context f` by
    fs[o1_ctx_shape_def, EVERY_MEM] >>
  `make_ssa_input_ok f` by fs[o1_fn_row_def] >>
  drule make_ssa_pass_step_replay >> strip_tac >>
  `o1_fn_shape observed.cu_context out.fpo_function` by
    (irule make_ssa_current_fn_o1_shape >> metis_tac[]) >>
  Cases_on `fn_entry_label f`
  >- (fs[make_ssa_current_fn_def] >> gvs[]) >>
  irule label_flow_own_ok_from_code_end_use >>
  reverse conj_tac
  >- fs[o1_fn_shape_def] >>
  fs[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `!j n. MEM j (fn_insts (f with fn_blocks := bbs2)) /\
    MEM (Var n) j.inst_operands /\
    code_end_var (f with fn_blocks := bbs2) n ==>
    j.inst_opcode = CODECOPY /\
    ?dst sz. j.inst_operands = [dst; Var n; sz] /\
      dst <> Var n /\ sz <> Var n` by
    (fs[o1_fn_shape_def] >>
     drule_at (Pat `add_phi_nodes_supply _ _ _ _ _ _ = _`)
       prepared_renaming_code_end_use >>
     simp[current_dom_tree_def, current_succ_map_def] >>
     metis_tac[]) >>
  drule cleanup_code_end_use >> simp[] >>
  qpat_x_assum `_ = out.fpo_function` (SUBST1_TAC o SYM) >>
  simp[] >> metis_tac[]
QED
