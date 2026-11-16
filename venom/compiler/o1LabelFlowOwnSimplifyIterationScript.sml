Theory o1LabelFlowOwnSimplifyIteration
Ancestors
  o1LabelFlowSimplifyPreservation o1LabelFlowLateContracts
  o1ContractSimplifyCfg simplifyCfgPhiRepair simplifyCfgDefs
  o1PassContract unitShapeDefs venomFnScheduleRunnerProps list
  simplifyCfgInvariant simplifyCfgWfssa simplifyCfgStruct

(* Local transform contracts are explicit hypotheses: this iteration theory
   is independent of the theories that discharge them. *)
Theorem simplify_collapse_code_end_uses_conditional:
  ((!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (remove_unreachable_blocks f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (fix_all_phis f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (fix_all_phis f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b. wf_function f /\ fn_inst_wf f /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
    MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
    (!i x. MEM i (fn_insts (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
      MEM (Var x) i.inst_operands /\ code_end_var (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b lm g lm'. lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\ code_end_var g x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)))) ==>
  !f lm vis lbl.
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\ all_reachable f /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  wf_ssa (FST (collapse_dfs f lm vis lbl)) /\
  wf_function (FST (collapse_dfs f lm vis lbl)) /\
  fn_inst_wf (FST (collapse_dfs f lm vis lbl)) /\
  first_block_no_preds (FST (collapse_dfs f lm vis lbl)) /\
  scfg_phi_safe (FST (collapse_dfs f lm vis lbl)) /\
  fn_defs_reach_uses (FST (collapse_dfs f lm vis lbl)) /\
  EVERY label_positions_ok (fn_insts (FST (collapse_dfs f lm vis lbl))) /\
  all_reachable (FST (collapse_dfs f lm vis lbl)) /\
  (!i x. MEM i (fn_insts (FST (collapse_dfs f lm vis lbl))) /\ MEM (Var x) i.inst_operands /\
    code_end_var (FST (collapse_dfs f lm vis lbl)) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "unreachable")
    (CONJUNCTS_THEN2 (mk_asm "phis")
      (CONJUNCTS_THEN2 (mk_asm "chain") (mk_asm "jump")))) >>
  ho_match_mp_tac collapse_dfs_preserves_predicate >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all do_merge_jump_ssa_invariant >> strip_tac >> simp[] >>
      asm "jump" (drule_at (Pat `do_merge_jump _ _ _ _ = _`)) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next /\
   MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  drule_at (Pat `can_merge_blocks _ _ _`) chain_merge_ssa_invariant >>
  simp[] >> strip_tac >> simp[] >>
  asm "chain" (qspecl_then [`f`, `a`, `b`] mp_tac) >> simp[]
QED

Theorem simplify_round_code_end_uses_conditional:
  ((!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (remove_unreachable_blocks f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (fix_all_phis f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (fix_all_phis f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b. wf_function f /\ fn_inst_wf f /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
    MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
    (!i x. MEM i (fn_insts (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
      MEM (Var x) i.inst_operands /\ code_end_var (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b lm g lm'. lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\ code_end_var g x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)))) ==>
  !f. wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\ EVERY label_positions_ok (fn_insts f) /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts (FST (simplify_cfg_round_with_labels f))) /\ MEM (Var x) i.inst_operands /\
    code_end_var (FST (simplify_cfg_round_with_labels f)) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  disch_then (fn th => mk_asm "H" th >>
    CONJUNCTS_THEN2 (mk_asm "unreachable")
      (CONJUNCTS_THEN2 (mk_asm "phis")
        (CONJUNCTS_THEN2 (mk_asm "chain") (mk_asm "jump"))) th) >>
  mp_tac simplify_collapse_code_end_uses_conditional >>
  (impl_tac >- asm "H" ACCEPT_TAC) >> disch_then (mk_asm "collapse") >>
  gen_tac >> strip_tac >> Cases_on `fn_entry_label f`
  >- simp[simplify_cfg_round_with_labels_def] >>
  drule_all simplify_cfg_round_entry_ssa_invariant >> strip_tac >>
  asm "unreachable" (qspec_then `f` mp_tac) >> simp[] >>
  strip_tac >> asm "phis" (drule_at Any) >> strip_tac >>
  qabbrev_tac `start = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs start [] [] x` >> PairCases_on `r` >>
  asm "collapse" (qspecl_then [`start`, `[]`, `[]`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  `subst_block_labels_fn r0 q = q` by
    (drule_at (Pat `collapse_dfs _ _ _ _ = _`) collapse_dfs_subst_identity >> simp[]) >>
  asm "unreachable" (qspec_then `q` mp_tac) >> simp[] >>
  strip_tac >> asm "phis" (drule_at Any) >> strip_tac >>
  fs[Abbr `start`] >> simp[simplify_cfg_round_with_labels_def]
QED

Theorem simplify_iter_code_end_uses_conditional:
  ((!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (remove_unreachable_blocks f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (fix_all_phis f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (fix_all_phis f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b. wf_function f /\ fn_inst_wf f /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
    MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
    (!i x. MEM i (fn_insts (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
      MEM (Var x) i.inst_operands /\ code_end_var (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b lm g lm'. lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\ code_end_var g x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)))) ==>
  !fuel f. wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\ EVERY label_positions_ok (fn_insts f) /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts (FST (simplify_cfg_iter_with_labels fuel f))) /\ MEM (Var x) i.inst_operands /\
    code_end_var (FST (simplify_cfg_iter_with_labels fuel f)) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  disch_then (mk_asm "H") >>
  mp_tac simplify_round_code_end_uses_conditional >>
  (impl_tac >- asm "H" ACCEPT_TAC) >> disch_then (mk_asm "round") >>
  Induct_on `fuel` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all simplify_cfg_round_ssa_invariant >> strip_tac >>
  asm "round" (qspec_then `f` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels f` >> gvs[] >>
  simp[simplify_cfg_iter_with_labels_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels fuel q` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED

Theorem simplify_row5_code_end_uses_conditional:
  ((!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (remove_unreachable_blocks f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f.
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts (fix_all_phis f)) /\ MEM (Var x) i.inst_operands /\ code_end_var (fix_all_phis f) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b. wf_function f /\ fn_inst_wf f /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
    MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
    (!i x. MEM i (fn_insts (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
      MEM (Var x) i.inst_operands /\ code_end_var (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))) /\
   (!f a b lm g lm'. lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') /\
    (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
    (!i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\ code_end_var g x ==>
      (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
      (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)))) ==>
  !rp observed s f out.
  fn_pass_step rp (CFP_Simple VP_SimplifyCFG) observed s f out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 5 f /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts out.fpo_function) /\ MEM (Var x) i.inst_operands /\
    code_end_var out.fpo_function x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz. i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  disch_then (mk_asm "H") >>
  mp_tac simplify_iter_code_end_uses_conditional >>
  (impl_tac >- asm "H" ACCEPT_TAC) >> disch_then (mk_asm "iter") >>
  rpt gen_tac >> strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context f` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
   first_block_no_preds f /\ first_block_no_phi f /\
   EVERY label_positions_ok (fn_insts f)` by
    (fs[o1_fn_row_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `scfg_phi_safe f /\ fn_defs_reach_uses f` by
    metis_tac[simplify_cfg_fn_ok_ssa, simplify_cfg_fn_ok_phi_safe] >>
  `out.fpo_function = FST (simplify_cfg_fn_with_labels f)` by
    metis_tac[simplify_cfg_pass_step_function, simplify_cfg_fn_def] >>
  gvs[simplify_cfg_fn_with_labels_def] >>
  asm "iter" (qspec_then `LENGTH f.fn_blocks` mp_tac) >>
  disch_then (qspec_then `f` mp_tac) >> simp[]
QED
