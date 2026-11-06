Theory bodyPtrBopParentPost
Ancestors
  bodyPtrBopScalarOutcome bodyPtrBopEntry bodyPtrBopSource
  bodyPtrBopScalarSeq exprSimProps exprLoweringProps compileEnv
  exprBopSimProps exprSimWordArgs bodyPtrDefs ptrDiscipline
  venomState finite_map wordArgsPtr bodyPtrBopOperandContract

Theorem bop_scalar_runtime_post:
  bop_scalar_seq {z | not_fresh_at c2 z} A code B /\
  run_inst_seq code t2 = OK t /\ local_ptrs_reserved cenv c2 /\
  stmt_state_rel ctx func cenv cx es2 t2 ==>
  stmt_state_rel ctx func cenv cx es2 (t with vs_inst_idx := j) /\
  (!z w. not_fresh_at c2 z /\ lookup_var z t2 = SOME w ==>
         lookup_var z (t with vs_inst_idx := j) = SOME w) /\
  (!aid b. FLOOKUP t2.vs_allocas aid = SOME b ==>
           FLOOKUP (t with vs_inst_idx := j).vs_allocas aid = SOME b) /\
  (t with vs_inst_idx := j).vs_memory = t2.vs_memory /\
  (t with vs_inst_idx := j).vs_halted = t2.vs_halted /\
  (t with vs_inst_idx := j).vs_current_bb = t2.vs_current_bb
Proof
  strip_tac >> drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es2 (t2 with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >>
     gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `t = t2 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[stmt_state_rel_inst_idx, lookup_var_def, pred_setTheory.GSPECIFICATION] >>
  metis_tac[]
QED

Theorem bop_pair_ghost_kept_suffix:
  bop_operand_post d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  stmt_state_rel ctx func cenv cx es t0 /\
  local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv c1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  ca.cs_next_var <= c1.cs_next_var /\ ca.cs_next_id <= c1.cs_next_id /\
  c1.cs_next_var <= c2.cs_next_var /\ c1.cs_next_id <= c2.cs_next_id /\
  ghost_kept cenv es2 c2 G2 tn2 t2 G tn ==>
  ghost_kept cenv es ca G0 tn0 t0 G tn
Proof
  simp[bop_operand_post_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t1 /\
   wb_frame cenv es ca t0 t1 /\ wb_frame cenv es1 c1 t1 t2` by
    metis_tac[expr_post_frame, expr_post_state] >>
  `ghost_kept cenv es1 c1 G1 tn1 t1 G tn` by
    metis_tac[ghost_kept_wb_trans] >>
  metis_tac[ghost_kept_wb_trans]
QED
