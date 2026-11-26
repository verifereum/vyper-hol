(* Saved raw-call operands and the caller frame across the keyword cut. *)
Theory bodyRawBytesKeywordSavedMods
Ancestors
  exprSimPrecompiles exprSimWordArgs wordArgsPtr bodyMemoryDefs exprSafeOperand
  loweringPosts loweringShapeDefs loweringStateRelDefs exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState words finite_map compileEnv vyperAST

val _ = Parse.hide "base";
val _ = Parse.hide "size";

Triviality keyword_saved_operand:
  wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G' tn' /\
  safe_operand sa op ==>
  (!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op
Proof
  Cases_on `op` >>
  simp[safe_operand_def, eval_operand_def, op_taint_def, op_prov_def,
       wb_frame_def, ghost_kept_at_def] >>
  metis_tac[]
QED

Triviality keyword_saved_return_buf:
  return_buf_frame d ce sa s /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_var <= sb.cs_next_var /\ wb_frame ce es ee sm s t /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d ce sb t
Proof
  strip_tac >> irule return_buf_frame_frame >>
  qpat_assum `return_buf_frame _ _ _ s` (irule_at Any) >>
  simp[] >> rpt strip_tac >> irule wb_frame_vars >>
  qpat_assum `wb_frame _ _ _ sm s t` (irule_at Any) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem raw_bytes_keyword_saved_mods:
  stmt_state_rel H0 ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM esD.scopes /\
  sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id /\
  ci_mono s4 s5 /\
  wb_frame cenv es esD sa s0 t4 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4 /\
  return_buf_frame dframe cenv sa t4 /\ return_buf_frame dframe cenv s4 t4 /\
  s0.vs_alloca_next <= t4.vs_alloca_next /\
  typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
  ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK /\
  t4.vs_alloca_next <= tk.vs_alloca_next /\
  EVERY (safe_operand s4) [addr; len; Var p] /\
  expr_val_rel cx (BaseT AddressT) av addr t4 /\
  eval_operand len t4 = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) t4 = SOME (n2w (b+32)) /\
  EVERY (\op. op_taint tn4 op = {}) [addr; len; Var p] /\
  op_prov G4 addr = NONE /\ op_prov G4 len = NONE /\
  op_prov G4 (Var p) = SOME (base,size) /\
  base <= b+32 /\ b+32+LENGTH bs <= base+size /\
  (bs <> [] ==> ptr_covers G4 tn4 p t4 (LENGTH bs)) /\
  b+32+LENGTH bs <= t4.vs_alloca_next ==>
  expr_val_rel cx (BaseT AddressT) av addr tk /\
  eval_operand len tk = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) tk = SOME (n2w (b+32)) /\
  EVERY (safe_operand s5) [addr; len; Var p] /\
  EVERY (\op. op_taint tnK op = {}) [addr; len; Var p] /\
  op_prov GK addr = NONE /\ op_prov GK len = NONE /\
  op_prov GK (Var p) = SOME (base,size) /\
  base <= b+32 /\ b+32+LENGTH bs <= base+size /\
  (bs <> [] ==> ptr_covers GK tnK p tk (LENGTH bs)) /\
  (!aid entry. FLOOKUP t4.vs_allocas aid = SOME entry ==>
     FLOOKUP tk.vs_allocas aid = SOME entry) /\
  b+32+LENGTH bs <= tk.vs_alloca_next /\ s0.vs_alloca_next <= tk.vs_alloca_next /\
  wb_frame cenv es esK sa s0 tk /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK /\
  return_buf_frame dframe cenv sa tk /\ return_buf_frame dframe cenv s5 tk
Proof
  strip_tac >>
  `wb_frame cenv esD esK s4 t4 tk` by fs[typed_args_post_def] >>
  `wb_frame cenv es esK sa s0 tk` by
    (irule wb_frame_trans >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es esD sa s0 t4` (irule_at Any) >>
     qexists_tac `s4` >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK` by
    (qpat_x_assum `wb_frame cenv es esK sa s0 tk` kall_tac >>
     drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans) >>
  `s4.cs_next_var <= s5.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame dframe cenv sa tk` by
    (irule keyword_saved_return_buf >>
     qpat_assum `return_buf_frame dframe cenv sa t4` (irule_at Any) >>
     qpat_assum `wb_frame cenv esD esK s4 t4 tk` (irule_at Any) >> simp[]) >>
  `return_buf_frame dframe cenv s5 tk` by
    (irule keyword_saved_return_buf >>
     qpat_assum `return_buf_frame dframe cenv s4 t4` (irule_at Any) >>
     qpat_assum `wb_frame cenv esD esK s4 t4 tk` (irule_at Any) >> simp[]) >>
  `!op. safe_operand s4 op ==>
      (!w. eval_operand op t4 = SOME w ==> eval_operand op tk = SOME w) /\
      op_taint tnK op = op_taint tn4 op /\ op_prov GK op = op_prov G4 op` by
    (gen_tac >> disch_tac >> irule keyword_saved_operand >>
     qpat_assum `ghost_kept_at _ _ esD s4 G4 tn4 t4 GK tnK` (irule_at Any) >>
     qexists_tac `esK` >> simp[]) >>
  `safe_operand s4 addr /\ safe_operand s4 len /\ safe_operand s4 (Var p)` by fs[] >>
  `expr_val_rel cx (BaseT AddressT) av addr tk` by
    (qpat_assum `expr_val_rel _ _ _ addr t4` mp_tac >>
     simp[NoAsms, expr_val_rel_def, is_word_type_def] >> strip_tac >>
     rename1 `eval_operand addr t4 = SOME w` >> qexists_tac `w` >> simp[]) >>
  `bs <> [] ==> ptr_covers GK tnK p tk (LENGTH bs)` by
    (disch_tac >>
     `ptr_covers G4 tn4 p t4 (LENGTH bs)` by simp[] >>
     pop_assum (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     rename1 `FLOOKUP G4 p = SOME (oldbase,oldsize)` >>
     rename1 `lookup_var p t4 = SOME w` >>
     simp[ptr_covers_def] >> qexistsl_tac [`w`,`oldbase`,`oldsize`] >>
     qpat_assum `!op. safe_operand s4 op ==> _` (qspec_then `Var p` mp_tac) >>
     simp[NoAsms, op_prov_def, eval_operand_def] >>
     disch_then (drule_then strip_assume_tac) >> simp[]) >>
  `EVERY (safe_operand s5) [addr; len; Var p]` by
    (simp[] >> rpt conj_tac >> irule safe_operand_mono >> qexists_tac `s4` >> simp[]) >>
  `!aid entry. FLOOKUP t4.vs_allocas aid = SOME entry ==>
       FLOOKUP tk.vs_allocas aid = SOME entry` by fs[wb_frame_def] >>
  fs[]
QED
