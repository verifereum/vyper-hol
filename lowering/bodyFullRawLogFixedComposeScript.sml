(* Composition of the fixed RawLog data continuation. *)
Theory bodyFullRawLogFixedCompose
Ancestors
  bodyFullRawLogFixedBoundary bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasOutcomeFullStmts gasShadowState gasShadow bodyFullShared
  exprLoweringProps exprOperandVar exprSimProps exprSimWordArgs
  stmtSimDefs exprSimMemDefs exprSimDefs gasExemptCert
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyPtrDefs
  loweringShapeDefs vyperInterpreter vyperState vyperValue vyperEvent
  venomState words list rich_list arithmetic finite_map pred_set

(* Reanchor the scalar child's frame across the scratch allocation. *)
Theorem raw_log_fixed_data_reanchor:
  compile_alloc_buffer 32 sa = (buf,sd) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  expr_post H ctx func cenv cx data es sd sm u ee v op t /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) ==>
  expr_post H ctx func cenv cx data es sa sm s ee v op t
Proof
  strip_tac >>
  `wb_frame cenv es es sa s u` by
    simp[wb_frame_def, locals_kept_mem] >>
  `wb_frame cenv es ee sa s t` by
    (irule wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`es`, `sd`, `u`] >> simp[] >>
         metis_tac[expr_post_frame]) >>
     metis_tac[]) >>
  `~expr_has_effect data ==> pure_frame cenv func es sa s t` by
    (strip_tac >> irule pure_frame_trans >> simp[] >>
     qexistsl [`es`, `sd`, `u`] >>
     fs[expr_post_def, pure_frame_def] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  fs[expr_post_def, wb_frame_def, expr_val_at_def,
     compileEnvTheory.is_word_type_def] >> first_assum MATCH_ACCEPT_TAC
QED
