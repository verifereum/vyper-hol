(* Typed source representation at the extract32 suffix entry. *)
Theory bodyMemTbExtract32TypedSuffix
Ancestors
  bodyMemTbExtract32IntClamp bodyMemTbExtract32Readonly bodyMemTbExtract32Load bodyMemTbExtract32Cuts bodyMemTbExtract32Slice bodyMemTbExtract32Encoding stmtSimLogArgs
  exprSimHash exprSimProps exprSimWordArgs loweringPosts exprSimDefs
  valueEncoding vyperTypeSystem compileEnv

Theorem extract32_source_bytes_kept:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sm es (BytesV bs) src s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand src s = SOME w /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) s.vs_memory /\
  expr_post ctx func cenv cx off es sm sb s es' v op t ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) t.vs_memory
Proof
  strip_tac >>
  `log_arg_clear cenv cx (BaseT (BytesT (Dynamic cap))) (BytesV bs)` by
    (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
  `wb_frame cenv es sm s t` by metis_tac[expr_post_frame] >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  drule_all log_argument_footprint_kept >> strip_tac >>
  drule_all expr_val_at_footprint >> strip_tac >>
  irule val_in_memory_footprint_agree >> metis_tac[]
QED

