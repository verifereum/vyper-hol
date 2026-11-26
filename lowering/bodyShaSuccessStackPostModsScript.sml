(* The typed successful SHA endpoint, exposed as a linked stack post. *)
Theory bodyShaSuccessStackPostMods
Ancestors
  exprSimHash bodyFullPostsMods loweringPosts exprSimVVFrame
  bodyPtrDefs exprLoweringProps compileEnv vyperInterpreter vyperState
  vyperTyping vyperValue vyperAST vyperTypeSystem

Theorem sha_success_stack_post_mods:
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  run_inst_seq (emitted_insts sm sb) s = OK z /\
  immutable_frame_mods func cenv cx ef z /\
  ef = SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid) ==>
  ?w. builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32)))
      Sha256 [expr_type e] [v] = INL w /\
    vv_post_mods H ctx func cenv cx
      (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 ef (Value w) (StackValue (BaseT (BytesT (Fixed 32))) op) z
Proof
  strip_tac >>
  drule_at (Pat `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_post_run >>
  simp[] >> strip_tac >> gvs[] >>
  qhdtm_assum `vv_post`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def, vv_at_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, vv_own_def, read_result_def,
       return_def, vv_storage_live_def] >>
  metis_tac[]
QED
