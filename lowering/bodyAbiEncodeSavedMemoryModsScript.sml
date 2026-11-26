(* Identity restoration of a saved stack or memory ABI operand. *)
Theory bodyAbiEncodeSavedMemoryMods
Ancestors
  bodyAbiEncodePackedPostMods bodyFullPostsMods bodyPtrDefs
  loweringPosts exprSimMemDefs exprLowering compileEnv
  fragGasOriginPtr venomState vyperInterpreter vyperTypeSystem
  finite_map list pair option

(* A saved aggregate which is already on the stack, or already points at
   memory, is not changed by unwrap_value.  The value and pointer facts are
   therefore available at the old compiler provenance interval. *)
Theorem abi_encode_saved_memory_restore_mods:
  ty = lowered_value_type ce e /\
  ((?tag op. saved = StackValue tag op) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\
      p.ptr_location = LocMemory)) /\
  unwrap_value ce saved ready = (src,u) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx ty raw saved ee s /\
  vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx ty ty ee raw saved s /\
  (!x. src = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted ==>
  u = ready /\ src = vv_operand saved /\
  expr_val_at ce cx ty si ss ee v src s /\
  expr_val_rel cx ty v src s /\
  ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s /\
  (!D lo explicit ctx func PG.
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK s,G,tn))
Proof
  strip_tac >> Cases_on `saved` >> gvs[unwrap_value_def, comp_return_def]
  >- (rename1 `StackValue tag op` >>
      gvs[vv_holds_mods_def, vv_holds_def, vv_at_def, ptr_vv_ok_def,
          vv_store_bound_def, expr_val_at_def, expr_val_rel_def,
          ptr_val_ok_def, expr_store_bound_def] >>
      rpt conj_tac >> simp[contextTheory.vv_operand_def, gas_origin_ptr_path_rules])
  >- (rename1 `LocatedValue tag p` >>
      `expr_val_at ce cx tag si ss ee v p.ptr_operand s` by
        (qspecl_then [`ce`,`cx`,`tag`,`si`,`ss`,`ee`,`raw`,`tag`,`p`,`s`,`v`]
           mp_tac exprSimPropsTheory.vv_at_memory_val_at >> simp[]) >>
      gvs[vv_holds_mods_def, vv_holds_def, vv_at_def, ptr_vv_ok_def,
          vv_store_bound_def, expr_val_at_def, expr_val_rel_def,
          ptr_val_ok_def, expr_store_bound_def] >>
      rpt conj_tac >> simp[contextTheory.vv_operand_def, gas_origin_ptr_path_rules])
QED
