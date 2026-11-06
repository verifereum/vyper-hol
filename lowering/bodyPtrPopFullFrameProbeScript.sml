Theory bodyPtrPopFullFrameProbe
Ancestors
  supportedProgram vyperTypeContract vyperValue words compileEnv compileVyper
  venomCompilerTypes alist integer_word
Libs finite_mapLib computeLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

(* Concrete names keep the full-entry control experiment readable. These
   definitions name a supported source fixture, not an assumed frame. *)
Definition pop_full_frame_expr_def:
  pop_full_frame_expr =
    Pop (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"a"))
End
Definition pop_full_frame_tops_def:
  pop_full_frame_tops =
    [VariableDecl Private Storage "a"
       (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (SOME 0);
     FunctionDecl Internal Nonpayable F F "take" [] []
       (BaseT (UintT 256)) [Return (SOME pop_full_frame_expr)]]
End

Theorem pop_full_frame_supported:
  supported_program pop_full_frame_tops
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_cenv_def:
  pop_full_frame_cenv =
    (build_compile_env pop_full_frame_tops Internal Nonpayable "take" []
      (BaseT (UintT 256)) [Return (SOME pop_full_frame_expr)] F) with
      <| ce_is_ctor := F; ce_raw_return := F;
         ce_nonreentrant := (F,0,F,F) |>
End

Theorem pop_full_frame_allocs:
  fn_allocs_ok pop_full_frame_tops
    (Nonpayable,F,F,"take",[],([] : expr list),BaseT (UintT 256),
      [Return (SOME pop_full_frame_expr)])
Proof
  simp[fn_allocs_ok_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_policy_def:
  pop_full_frame_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End

Theorem pop_full_frame_unit_exists:
  IS_SOME (lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_unit_def:
  pop_full_frame_unit = THE
    (lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy)
End

Theorem pop_full_frame_unit_lowered:
  lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy =
    SOME pop_full_frame_unit
Proof
  metis_tac[pop_full_frame_unit_exists, pop_full_frame_unit_def,
            optionTheory.IS_SOME_EXISTS, optionTheory.THE_DEF]
QED
