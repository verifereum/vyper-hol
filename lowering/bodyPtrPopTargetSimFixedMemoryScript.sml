Theory bodyPtrPopTargetSimFixedMemory
Ancestors
  bodyPtrPopTargetSimArrayContinue bodyPtrPopTargetSimArraySource
  bodyPtrPopTargetSimArrayCase bodyPtrPopTargetDefs
  exprLowering loweringPosts vyperValueOperation vyperValue vyperTyping compileEnv words list

(* Source selection uses the current local entry, not the pre-index value.
   Both successful and failing bounds are paired with checked execution. *)
Theorem target_fixed_memory_array_continue_ptr:
  compile_array_subscript bop idx F cnt ws (type_memory_size etv)
    (is_signed_type ity) loader sn = (dst,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME (val_to_w256 iv) /\
  fresh_vars_wrt sn s /\ op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  lookup_scopes id ef.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Fixed cnt)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed cnt)) = SOME (ArrayTV etv (Fixed cnt)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed cnt)) (ArrayV av) /\
  is_int_type ity /\ evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv iv /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b loc (Type (ArrayT et (Fixed cnt))) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (bop,loc,SOME (ValPT (ArrayT et (Fixed cnt)))) G tn s ==>
  (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) ef =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))),ef) /\
   ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
     target_post ctx fn cenv cx es sa sb s0 ef
       (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))) (Type et)
       (dst,loc,SOME (ValPT et)) t /\
     ghost_inv d cenv cx ef H un t /\
     target_ptr_ok cenv (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
       (dst,loc,SOME (ValPT et)) H un t /\ ghost_kept cenv es sa G0 tn0 s0 H un /\
     t.vs_current_bb = s.vs_current_bb /\
     t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sn sb)) \/
  (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) ef =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),ef) /\
   ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
     (Abort Revert_abort (t with vs_inst_idx := pc)))
Proof
  strip_tac >> drule_all target_live_memory_array_extend >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  `array_length (ArrayTV etv (Fixed cnt)) av = cnt` by
    (Cases_on `av` >> fs[value_has_type_def, array_length_def]) >>
  Cases_on `idx_in_range (is_signed_type ity) (val_to_w256 iv) (n2w cnt)`
  >- suspend "success" >> suspend "abort"
QED

Resume target_fixed_memory_array_continue_ptr[success]:
  fs[] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
    (b + val_to_w256 iv * n2w (type_memory_size etv)) loc (Type et)` by
    (drule_all target_memory_child_layout >>
     simp[GSYM word_mul_n2w]) >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
    (bop,loc,SOME (value_type_place (Type et))) G tn s` by
    fs[target_ptr_ok_def] >>
  gvs[value_type_place_def] >>
  drule_all (SRULE [value_type_place_def, arithmeticTheory.ADD_COMM]
    (Q.INST [`ty` |-> `Type et`] target_fixed_array_continue_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Resume target_fixed_memory_array_continue_ptr[abort]:
  gvs[] >>
  drule_all target_fixed_array_abort_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Finalise target_fixed_memory_array_continue_ptr
