Theory bodyPtrPopTargetSimFixedSlot
Ancestors
  bodyPtrPopTargetSimArrayContinue bodyPtrPopTargetSimArraySource
  bodyPtrPopTargetSimArrayCase bodyPtrPopTargetDefs exprSimCopy
  exprLowering loweringPosts compileEnv words list

Theorem target_fixed_slot_array_continue_ptr:
  compile_array_subscript bop idx F cnt ws (type_slot_size etv)
    (is_signed_type ity) loader sn = (dst,sb) /\
  eval_operand bop s = SOME slot /\ eval_operand idx s = SOME (val_to_w256 iv) /\
  copy_old_operand sn bop /\ copy_old_operand sn idx /\ op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed cnt)) = SOME (ArrayTV etv (Fixed cnt)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  slots_in_range (get_storage cx ef tr) (w2n slot) (ArrayTV etv (Fixed cnt)) /\
  is_int_type ity /\ evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv iv /\
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed cnt))))
    slot loc (Type (ArrayT et (Fixed cnt))) /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed cnt))))
    (bop,loc,SOME (ValPT (ArrayT et (Fixed cnt)))) G tn s ==>
  (?child. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed cnt))))
     (ValueSubscript iv) ef = (INL child,ef) /\
   ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
     target_post ctx fn cenv cx es sa sb s0 ef child (Type et) (dst,loc,SOME (ValPT et)) t /\
     ghost_inv d cenv cx ef H un t /\
     target_ptr_ok cenv child (dst,loc,SOME (ValPT et)) H un t /\
     ghost_kept cenv es sa G0 tn0 s0 H un /\
     t.vs_current_bb = s.vs_current_bb /\
     t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sn sb)) \/
  (?msg. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed cnt))))
     (ValueSubscript iv) ef = (INR (Error (RuntimeError msg)),ef) /\
   ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
     (Abort Revert_abort (t with vs_inst_idx := pc)))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`bd` |-> `Fixed cnt`, `len` |-> `cnt`]
    target_typed_storage_array_extend)) >> strip_tac >>
  Cases_on `idx_in_range (is_signed_type ity) (val_to_w256 iv) (n2w cnt)`
  >- suspend "success" >> suspend "abort"
QED

Resume target_fixed_slot_array_continue_ptr[success]:
  fs[] >>
  `place_ptr_rel cenv cx s
    (PlaceR (StoragePlace tr (slot + n2w (Num i * type_slot_size etv)) etv))
    (slot + val_to_w256 iv * n2w (type_slot_size etv)) loc (Type et)` by
    (fs[place_ptr_rel_def, word_mul_n2w]) >>
  `place_readable cx ef
    (PlaceR (StoragePlace tr (slot + n2w (Num i * type_slot_size etv)) etv)) /\
   target_ptr_ok cenv
    (PlaceR (StoragePlace tr (slot + n2w (Num i * type_slot_size etv)) etv))
    (bop,loc,SOME (value_type_place (Type et))) G tn s` by
    fs[place_readable_def, target_ptr_ok_def] >>
  gvs[value_type_place_def] >>
  drule_all (SRULE [value_type_place_def, arithmeticTheory.ADD_COMM]
    (Q.INST [`ty` |-> `Type et`] target_fixed_array_continue_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Resume target_fixed_slot_array_continue_ptr[abort]:
  gvs[] >>
  `!x. idx = Var x ==> not_fresh_at sn x` by fs[copy_old_operand_def] >>
  drule_all target_fixed_array_abort_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Finalise target_fixed_slot_array_continue_ptr
