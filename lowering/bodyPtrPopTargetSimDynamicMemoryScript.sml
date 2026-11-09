Theory bodyPtrPopTargetSimDynamicMemory
Ancestors
  bodyPtrPopTargetSimArrayContinue bodyPtrPopTargetSimArraySource
  bodyPtrPopTargetSimArrayCase bodyPtrPopTargetDefs
  typedCopyLayoutPtr valueEncodingProps bodyPtrDefs
  exprLowering loweringPosts compileEnv words list

Theorem target_live_dynamic_memory_array_continue_ptr:
  emit_op MLOAD [Var src] sn = (Var out,sl) /\
  array_bounds_check idx (Var out) (is_signed_type ity) sl = ((),sm) /\
  array_elem_ptr (Var src) idx T 32 (type_memory_size etv) sm = (dst,sb) /\
  fn_has_code sn sl fn /\ fn_has_code sl sb fn /\ fn_has_code sl sm fn /\
  lookup_var src s = SOME b /\ eval_operand idx s = SOME (val_to_w256 iv) /\
  not_fresh_at sn src /\ copy_old_operand sn idx /\ ptr_covers G tn src s bytes /\ 32 <= bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) mem) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\ op_taint tn (Var src) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  lookup_scopes id ef.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV etv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  is_int_type ity /\ evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv iv /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b loc (Type (ArrayT et (Dynamic cap))) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (Var src,loc,SOME (ValPT (ArrayT et (Dynamic cap)))) G tn s ==>
  (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) ef =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))),ef) /\
   ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
     target_post ctx fn cenv cx es sa sb s0 ef
       (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))) (Type et)
       (dst,loc,SOME (ValPT et)) t /\
     ghost_inv d cenv cx ef H un t /\
     target_ptr_ok cenv (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
       (dst,loc,SOME (ValPT et)) H un t /\ ghost_kept cenv es sa G0 tn0 s0 H un /\
     t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
  (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) ef =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),ef) /\
   ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
     (Abort Revert_abort (t with vs_inst_idx := pc)))
Proof
  strip_tac >>
  `mload (w2n b) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
  drule_all target_live_memory_array_extend >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  Cases_on `idx_in_range (is_signed_type ity) (val_to_w256 iv) (n2w (LENGTH vs))`
  >- suspend "success" >> suspend "abort"
QED

Resume target_live_dynamic_memory_array_continue_ptr[success]:
  fs[vyperValueOperationTheory.array_length_def] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
    ((b+32w) + val_to_w256 iv * n2w (type_memory_size etv)) loc (Type et)` by
    (drule_all target_memory_child_layout >>
     simp[GSYM word_mul_n2w, GSYM word_add_n2w, AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv])))
    (Var src,loc,SOME (value_type_place (Type et))) G tn s` by
    fs[target_ptr_ok_def] >>
  gvs[value_type_place_def] >>
  `idx_in_range (is_signed_type ity) (n2w (Num i)) (mload (w2n b) s)` by simp[] >>
  drule_all (SRULE [value_type_place_def]
    (Q.INST [`ty` |-> `Type et`] target_dynamic_memory_array_continue_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Resume target_live_dynamic_memory_array_continue_ptr[abort]:
  gvs[vyperValueOperationTheory.array_length_def] >>
  metis_tac[target_dynamic_memory_array_abort_ptr]
QED

Finalise target_live_dynamic_memory_array_continue_ptr
