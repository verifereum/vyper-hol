Theory bodyPtrPopTargetSimDynamicSlot
Ancestors
  bodyPtrPopTargetSimArrayContinue bodyPtrPopTargetSimArraySource
  bodyPtrPopTargetSimArraySlot bodyPtrPopTargetDefs bodyPtrPopTargetSimStorageHeader
  exprLowering loweringPosts compileEnv words list vyperStorageBackend vyperValue

Theorem target_live_dynamic_slot_array_continue_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] sn = (Var out,sl) /\
  array_bounds_check idx (Var out) (is_signed_type ity) sl = ((),sm) /\
  array_elem_ptr bop idx T 1 (type_slot_size etv) sm = (dst,sb) /\
  fn_has_code sn sl fn /\ fn_has_code sl sb fn /\ fn_has_code sl sm fn /\
  eval_operand bop s = SOME slot /\ eval_operand idx s = SOME (val_to_w256 iv) /\
  copy_old_operand sn bop /\ copy_old_operand sn idx /\ op_prov G bop = NONE /\ op_taint tn bop = {} /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV etv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  slots_in_range (get_storage cx ef tr) (w2n slot) (ArrayTV etv (Dynamic cap)) /\
  storage_read_live cx tr (get_storage cx ef tr) slot (ArrayTV etv (Dynamic cap)) /\
  is_int_type ity /\ evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv iv /\
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
    slot loc (Type (ArrayT et (Dynamic cap))) /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
    (bop,loc,SOME (ValPT (ArrayT et (Dynamic cap)))) G tn s ==>
  (?child. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
     (ValueSubscript iv) ef = (INL child,ef) /\
   ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
     target_post ctx fn cenv cx es sa sb s0 ef child (Type et) (dst,loc,SOME (ValPT et)) t /\
     ghost_inv d cenv cx ef H un t /\
     target_ptr_ok cenv child (dst,loc,SOME (ValPT et)) H un t /\
     ghost_kept cenv es sa G0 tn0 s0 H un /\
     t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
  (?msg. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
     (ValueSubscript iv) ef = (INR (Error (RuntimeError msg)),ef) /\
   ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
     (Abort Revert_abort (t with vs_inst_idx := pc)))
Proof
  strip_tac >>
  `(if tr then tload slot s else sload slot s) = lookup_storage slot (get_storage cx ef tr)` by
    (irule target_storage_header_value >> conj_tac
     >- (qexists_tac `ArrayTV etv (Dynamic cap)` >> simp[type_slot_size_def]) >>
     metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`bd` |-> `Dynamic cap`, `es` |-> `ef`,
    `len` |-> `w2n (lookup_storage slot (get_storage cx ef tr))`]
    target_typed_storage_array_extend)) >> strip_tac >>
  Cases_on `idx_in_range (is_signed_type ity) (val_to_w256 iv)
    (lookup_storage slot (get_storage cx ef tr))`
  >- suspend "success" >> suspend "abort"
QED

Resume target_live_dynamic_slot_array_continue_ptr[success]:
  fs[] >>
  `place_ptr_rel cenv cx s
    (PlaceR (StoragePlace tr (slot + n2w (1 + Num i * type_slot_size etv)) etv))
    ((slot+1w) + val_to_w256 iv * n2w (type_slot_size etv)) loc (Type et)` by
    fs[place_ptr_rel_def, GSYM word_mul_n2w, GSYM word_add_n2w,
       AC WORD_ADD_ASSOC WORD_ADD_COMM] >>
  `place_readable cx ef
    (PlaceR (StoragePlace tr (slot + n2w (1 + Num i * type_slot_size etv)) etv)) /\
   target_ptr_ok cenv
    (PlaceR (StoragePlace tr (slot + n2w (1 + Num i * type_slot_size etv)) etv))
    (bop,loc,SOME (value_type_place (Type et))) G tn s` by
    fs[place_readable_def, target_ptr_ok_def] >>
  gvs[value_type_place_def] >>
  `idx_in_range (is_signed_type ity) (n2w (Num i))
    (if tr then tload slot s else sload slot s)` by fs[] >>
  drule_all (SRULE [value_type_place_def]
    (Q.INST [`ty` |-> `Type et`] target_dynamic_slot_array_continue_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Resume target_live_dynamic_slot_array_continue_ptr[abort]:
  gvs[] >>
  `~idx_in_range (is_signed_type ity) (val_to_w256 (IntV i))
    (if tr then tload slot s else sload slot s)` by simp[] >>
  drule_all target_dynamic_slot_array_abort_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Finalise target_live_dynamic_slot_array_continue_ptr
