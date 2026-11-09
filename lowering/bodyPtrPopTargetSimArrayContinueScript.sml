Theory bodyPtrPopTargetSimArrayContinue
Ancestors
  bodyPtrPopTargetSimPost bodyPtrPopTargetSimArraySource
  bodyPtrPopTargetSimArrayCase bodyPtrPopTargetSimArraySlot
  targetPlaceSimCasesBase exprSimCopy compileEnv venomState
  loweringPosts ptrDiscipline finite_map list

(* Fixed-array suffix, with the original starting frame and full target post.
   Source selection supplies child layout/readability at the post-index state. *)
Theorem target_fixed_array_continue_ptr:
  compile_array_subscript bop idx F cnt ws esz sgn loader sn = (dst,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  copy_old_operand sn bop /\ copy_old_operand sn idx /\ idx_in_range sgn i (n2w cnt) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\ op_taint tn bop = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  place_ptr_rel cenv cx s child (b+i*n2w esz) loc ty /\
  place_readable cx ef child /\ target_ptr_ok cenv child (bop,loc,SOME (value_type_place ty)) G tn s ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    target_post ctx fn cenv cx es sa sb s0 ef child ty
      (dst,loc,SOME (value_type_place ty)) t /\
    ghost_inv d cenv cx ef H un t /\
    target_ptr_ok cenv child (dst,loc,SOME (value_type_place ty)) H un t /\
    ghost_kept cenv es sa G0 tn0 s0 H un /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sn sb)
Proof
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at sn x) /\
   (!x. idx = Var x ==> not_fresh_at sn x)` by fs[copy_old_operand_def] >>
  drule_all target_fixed_array_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sn sb)` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >>
  `!x. dst = Var x ==> not_fresh_at sb x` by fs[copy_old_operand_def] >>
  `place_ptr_rel cenv cx t child (b+i*n2w esz) loc ty` by
    (irule place_ptr_rel_vars_frame >> qexistsl_tac [`s`, `sn`] >> simp[]) >>
  irule target_readonly_suffix_post_ptr >> simp[] >>
  qexistsl_tac [`G`, `s.vs_inst_idx + LENGTH (emitted_insts sn sb)`,
    `(bop,loc,SOME (value_type_place ty))`, `s`, `sn`, `tn`] >> simp[]
QED

Theorem target_dynamic_slot_array_continue_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] sn = (Var out,sl) /\
  array_bounds_check idx (Var out) sgn sl = ((),sm) /\
  array_elem_ptr bop idx T 1 esz sm = (dst,sb) /\
  fn_has_code sn sl fn /\ fn_has_code sl sb fn /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  copy_old_operand sn bop /\ copy_old_operand sn idx /\ idx_in_range sgn i (if tr then tload b s else sload b s) /\
  op_prov G bop = NONE /\ op_taint tn bop = {} /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) b = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  place_ptr_rel cenv cx s child ((b+1w)+i*n2w esz) loc ty /\
  place_readable cx ef child /\ target_ptr_ok cenv child (bop,loc,SOME (value_type_place ty)) G tn s ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    target_post ctx fn cenv cx es sa sb s0 ef child ty
      (dst,loc,SOME (value_type_place ty)) t /\
    ghost_inv d cenv cx ef H un t /\
    target_ptr_ok cenv child (dst,loc,SOME (value_type_place ty)) H un t /\
    ghost_kept cenv es sa G0 tn0 s0 H un /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all target_dynamic_slot_array_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >>
  `!x. dst = Var x ==> not_fresh_at sb x` by fs[copy_old_operand_def] >>
  `place_ptr_rel cenv cx t child ((b+1w)+i*n2w esz) loc ty` by
    (irule place_ptr_rel_vars_frame >> qexistsl_tac [`s`, `sn`] >> simp[]) >>
  irule target_readonly_suffix_post_ptr >> simp[] >>
  qexistsl_tac [`G`, `LENGTH sb.cs_current_insts`,
    `(bop,loc,SOME (value_type_place ty))`, `s`, `sn`, `tn`] >> simp[]
QED

Theorem target_dynamic_memory_array_continue_ptr:
  emit_op MLOAD [Var src] sn = (Var out,sl) /\
  array_bounds_check idx (Var out) sgn sl = ((),sm) /\
  array_elem_ptr (Var src) idx T 32 esz sm = (dst,sb) /\
  fn_has_code sn sl fn /\ fn_has_code sl sb fn /\
  lookup_var src s = SOME b /\ eval_operand idx s = SOME i /\
  not_fresh_at sn src /\ copy_old_operand sn idx /\ idx_in_range sgn i (mload (w2n b) s) /\
  ptr_covers G tn src s bytes /\ 32 <= bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) mem) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\ op_taint tn (Var src) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  wb_frame cenv es sa s0 s /\
  stmt_state_rel ctx fn cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  place_ptr_rel cenv cx s child ((b+32w)+i*n2w esz) loc ty /\
  place_readable cx ef child /\ target_ptr_ok cenv child (Var src,loc,SOME (value_type_place ty)) G tn s ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    target_post ctx fn cenv cx es sa sb s0 ef child ty
      (dst,loc,SOME (value_type_place ty)) t /\
    ghost_inv d cenv cx ef H un t /\
    target_ptr_ok cenv child (dst,loc,SOME (value_type_place ty)) H un t /\
    ghost_kept cenv es sa G0 tn0 s0 H un /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all target_dynamic_memory_array_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >>
  `!x. dst = Var x ==> not_fresh_at sb x` by fs[copy_old_operand_def] >>
  `place_ptr_rel cenv cx t child ((b+32w)+i*n2w esz) loc ty` by
    (irule place_ptr_rel_vars_frame >> qexistsl_tac [`s`, `sn`] >> simp[]) >>
  irule target_readonly_suffix_post_ptr >> simp[] >>
  qexistsl_tac [`G`, `LENGTH sb.cs_current_insts`,
    `(Var src,loc,SOME (value_type_place ty))`, `s`, `sn`, `tn`] >> simp[]
QED
