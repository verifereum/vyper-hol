Theory bodyPtrStructLitOwnershipMembership
Ancestors bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  exprLowering context compileEnv

Theorem alloc_run_membership_offset[local]:
  alloc_run fresh_outputs
    (if offset_base > 0 then emit_op ADD [Lit (n2w offset_base); idx_offset]
     else return idx_offset) (\v s. fresh_outputs s)
Proof
  Cases_on `offset_base > 0`
  >- simp[alloc_run_emit_op_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_membership_return[local]:
  alloc_run fresh_outputs (return v) (\u s. fresh_outputs s)
Proof simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_array_membership_loop:
  (!op. alloc_run fresh_outputs (loader op) (\v s. fresh_outputs s)) ==>
  alloc_run fresh_outputs
    (compile_array_membership_loop needle arr len elem_size offset_base loader
       bound_opt is_in)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `bound_opt` >>
  simp[compile_array_membership_loop_def, comp_ignore_bind_def, comp_bind_assoc] >>
  (irule alloc_run_bind >>
  qexists `\x s. fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac >- simp[alloc_run_fresh_var_fresh] >>
  qx_gen_tac `result_var` >> simp[] >>
  ntac 8 (irule alloc_run_bind >>
    qexists `\v s. fresh_outputs s /\ not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
    reverse conj_tac
    >- (ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh]) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  irule alloc_run_bind >>
  qexists `\x s. (fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x) /\
                       not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_frame_reserved >>
      simp[alloc_run_fresh_var_fresh]) >>
  qx_gen_tac `idx_var` >> simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >>
    qexists `\v s. (fresh_outputs s /\ not_fresh_at s idx_var /\ ~alloc_owned s idx_var) /\
                         not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
    reverse conj_tac
    >- FIRST [
      ho_match_mp_tac alloc_run_frame_reserved >>
        simp[alloc_run_assign_reserved] >> NO_TAC,
      irule alloc_run_conseq >>
        irule_at Any alloc_run_frame_reserved >>
        irule_at Any alloc_run_assign_reserved >> simp[] >>
        qexists `idx_var` >> simp[] >> NO_TAC,
      ho_match_mp_tac alloc_run_frame_reserved >>
        ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_membership_offset] >> NO_TAC,
      ho_match_mp_tac alloc_run_frame_reserved >>
        ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_membership_return] >> NO_TAC] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  Cases_on `is_in`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_emit_op_fresh >> simp[])
QED

Theorem alloc_run_compile_var_array_membership:
  alloc_run fresh_outputs
    (compile_var_array_membership ce needle arr_vv rhs_ty is_in)
    (\v s. fresh_outputs s)
Proof
  simp[compile_var_array_membership_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (Cases_on `rhs_ty` >> simp[alloc_run_membership_return] >>
      Cases_on `b` >> simp[alloc_run_compile_ptr_load, alloc_run_membership_return]) >>
  gen_tac >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_array_membership_loop,
       SRULE [SF ETA_ss] alloc_run_compile_ptr_load]
QED
