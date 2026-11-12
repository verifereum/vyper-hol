Theory bodyPtrStructLitOwnershipUint2str
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinStrings context compileEnv

Theorem alloc_run_compile_uint2str:
  alloc_run fresh_outputs (compile_uint2str op digits buf_size) (\v s. fresh_outputs s)
Proof
  simp[compile_uint2str_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\x s. fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac >- simp[alloc_run_fresh_var_fresh] >>
  qx_gen_tac `val_var` >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s /\ not_fresh_at s val_var /\ ~alloc_owned s val_var` >>
  reverse conj_tac >- simp[alloc_run_assign_reserved] >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >>
  qexists `\x s. (fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x) /\
    not_fresh_at s val_var /\ ~alloc_owned s val_var` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_frame_reserved >> simp[alloc_run_fresh_var_fresh]) >>
  qx_gen_tac `i_var` >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\v s. (fresh_outputs s /\ not_fresh_at s i_var /\ ~alloc_owned s i_var) /\
    not_fresh_at s val_var /\ ~alloc_owned s val_var` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_frame_reserved >> simp[alloc_run_assign_reserved]) >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >>
  qexists `\x s. ((fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x) /\
    not_fresh_at s i_var /\ ~alloc_owned s i_var) /\
    not_fresh_at s val_var /\ ~alloc_owned s val_var` >>
  reverse conj_tac
  >- (ntac 2 (ho_match_mp_tac alloc_run_frame_reserved) >>
      simp[alloc_run_fresh_var_fresh]) >>
  qx_gen_tac `result_var` >> simp[comp_ignore_bind_def] >>
  suspend "blocks"
QED

Resume alloc_run_compile_uint2str[blocks]:
  rpt (irule alloc_run_bind >>
    qexists `\v s. ((fresh_outputs s /\ not_fresh_at s result_var /\ ~alloc_owned s result_var) /\
      not_fresh_at s i_var /\ ~alloc_owned s i_var) /\
      not_fresh_at s val_var /\ ~alloc_owned s val_var` >>
    reverse conj_tac
    >- FIRST [
      ntac 2 (ho_match_mp_tac alloc_run_frame_reserved) >>
        simp[alloc_run_assign_reserved] >> NO_TAC,
      ho_match_mp_tac alloc_run_frame_reserved >>
        irule alloc_run_conseq >>
        irule_at Any alloc_run_frame_reserved >>
        irule_at Any alloc_run_assign_reserved >> simp[] >>
        qexists `result_var` >> simp[] >> NO_TAC,
      irule alloc_run_conseq >>
        irule_at Any alloc_run_frame_reserved >>
        irule_at Any alloc_run_frame_reserved >>
        irule_at Any alloc_run_assign_reserved >> simp[] >>
        qexistsl [`result_var`, `i_var`] >> simp[] >> NO_TAC,
      ntac 3 (ho_match_mp_tac alloc_run_frame_reserved) >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_fresh_label_fresh] >> NO_TAC] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Finalise alloc_run_compile_uint2str
