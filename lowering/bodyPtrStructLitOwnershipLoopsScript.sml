Theory bodyPtrStructLitOwnershipLoops
Ancestors bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps context compileEnv venomInst list

Theorem alloc_run_compile_zero_memory_loop:
  !ptr i words. alloc_run fresh_outputs (compile_zero_memory_loop ptr i words)
    (\u st. fresh_outputs st)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_zero_memory_loop_def] >>
  Cases_on `i >= words`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  reverse conj_tac
  >- (Cases_on `i = 0`
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >>
  gen_tac >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  fs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_zero_memory:
  !size. alloc_run fresh_outputs (compile_zero_memory ptr_op size)
    (\u st. fresh_outputs st)
Proof
  Cases
  >- simp[compile_zero_memory_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  simp[compile_zero_memory_def, alloc_run_compile_zero_memory_loop]
QED

Theorem alloc_run_assign_reserved:
  alloc_run (\st. fresh_outputs st /\ not_fresh_at st x /\ ~alloc_owned st x)
    (emit_inst ASSIGN ops [x])
    (\u st. fresh_outputs st /\ not_fresh_at st x /\ ~alloc_owned st x)
Proof
  irule alloc_run_conseq >>
  irule_at Any alloc_run_frame_reserved >>
  irule_at Any alloc_run_emit_inst_fresh >> simp[] >> qexists `x` >> simp[]
QED

Theorem alloc_run_emit_empty_fresh:
  opc <> ALLOCA ==>
  alloc_run fresh_outputs (emit_inst opc ops []) (\u st. fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_emit_inst_fresh >> simp[]
QED

Theorem alloc_run_word_copy_offset[local]:
  alloc_run fresh_outputs
    (if scale = 1 then emit_op ADD [op; Var counter]
     else do scaled <- emit_op MUL [Var counter; Lit (n2w scale)];
             emit_op ADD [op; scaled] od)
    (\v st. fresh_outputs st)
Proof
  Cases_on `scale = 1` >> simp[alloc_run_emit_op_fresh] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_word_copy_loop_base:
  alloc_run fresh_outputs
    (compile_word_copy_loop_base src_op dst_op count_op load_loc store_loc
       is_ctor imm)
    (\u st. fresh_outputs st)
Proof
  simp[compile_word_copy_loop_base_def, comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >>
  qexists `\x st. fresh_outputs st /\ not_fresh_at st x /\ ~alloc_owned st x` >>
  reverse conj_tac >- simp[SF ETA_ss, alloc_run_fresh_var_fresh] >>
  qx_gen_tac `counter` >> simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >>
    qexists `\v st. fresh_outputs st /\ not_fresh_at st counter /\
                      ~alloc_owned st counter` >>
    reverse conj_tac
    >- FIRST [simp[alloc_run_assign_reserved] >> NO_TAC,
        ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_compile_ptr_load,
          SRULE [SF ETA_ss] alloc_run_compile_ptr_store,
          SRULE [SF ETA_ss] alloc_run_word_copy_offset] >> NO_TAC] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  irule alloc_run_conseq >>
  irule_at Any alloc_run_new_block_fresh >> simp[]
QED

Theorem alloc_run_compile_word_copy_loop:
  alloc_run fresh_outputs
    (compile_word_copy_loop src_op dst_op word_count load_loc store_loc is_ctor)
    (\u st. fresh_outputs st)
Proof
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       alloc_run_compile_word_copy_loop_base]
QED

Theorem alloc_run_compile_storage_to_memory:
  alloc_run fresh_outputs (compile_storage_to_memory slot buf words)
    (\u st. fresh_outputs st)
Proof simp[compile_storage_to_memory_def, alloc_run_compile_word_copy_loop]
QED

Theorem alloc_run_compile_memory_to_storage:
  alloc_run fresh_outputs (compile_memory_to_storage buf slot words)
    (\u st. fresh_outputs st)
Proof simp[compile_memory_to_storage_def, alloc_run_compile_word_copy_loop]
QED

Theorem alloc_run_compile_transient_to_memory:
  alloc_run fresh_outputs (compile_transient_to_memory slot buf words)
    (\u st. fresh_outputs st)
Proof simp[compile_transient_to_memory_def, alloc_run_compile_word_copy_loop]
QED

Theorem alloc_run_compile_memory_to_transient:
  alloc_run fresh_outputs (compile_memory_to_transient buf slot words)
    (\u st. fresh_outputs st)
Proof simp[compile_memory_to_transient_def, alloc_run_compile_word_copy_loop]
QED

Theorem alloc_run_compile_slot_to_memory:
  alloc_run fresh_outputs (compile_slot_to_memory slot buf words loc)
    (\u st. fresh_outputs st)
Proof simp[compile_slot_to_memory_def, alloc_run_compile_word_copy_loop]
QED

Theorem alloc_run_compile_code_to_memory:
  alloc_run fresh_outputs (compile_code_to_memory off dst words)
    (\u st. fresh_outputs st)
Proof
  Cases_on `words = 0`
  >- simp[compile_code_to_memory_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  simp[compile_code_to_memory_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u st. fresh_outputs st` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_word_copy_loop] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
