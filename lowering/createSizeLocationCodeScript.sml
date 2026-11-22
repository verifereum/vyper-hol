(* Static branch confinement for copying and materializing locations. *)
Theory createSizeLocationCode
Ancestors
  createSizeCutOpens createSizeCutCode exprLowering context
  compileEnv emitHelper venomInst pair option pred_set

fun location_cut_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_inst,
                  create_cut_code_emit_op, create_cut_code_emit_void,
                  create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac, IF_CASES_TAC]);

Theorem create_location_imm_load[local,simp]:
  create_cut_code exits a (SND (compile_imm_load_word ctor imm op a))
Proof
  Cases_on `imm` >> location_cut_steps [compile_imm_load_word_def]
QED

Theorem create_location_imm_store[local,simp]:
  create_cut_code exits a (SND (compile_imm_store_word imm op v a))
Proof
  Cases_on `imm` >> location_cut_steps [compile_imm_store_word_def]
QED

(* Keep the set of guaranteed openings unchanged across straight-line steps. *)
val location_cut_prepend =
  SIMP_RULE (srw_ss()) [] (Q.INST [`opened1` |-> `{}`] create_cut_opens_bind);

Theorem create_location_close_loop[local]:
  !h b x. create_cut_code {h;b;x} a t /\
  ({h} UNION ({b} UNION {x})) SUBSET set (added_labels a t) ==>
  create_cut_code {} a t
Proof
  rpt gen_tac >> strip_tac >> irule create_cut_opens_close >>
  qexistsl_tac [`{h} UNION ({b} UNION {x})`, `{h;b;x}`] >> simp[]
QED

Theorem create_word_copy_cut_code:
  create_cut_code {} a
    (SND (compile_word_copy_loop_base src dst count_op ll sl ctor imm a))
Proof
  simp[compile_word_copy_loop_base_def, LET_DEF, comp_ignore_bind_def] >>
  map_every (fn l => match_mp_tac create_cut_code_bind_all >>
    (conj_tac >- simp[]) >> qx_gen_tac l >> gen_tac >> BETA_TAC)
    [`h`, `b`, `x`, `ctr`] >>
  match_mp_tac create_cut_code_bind_all >>
  (conj_tac >- simp[create_cut_code_emit_inst, create_cut_targets_def]) >>
  rpt gen_tac >> BETA_TAC >>
  qspecl_then [`h`, `b`, `x`] match_mp_tac create_location_close_loop >>
  match_mp_tac location_cut_prepend >>
  (conj_tac >- simp[create_cut_code_emit_inst, create_cut_targets_def]) >> BETA_TAC >>
  match_mp_tac create_cut_opens_bind >>
  (conj_tac >- irule create_cut_opens_block) >> BETA_TAC >>
  match_mp_tac location_cut_prepend >>
  (conj_tac >- location_cut_steps []) >> BETA_TAC >>
  match_mp_tac location_cut_prepend >>
  (conj_tac >- (qmatch_goalsub_rename_tac `emit_inst JNZ [cond;_;_] [] _` >>
                Cases_on `cond` >> irule create_cut_code_emit_inst >>
                simp[create_cut_targets_def, DISJ_IMP_THM])) >> BETA_TAC >>
  match_mp_tac create_cut_opens_bind >>
  (conj_tac >- irule create_cut_opens_block) >> BETA_TAC >>
  rpt (match_mp_tac location_cut_prepend >>
    (conj_tac >- FIRST [
       rename1 `create_cut_code _ _ (SND (compile_ptr_load _ _ loc _ _))` >>
         Cases_on `loc` >> location_cut_steps [compile_ptr_load_def],
       rename1 `create_cut_code _ _ (SND (compile_ptr_store _ _ loc _ _ _))` >>
         Cases_on `loc` >> location_cut_steps [compile_ptr_store_def],
       location_cut_steps []]) >> BETA_TAC) >>
  irule create_cut_opens_block
QED

Theorem create_location_byte_offset[local,simp]:
  create_cut_code exits a (SND (compile_lit_byte_offset op off a))
Proof
  Cases_on `op` >> location_cut_steps [compile_lit_byte_offset_def]
QED

Theorem create_imm_copy_cut_code:
  !n off a. create_cut_code {} a
    (SND (compile_imm_copy_to_memory ctor imm src dst n off a))
Proof
  Induct >> location_cut_steps [compile_imm_copy_to_memory_def] >>
  rpt gen_tac >> location_cut_steps [compile_imm_copy_to_memory_def]
QED

Theorem create_slot_to_memory_cut_code:
  create_cut_code {} a (SND (compile_slot_to_memory src dst n loc a))
Proof
  simp[compile_slot_to_memory_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def, create_word_copy_cut_code]
QED

Theorem create_ensure_in_memory_cut_code:
  create_cut_code {} a (SND (compile_ensure_in_memory op loc bytes n ctor imm a))
Proof
  Cases_on `loc` >>
  location_cut_steps [compile_ensure_in_memory_def, compile_alloc_buffer_def,
                      compile_storage_to_memory_def, compile_transient_to_memory_def,
                      compile_word_copy_loop_def, compile_word_copy_loop_op_def,
                      create_word_copy_cut_code, create_imm_copy_cut_code]
QED

Theorem create_unwrap_cut_code:
  create_cut_code {} a (SND (unwrap_value ce vv a))
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >>
  Cases_on `p.ptr_location` >>
  location_cut_steps [compile_ptr_load_def, create_ensure_in_memory_cut_code]
QED
