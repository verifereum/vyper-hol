(* Memory writes, freshness on re-entry, and exact allocated footprints. *)
Theory abiEncoderWrites
Ancestors
  arithmetic
  pred_set
  finite_map
  valueEncodingProps
  abiDecoderContract abiDecoderDynamicLoopSetup emitHelperProps exprLoweringProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list

Theorem abi_encoder_write_observations[simp]:
  (mstore p w s).vs_call_ctx = s.vs_call_ctx /\
  (mstore p w s).vs_data_section = s.vs_data_section /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (mcopy db sb cnt s).vs_call_ctx = s.vs_call_ctx /\
  (mcopy db sb cnt s).vs_data_section = s.vs_data_section /\
  (mcopy db sb cnt s).vs_allocas = s.vs_allocas /\
  (mcopy db sb cnt s).vs_alloca_next = s.vs_alloca_next /\
  (mcopy db sb cnt s).vs_halted = s.vs_halted
Proof
  simp[mcopy_def, mstore_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem abi_encoder_emit_store:
  emit_void MSTORE [ptr_op;value_op] st = ((),st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore p w s) /\
  fresh_vars_wrt limit_st (mstore p w s) /\ inst_extends st st'
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    exec_write2_def, mk_inst_def, w2n_n2w] >>
  fs[fresh_vars_wrt_def, lookup_var_def, mstore_def]
QED

Theorem abi_encoder_emit_copy:
  emit_void MCOPY [dst;src;len] st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\
  db < dimword (:256) /\ sb < dimword (:256) /\ cnt < dimword (:256) /\
  fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mcopy db sb cnt s) /\
  fresh_vars_wrt limit_st (mcopy db sb cnt s) /\ inst_extends st st'
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def, mk_inst_def, w2n_n2w] >>
  fs[fresh_vars_wrt_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Definition encoder_exact_writes_def:
  encoder_exact_writes ids d n (s:venom_state) (t:venom_state) <=>
    !a. (a < d \/ d+n <= a) /\
        (!id p sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
                   a < p \/ p+sz <= a) ==>
        mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
End

Theorem encoder_exact_registered_mstore:
  id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  encoder_exact_writes ids d n s (mstore p w s)
Proof
  rw[encoder_exact_writes_def] >>
  `a < p \/ p+32 <= a` by
    (first_x_assum irule >> simp[abi_encoder_write_observations] >>
     qexists_tac `id` >> simp[]) >>
  irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem encoder_exact_registered_step:
  id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,32) /\
  p+32 < dimword (:256) /\ eval_operand cell_op s = SOME (n2w p) /\
  eval_operand value s = SOME w ==>
  step_inst_base (mk_inst site MSTORE [cell_op;value] []) s =
    OK (mstore p w s) /\
  encoder_exact_writes ids d n s (mstore p w s)
Proof
  strip_tac >> conj_tac
  >- (qspecl_then [`cell_op`, `value`] mp_tac step_MSTORE >>
      simp[] >> disch_then (qspecl_then [`n2w p`, `w`, `site`, `s`] mp_tac) >>
      simp[]) >>
  irule encoder_exact_registered_mstore >> metis_tac[]
QED

(* Earlier allowed cells must remain registered in the final endpoint. *)
Theorem encoder_exact_writes_trans:
  encoder_exact_writes ids d n s t /\ encoder_exact_writes ids d n t u /\
  (!id slot. id IN ids /\ FLOOKUP t.vs_allocas id = SOME slot ==>
             FLOOKUP u.vs_allocas id = SOME slot) ==>
  encoder_exact_writes ids d n s u
Proof
  pure_rewrite_tac[encoder_exact_writes_def] >> rpt strip_tac >>
  `!id p sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
             a < p \/ p+sz <= a` by metis_tac[] >>
  metis_tac[]
QED

(* Output subwindows are justified by interval containment, not a reserve. *)
Theorem encoder_exact_writes_subwindow:
  d <= c /\ c+k <= d+n /\ encoder_exact_writes ids c k s t ==>
  encoder_exact_writes ids d n s t
Proof
  pure_rewrite_tac[encoder_exact_writes_def] >> rpt strip_tac >>
  `a < c \/ c+k <= a` by decide_tac >> metis_tac[]
QED

Theorem encoder_exact_output_mstore:
  d <= p /\ p+32 <= d+n ==>
  encoder_exact_writes ids d n s (mstore p w s)
Proof
  rw[encoder_exact_writes_def] >>
  irule mstore_mem_bytes_at_disjoint >> simp[] >> decide_tac
QED

(* A dynamic head occupies one word. Descriptor admissibility alone does
   not constrain h: the source input's ABI head-size equality and dynamic
   flag supply h = 32 (encoder_dynamic_input_head_size in abiEncoderInput).
   pre and post are the encoded lengths before and after this child. *)
Theorem encoder_dynamic_iteration_bounds:
  i = LENGTH pre /\ num_elems = LENGTH pre + 1 + LENGTH post /\
  32 <= h /\ off = num_elems*h + SUM pre /\
  out_len = 32 + num_elems*h + SUM pre + child_len + SUM post ==>
  d <= d+32+i*h /\ d+32+i*h+32 <= d+out_len /\
  d <= d+32+off /\ d+32+off+child_len <= d+out_len
Proof
  strip_tac >>
  `num_elems*h = i*h + h + LENGTH post*h` by
    (gvs[] >> simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]) >>
  decide_tac
QED

(* One child invocation is abstract: its precise effect must concern this
   very endpoint t. Repeated scratch writes reuse persistent registrations. *)
Theorem encoder_dynamic_iteration_exact:
  i = LENGTH pre /\ num_elems = LENGTH pre + 1 + LENGTH post /\
  32 <= h /\ off = num_elems*h + SUM pre /\
  out_len = 32 + num_elems*h + SUM pre + child_len + SUM post /\
  d+out_len < dimword (:256) /\
  encoder_exact_writes ids (d+32+off) child_len s t /\
  (!id slot. id IN ids /\ FLOOKUP s.vs_allocas id = SOME slot ==>
             FLOOKUP t.vs_allocas id = SOME slot) /\
  dyn_id IN ids /\ idx_id IN ids /\
  FLOOKUP s.vs_allocas dyn_id = SOME (dyn_p,32) /\
  FLOOKUP s.vs_allocas idx_id = SOME (idx_p,32) ==>
  encoder_exact_writes ids d out_len s
    (mstore idx_p (n2w (i+1))
      (mstore dyn_p (n2w (off+child_len))
        (mstore (d+32+i*h) (n2w off) t)))
Proof
  strip_tac >>
  `d <= d+32+i*h /\ d+32+i*h+32 <= d+out_len /\
   d <= d+32+off /\ d+32+off+child_len <= d+out_len` by
    (irule encoder_dynamic_iteration_bounds >> metis_tac[]) >>
  `encoder_exact_writes ids d out_len s t` by
    (irule encoder_exact_writes_subwindow >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas dyn_id = SOME (dyn_p,32) /\
   FLOOKUP t.vs_allocas idx_id = SOME (idx_p,32)` by metis_tac[] >>
  irule encoder_exact_writes_trans >> qexists_tac `t` >> simp[] >>
  irule encoder_exact_writes_trans >>
  qexists_tac `mstore (d+32+i*h) (n2w off) t` >>
  simp[abi_encoder_write_observations] >>
  conj_tac >- (irule encoder_exact_output_mstore >> gvs[]) >>
  irule encoder_exact_writes_trans >>
  qexists_tac `mstore dyn_p (n2w (off+child_len))
                (mstore (d+32+i*h) (n2w off) t)` >>
  simp[abi_encoder_write_observations] >>
  conj_tac >> irule encoder_exact_registered_mstore >>
  simp[abi_encoder_write_observations] >> metis_tac[]
QED

(* The three post-child stores at the generated body's addresses. Operand
   facts are intentionally separate from the exact-effect premise. *)
Theorem encoder_dynamic_iteration_stores:
  d+32+i*h+32 < dimword (:256) /\
  dyn_p+32 < dimword (:256) /\ idx_p+32 < dimword (:256) /\
  u = mstore (d+32+i*h) (n2w off) t /\
  v = mstore dyn_p (n2w (off+child_len)) u /\
  eval_operand head_op t = SOME (n2w (d+32+i*h)) /\
  eval_operand offset_op t = SOME (n2w off) /\
  eval_operand dyn_op u = SOME (n2w dyn_p) /\
  eval_operand next_dyn_op u = SOME (n2w (off+child_len)) /\
  eval_operand idx_op v = SOME (n2w idx_p) /\
  eval_operand next_idx_op v = SOME (n2w (i+1)) ==>
  step_inst_base (mk_inst hsite MSTORE [head_op;offset_op] []) t = OK u /\
  step_inst_base (mk_inst dsite MSTORE [dyn_op;next_dyn_op] []) u = OK v /\
  step_inst_base (mk_inst isite MSTORE [idx_op;next_idx_op] []) v =
    OK (mstore idx_p (n2w (i+1)) v)
Proof
  strip_tac >>
  simp[step_inst_base_def, exec_write2_def] >> gvs[]
QED

Theorem encoder_registered_cell_initialization_and_repeat:
  id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  encoder_exact_writes ids d n s (mstore p w2 (mstore p w1 s))
Proof
  strip_tac >> irule encoder_exact_writes_trans >>
  qexists_tac `mstore p w1 s` >> simp[NoAsms, abi_encoder_write_observations] >>
  conj_tac >> irule encoder_exact_registered_mstore >>
  simp[abi_encoder_write_observations] >> metis_tac[]
QED

Theorem encoder_dynamic_iteration_word_addresses:
  (n2w d:bytes32) + n2w 32 = n2w (d+32) /\
  (n2w i:bytes32) * n2w h = n2w (i*h) /\
  (n2w (d+32):bytes32) + n2w (i*h) = n2w (d+32+i*h) /\
  (n2w (d+32):bytes32) + n2w off = n2w (d+32+off) /\
  (n2w off:bytes32) + n2w child_len = n2w (off+child_len) /\
  (n2w i:bytes32) + 1w = n2w (i+1)
Proof
  simp[word_add_n2w, word_mul_n2w]
QED
