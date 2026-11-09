(* Parent cursor finish on arbitrary runtime variable maps. *)
Theory abiEncoderWindowArrayFinish
Ancestors
  abiEncoderWindowArrayExit abiEncoderWindowArrayBody abiEncoderArrayContext
  abiEncoderWindowSequence abiEncoderWindowLeaves abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderWindowContract abiEncoderArrayPhases
  emitHelperProps freshWrites emitHelper compileEnv fragExec venomState
  venomExecSemantics venomInst words list finite_map arithmetic

Theorem window_array_store_seq[local]:
  emit_void MSTORE [ptr_op;value_op] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value_op s = SOME w /\
  b < dimword (:256) ==>
  window_seq st en s (mstore b w s)
Proof
  strip_tac >> drule_all window_emit_store_run >> strip_tac >>
  `en.cs_next_var = st.cs_next_var` by
    (qpat_assum `emit_void _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emit_void_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM) >> simp[]) >>
  simp[window_seq_def] >>
  simp_tac (srw_ss()) [lookup_var_def, mstore_def,
    write_memory_with_expansion_def, LET_THM]
QED

Theorem window_array_parent_finish_seq:
  abi_encode_array_finish pp size_op st = (out,en) /\
  eval_operand pp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = 0w /\ eval_operand size_op s = SOME (n2w n) /\
  (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at st x) ==>
  ?raw t2 before after.
    window_seq st en s raw /\
    window_pure_seq st before s t2 /\
    window_pure_seq after en (mstore slot (n2w n) t2) raw /\
    eval_operand out raw = SOME (n2w n) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  simp_tac bool_ss [abi_encode_array_finish_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [pp] st = (old,c1)` >>
  rename1 `emit_op ADD [old;size_op] c1 = (next,c2)` >>
  rename1 `emit_void MSTORE [pp;next] c2 = ((),c3)` >>
  `?t1. window_pure_seq st c1 s t1 /\
      eval_operand old t1 = SOME (0w:bytes32) /\
      (!x. old = Var x ==> not_fresh_at c1 x)` by
    metis_tac[window_emit_load_pure] >>
  `eval_operand size_op t1 = SOME (n2w n)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `?t2. window_pure_seq c1 c2 t1 t2 /\
      eval_operand next t2 = SOME (n2w n) /\
      (!x. next = Var x ==> not_fresh_at c2 x)` by
    (drule_all window_emit_add_pure >> simp[WORD_ADD_0]) >>
  `window_pure_seq st c2 s t2` by metis_tac[window_pure_seq_chain] >>
  `eval_operand pp t2 = SOME (n2w slot)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `window_seq c2 c3 t2 (mstore slot (n2w n) t2)` by
    metis_tac[window_array_store_seq] >>
  `eval_operand pp (mstore slot (n2w n) t2) = SOME (n2w slot)` by
    (Cases_on `pp` >> fs[eval_operand_def, lookup_var_def,
       mstore_def, write_memory_with_expansion_def]) >>
  `mload slot (mstore slot (n2w n) t2) = n2w n` by
    simp[venomMemPropsTheory.mload_mstore_same] >>
  `?raw. window_pure_seq c3 en (mstore slot (n2w n) t2) raw /\
      eval_operand out raw = SOME (n2w n) /\
      (!x. out = Var x ==> not_fresh_at en x)` by
    metis_tac[window_emit_load_pure] >>
  qexistsl_tac [`raw`, `t2`, `c2`, `c3`] >> asm_rewrite_tac[] >>
  metis_tac[window_seq_chain, window_pure_seq_def]
QED

Theorem window_array_parent_finish:
  abi_encode_array_finish pp size_op st = (out,en) /\
  eval_operand pp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = 0w /\ eval_operand size_op s = SOME (n2w n) /\
  (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {site} [] s t /\
    window_array_transition ctx func st {site} [] s t /\
    eval_operand out t = SOME (n2w n) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_parent_finish_seq >> strip_tac >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next /\
   raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb` by
    fs[window_pure_seq_def, mstore_def, write_memory_with_expansion_def] >>
  `abi_encoder_registered_effect {site} [] s raw` by
    (`abi_encoder_registered_effect {site} [] s t2` by
       metis_tac[window_pure_seq_registered_effect] >>
     `abi_encoder_registered_effect {site} [] t2 (mstore slot (n2w n) t2)` by
       (irule abiEncoderPrimitiveEffectTheory.abi_encoder_registered_slot_store >>
        fs[window_pure_seq_def]) >>
     `abi_encoder_registered_effect {site} [] (mstore slot (n2w n) t2) raw` by
       metis_tac[window_pure_seq_registered_effect] >>
     metis_tac[abi_encoder_registered_effect_trans]) >>
  `window_alloca_growth s raw` by
    metis_tac[window_alloca_growth_fields] >>
  `alloca_inv raw /\ alloca_room ctx func raw` by
    (fs[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def] >> metis_tac[]) >>
  `window_phase ctx func st en {site} [] s
     (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_phase] >>
  qexists_tac `raw with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_phase_transition >> conj_tac
      >- simp[abiEncoderWindowArrayInvariantTheory.window_sizes32_def] >>
      goal_assum (drule_at Any)) >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED
