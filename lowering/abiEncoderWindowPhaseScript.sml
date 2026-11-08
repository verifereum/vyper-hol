(* Control-normalized phases for recursive window execution. *)
Theory abiEncoderWindowPhase
Ancestors
  abiEncoderWindowCursor abiEncoderWindowSequence abiEncoderWindowContract
  abiEncoderWindowLeaves abiEncoderPrimitiveEffect emitHelperProps emitHelper
  abiEncoderRegisteredEffect abiEncoderExtendSim exprLoweringProps freshWrites
  compileEnv venomState venomExecSemantics venomMemDefs fragExec finite_map list pred_set

Definition window_phase_def:
  window_phase ctx func st en ids outs s t <=>
    abi_encoder_extend_sim ctx func s t /\
    abi_encoder_registered_effect ids outs s t /\
    window_alloca_growth s t /\ alloca_inv t /\ alloca_room ctx func t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ t.vs_labels = s.vs_labels
End

Theorem window_phase_resources:
  window_phase ctx func st en ids outs s t ==>
  alloca_inv t /\ alloca_room ctx func t /\ window_alloca_growth s t
Proof
  simp[window_phase_def]
QED

Theorem window_phase_control:
  window_phase ctx func st en ids outs s t ==>
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  simp[window_phase_def]
QED

Theorem window_phase_effect:
  window_phase ctx func st en ids outs s t ==>
  abi_encoder_registered_effect ids outs s t
Proof
  simp[window_phase_def]
QED

Theorem window_phase_extend:
  window_phase ctx func st en ids outs s t ==>
  abi_encoder_extend_sim ctx func s t
Proof
  simp[window_phase_def]
QED

Theorem window_phase_vars:
  window_phase ctx func st en ids outs s t /\
  not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w
Proof
  simp[window_phase_def] >> metis_tac[]
QED

Theorem window_phase_chain:
  window_phase ctx func st mid left left_out s t /\
  window_phase ctx func mid en right right_out t u /\
  st.cs_next_var <= mid.cs_next_var /\ left SUBSET ids /\ right SUBSET ids /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) left_out) /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) right_out) ==>
  window_phase ctx func st en ids outs s u
Proof
  simp_tac bool_ss [window_phase_def] >> strip_tac >>
  `abi_encoder_registered_effect ids outs s u /\ window_alloca_growth s u` by
    (irule window_alloca_growth_sequence >> metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[abi_encoder_extend_sim_trans] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_seq_phase:
  window_seq st en s raw /\ fn_has_code st en func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_registered_effect ids outs s raw /\ window_alloca_growth s raw /\
  alloca_inv raw /\ alloca_room ctx func raw /\
  raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb ==>
  window_phase ctx func st en ids outs s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >>
  `raw.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  `abi_encoder_extend_sim ctx func s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_extend_sim] >>
  simp_tac (srw_ss()) [window_phase_def, lookup_var_def,
    abi_encoder_registered_effect_def, window_alloca_growth_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_room_def] >>
  fs[window_seq_def, lookup_var_def, abi_encoder_registered_effect_def,
    window_alloca_growth_def, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, alloca_room_def, pending_alloca_size_def] >>
  metis_tac[]
QED

Theorem window_phase_eval:
  window_phase ctx func st en ids outs s t /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  t.vs_labels = s.vs_labels /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  strip_tac >> Cases_on `op` >> fs[eval_operand_def] >>
  metis_tac[window_phase_vars]
QED

Theorem window_phase_enlarge:
  window_phase ctx func st en ids outs s t /\ ids SUBSET more /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) wider ==>
    EVERY (\(b,n). a < b \/ b+n <= a) outs) ==>
  window_phase ctx func st en more wider s t
Proof
  simp_tac bool_ss [window_phase_def] >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_encoder_registered_effect_enlarge >>
  metis_tac[]
QED

Theorem window_phase_refl:
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st st ids outs s s
Proof
  simp[window_phase_def, abi_encoder_extend_sim_refl,
    abi_encoder_registered_effect_refl, window_alloca_growth_refl]
QED

Theorem window_phase_strong_result:
  window_strong_result ctx func st en out at av d s t ==>
  window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t
Proof
  simp[window_strong_result_def, abi_encoder_window_result_def, window_phase_def]
QED

Theorem window_pure_seq_phase:
  window_pure_seq st en s raw /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en ids outs s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_seq_phase >>
  simp_tac (srw_ss()) [] >>
  `abi_encoder_registered_effect ids outs s raw` by
    metis_tac[window_pure_seq_registered_effect] >>
  `window_alloca_growth s raw` by
    metis_tac[window_pure_seq_def, window_alloca_growth_fields] >>
  `alloca_room ctx func raw` by
    (irule alloca_room_fields >> qexists_tac `s` >>
     metis_tac[window_pure_seq_def]) >>
  `alloca_inv raw` by
    (qpat_x_assum `alloca_inv s` mp_tac >>
     fs[window_pure_seq_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def]) >>
  fs[window_pure_seq_def]
QED

Theorem window_emit_add_phase:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_cursor_load_phase:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all window_cursor_load_sequence >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

(* One store boundary covers both registered cursors and destination words.
   Its effect premise specifies which of those two footprints is writable. *)
Theorem window_store_phase:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_registered_effect ids outs s (mstore b w s) ==>
  window_phase ctx func st en ids outs s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> drule_all window_emit_store_run >> strip_tac >>
  `en.cs_next_var = st.cs_next_var` by
    (qpat_assum `emit_void _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emit_void_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM) >> simp[]) >>
  `window_seq st en s (mstore b w s)` by
    (simp[window_seq_def] >>
     simp_tac (srw_ss()) [lookup_var_def, mstore_def,
       write_memory_with_expansion_def, LET_THM]) >>
  irule window_seq_phase >> simp_tac (srw_ss()) [] >>
  asm_rewrite_tac[] >>
  `alloca_inv (mstore b w s)` by
    metis_tac[abi_encoder_primitive_alloca_inv] >>
  `alloca_room ctx func (mstore b w s)` by
    (irule alloca_room_fields >> qexists_tac `s` >>
     simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
     asm_rewrite_tac[]) >>
  `window_alloca_growth s (mstore b w s)` by
    (irule window_alloca_growth_fields >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
  asm_rewrite_tac[]
QED

Theorem window_cursor_store_phase:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ FLOOKUP s.vs_allocas id = SOME (b,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en {id} [] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase >> asm_rewrite_tac[] >>
  metis_tac[abi_encoder_registered_slot_store, IN_SING]
QED

Theorem window_output_store_phase:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_phase ctx func st en {} [(b,32)] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  irule abi_encoder_output_store >> simp[]
QED

Theorem window_emit_alloca32_phase:
  emit_op ALLOCA [Lit 32w] st = (out,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    eval_operand out t = SOME (n2w b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  (conj_tac >- metis_tac[window_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_phase_labels:
  window_phase ctx func st en ids outs s t ==> t.vs_labels = s.vs_labels
Proof
  simp[window_phase_def]
QED

Theorem window_phase_operand:
  window_phase ctx func st en ids outs s t /\
  (!x. op = Var x ==> not_fresh_at st x) /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >>
  metis_tac[window_phase_vars, window_phase_labels]
QED
