Theory loadElimPaddedSimHelpers
Ancestors
  loadElimMemoryRel venomExecSemantics venomState stateFrame
  regularCallEmitSim codegenRel list finite_map

Theorem padded_exec_equiv_read_memory:
  padded_exec_equiv vars s t ==>
  read_memory off n s = read_memory off n t
Proof
  strip_tac >> irule read_memory_range_ext >>
  gvs[padded_exec_equiv_def]
QED

Theorem padded_exec_equiv_read_byte:
  padded_exec_equiv vars s t ==>
  read_byte i s.vs_memory = read_byte i t.vs_memory
Proof
  strip_tac >>
  `read_memory i 1 s = read_memory i 1 t` by
    metis_tac[padded_exec_equiv_read_memory] >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[read_memory_read_byte]
QED

Theorem padded_exec_equiv_write_memory:
  padded_exec_equiv vars s t ==>
  padded_exec_equiv vars (write_memory_with_expansion off bytes s)
    (write_memory_with_expansion off bytes t)
Proof
  strip_tac >> rewrite_tac[padded_exec_equiv_def] >> conj_tac
  >- gvs[padded_exec_equiv_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (gen_tac >> irule read_memory_read_byte_ext >> gen_tac >>
      simp[read_byte_write_memory_with_expansion] >>
      metis_tac[padded_exec_equiv_read_byte]) >>
  gvs[padded_exec_equiv_def, write_memory_with_expansion_def, execution_frame_def]
QED

Theorem padded_exec_equiv_update_var:
  padded_exec_equiv vars s t ==>
  padded_exec_equiv vars (update_var v w s) (update_var v w t)
Proof
  simp[padded_exec_equiv_def, lookup_var_def, update_var_def,
       read_memory_def, execution_frame_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem padded_exec_equiv_adopt_return:
  padded_exec_equiv vars s t ==>
  padded_exec_equiv vars (adopt_return_fmp ir s) (adopt_return_fmp ir t)
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality]
QED

Theorem padded_exec_equiv_merge_callee:
  padded_exec_equiv vars s t /\ padded_exec_equiv callee_vars c d ==>
  padded_exec_equiv vars (merge_callee_state s c) (merge_callee_state t d)
Proof
  strip_tac >> rewrite_tac[padded_exec_equiv_def] >> conj_tac
  >- gvs[padded_exec_equiv_def, merge_callee_state_def, lookup_var_def] >>
  conj_tac
  >- gvs[padded_exec_equiv_def, merge_callee_state_def, read_memory_def] >>
  gvs[padded_exec_equiv_def, execution_frame_def,
      merge_callee_state_def, venom_state_component_equality]
QED

Theorem padded_exec_equiv_setup_callee:
  padded_exec_equiv vars s t /\ setup_callee fn args s = SOME c /\
  setup_callee fn args t = SOME d ==>
  padded_exec_equiv callee_vars c d
Proof
  Cases_on `NULL fn.fn_blocks` >- simp[setup_callee_def] >>
  simp[setup_callee_def] >>
  rpt strip_tac >> gvs[] >>
  rewrite_tac[padded_exec_equiv_def] >> conj_tac
  >- simp[lookup_var_def, FLOOKUP_EMPTY] >>
  conj_tac
  >- gvs[padded_exec_equiv_def, read_memory_def] >>
  gvs[padded_exec_equiv_def, execution_frame_def, venom_state_component_equality]
QED

Theorem padded_exec_equiv_fold_updates:
  !pairs s t. padded_exec_equiv vars s t ==>
    padded_exec_equiv vars
      (FOLDL (\st (v,w). update_var v w st) s pairs)
      (FOLDL (\st (v,w). update_var v w st) t pairs)
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >>
  metis_tac[padded_exec_equiv_update_var]
QED

Theorem padded_exec_equiv_bind_outputs:
  padded_exec_equiv vars s t /\ bind_outputs outs vals s = SOME s' /\
  bind_outputs outs vals t = SOME t' ==>
  padded_exec_equiv vars s' t'
Proof
  simp[bind_outputs_def] >>
  rpt strip_tac >> gvs[] >> irule padded_exec_equiv_fold_updates >> simp[]
QED
