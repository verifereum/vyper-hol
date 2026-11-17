(* Ordinary effect opcodes: compositional raw stack effects and checker edges. *)
Theory stackBoundEffects
Ancestors
  stackBoundEffectMemory stackBoundEffectState stackBoundEffectBridge
  stackBoundEffectCore stackBoundInterface stackBoundDefs
  vfmExecution vfmExecutionProp vfmState vfmContext vfmConstants
  list rich_list pair option finite_map words arithmetic

Theorem sb_eff_raw_neutral_prefix:
  sb_eff_neutral m /\ (!x. sb_eff_raw 0 k (f x)) ==>
  sb_eff_raw 0 k (bind m f)
Proof
  strip_tac >> simp[sb_eff_raw_def] >> rpt gen_tac >>
  simp[bind_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all (iffLR sb_eff_neutral_def) >> strip_tac >>
  gvs[] >> rename1 `m s = (INL x,u)` >>
  qpat_x_assum `!x. sb_eff_raw _ _ _` (qspec_then `x` mp_tac) >>
  simp[sb_eff_raw_def] >>
  disch_then (qspec_then `u` mp_tac) >>
  gvs[sb_eff_frame_def]
QED

Theorem sb_eff_raw_pop_prefix:
  (!args. sb_eff_raw 0 k (f args)) ==>
  sb_eff_raw p k (bind (pop_stack p) f)
Proof
  rw[sb_eff_raw_def, pop_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, assert_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  first_x_assum (qspec_then `TAKE p (FST (HD s.contexts)).stack` mp_tac) >>
  disch_then (drule_at Any) >> simp[] >> strip_tac >>
  gvs[sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_raw_push:
  sb_eff_raw 0 1 (push_stack v)
Proof
  rw[sb_eff_raw_def, push_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, assert_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_opcode_raw[local]:
  MEM op [Keccak256; Balance; CallDataLoad; CallDataCopy; CodeCopy;
          ExtCodeSize; ExtCodeCopy; ReturnDataCopy; ExtCodeHash; BlockHash;
          SelfBalance; BlobHash; MLoad; MStore; MStore8; SLoad; SStore;
          TLoad; TStore; MCopy; Log n] ==>
  sb_eff_raw (FST (bytecode_stack_io op)) (SND (bytecode_stack_io op))
    (step_inst op)
Proof
  simp[MEM] >> strip_tac >> gvs[bytecode_stack_io_def, step_inst_def] >>
  simp[step_keccak256_def, step_balance_def, step_call_data_load_def,
       step_copy_to_memory_def, step_ext_code_size_def, step_ext_code_copy_def,
       step_return_data_copy_def, step_ext_code_hash_def, step_block_hash_def,
       step_self_balance_def, step_blob_hash_def, step_mload_def, step_mstore_def,
       step_sload_def, step_sstore_def, step_log_def,
       ignore_bind_def, sb_eff_raw_pop_prefix, sb_eff_raw_neutral_prefix,
       sb_eff_raw_push, sb_eff_raw_pop_neutral, sb_eff_neutral_bind,
       sb_eff_copy_to_memory_neutral]
  >~ [`sb_eff_raw (n + 2) 0 _`]
  >- (irule sb_eff_raw_pop_neutral >> gen_tac >> BETA_TAC >>
      rpt (irule sb_eff_neutral_bind >>
           (reverse conj_tac >- simp[]) >> gen_tac >> BETA_TAC) >>
      simp[]) >>
  irule sb_eff_raw_pop_prefix >> gen_tac >> BETA_TAC >>
  rpt (irule sb_eff_raw_neutral_prefix >>
       (reverse conj_tac >- simp[]) >> gen_tac >> BETA_TAC) >>
  simp[sb_eff_raw_push]
QED

Theorem sb_effect_contracts:
  MEM op [Keccak256; Balance; CallDataLoad; CallDataCopy; CodeCopy;
          ExtCodeSize; ExtCodeCopy; ReturnDataCopy; ExtCodeHash; BlockHash;
          SelfBalance; BlobHash; MLoad; MStore; MStore8; SLoad; SStore;
          TLoad; TStore; MCopy; Log n] ==>
  sb_opcode_contract op
Proof
  strip_tac >> irule sb_eff_raw_opcode_contract >>
  conj_tac >- gvs[MEM, is_call_def] >>
  qexistsl [`SND (bytecode_stack_io op)`, `FST (bytecode_stack_io op)`] >>
  reverse conj_tac >- metis_tac[sb_eff_opcode_raw] >>
  rpt gen_tac >> strip_tac >>
  `wf_context (FST (HD s.contexts))` by
    (Cases_on `s.contexts` >> gvs[wf_state_def]) >>
  gvs[wf_context_def, sb_decoded_def, sb_successors_def] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY (FST (HD s.contexts)).msgParams.code)
                     (FST (HD s.contexts)).pc` >>
  gvs[AllCaseEqs(), MEM, bytecode_stack_successors_def, bytecode_stack_io_def]
QED
