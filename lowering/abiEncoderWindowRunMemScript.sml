(* Same-witness semantic and memory-safe window encoder execution. *)
Theory abiEncoderWindowRunMem
Ancestors
  abiEncoderWindowLeavesMem abiEncoderWindowArrayMem abiEncoderWindowComplexMem
  abiEncoderWindowContract abiEncoderAdmissible abiEncoder compileEnv
  memContinuation list pair

Theorem window_strong_admissible_mutual_mem:
  (!ei. abi_encoder_admissible ei ==>
    !dst src st out en ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,en) /\
      abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
      ?t. window_strong_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t) /\
  (!infos. abi_encoder_members_admissible infos ==>
    EVERY (\(ei,_,_,_).
      !dst src st out en ctx func s at av sb cap d.
        compile_abi_encode_to_buf dst src ei st = (out,en) /\
        abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
        ?t. window_strong_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rw[abi_encoder_admissible_def, EVERY_DEF] >> gvs[]
  >- metis_tac[window_word_contract_mem]
  >- metis_tac[window_copy_contract_mem]
  >- metis_tac[window_bytes_contract_mem]
  >- (drule window_array_strong_contract_mem >> disch_then drule >>
      disch_then drule >> simp[])
  >- (drule window_array_strong_contract_mem >> disch_then drule >>
      disch_then drule >> simp[]) >>
  `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==>
    !dst src st out en ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,en) /\
      abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
      ?t. window_strong_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t` by
    (fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  drule window_complex_strong_contract_mem >> strip_tac >> metis_tac[]
QED

Theorem compile_abi_encode_to_buf_window_strong_mem:
  abi_encoder_admissible ei /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
  ?t. window_strong_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t
Proof
  metis_tac[cj 1 window_strong_admissible_mutual_mem]
QED

Theorem compile_abi_encode_to_buf_window_run_mem:
  abi_encoder_admissible ei /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
  ?t. abi_encoder_window_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all compile_abi_encode_to_buf_window_strong_mem >>
  metis_tac[window_strong_result_public]
QED
