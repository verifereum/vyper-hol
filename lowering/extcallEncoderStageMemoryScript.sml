(* Same-witness encoder result supplied to the calldata length/offset suffix.
   The caller instantiates Q with the ADD 4 and ADD 28 endpoint facts. *)
Theory extcallEncoderStageMemory
Ancestors
  abiEncoderWindowRunMem abiEncoderWindowContract memContinuation abiEncoderProps

Theorem extcall_encode_length_cont_mem:
  abi_encoder_admissible ei /\
  compile_abi_encode_to_buf dst src ei st = (lenop,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  (!t. abi_encoder_window_result ctx func st en lenop at av d s t /\
       mem_cont_sim ctx func s t ==>
       ?u. Q t u /\ mem_cont_sim ctx func t u) ==>
  ?t u.
    abi_encoder_window_result ctx func st en lenop at av d s t /\
    mem_cont_sim ctx func s t /\ Q t u /\
    mem_cont_sim ctx func t u /\ mem_cont_sim ctx func s u /\
    abi_encoder_registered_effect (frag_ids st en)
      [(d,LENGTH (enc at av))] s t
Proof
  strip_tac >> drule_all compile_abi_encode_to_buf_window_run_mem >>
  strip_tac >>
  qpat_x_assum `!t. _` drule_all >> strip_tac >>
  qexistsl_tac [`t`, `u`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  fs[abi_encoder_window_result_def]
QED
