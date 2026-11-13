(* The recursive encoder reads live source fields, not unused capacity.
   Coverage and robustness are deliberately separate obligations. *)
Theory abiEncoderPointerInput
Ancestors
  abiEncoderWindow abiEncoderLiveSource representationCleanPtr
  logAbiPrefixPtr wordLoadStorePtr decoderProtectedScratchPtr
  reasonCopySourcePtr bodyPtrDefs

Theorem abi_encoder_window_bytes_clean:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiBytestring maxlen) at
      (contractABI$BytesV bs) sb cap mem) ==>
  !i. sb <= i /\ i < sb+32+LENGTH bs ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at sb mem = n2w (LENGTH bs)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[abi_encoder_window_bytes_iff]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_bytes_at (sb+32) (LENGTH bs) mem = bs` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[abi_encoder_window_bytes_iff]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  drule robust_mem_bytes_at_clean >> strip_tac >>
  rpt strip_tac >> Cases_on `i < sb+32` >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem abi_encoder_window_word_clean:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input AbiPrimWord at av sb cap mem) ==>
  !i. sb <= i /\ i < sb+32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> irule robust_mem_bytes_at_clean >>
  qexistsl_tac [`s.vs_memory`, `enc at av`] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[abi_encoder_window_word_iff]
QED

Theorem abi_encoder_window_copy_clean:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiCopy n) at av sb cap mem) ==>
  !i. sb <= i /\ i < sb+n ==> i NOTIN tn.t_mem
Proof
  strip_tac >> irule robust_mem_bytes_at_clean >>
  qexistsl_tac [`s.vs_memory`, `enc at av`] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[abi_encoder_window_copy_iff]
QED

Theorem abi_encoder_window_array_header_clean:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiDynArray ei h stride dyn)
      (Array NONE ct) (ListV avs) sb cap mem) ==>
  !i. sb <= i /\ i < sb+32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> irule robust_mem_word_at_clean >>
  qexistsl_tac [`s.vs_memory`, `n2w (LENGTH avs)`] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[abi_encoder_window_array_iff]
QED
