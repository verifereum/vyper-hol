Theory exprSimAbiEncodeExecFrame
Ancestors
  abiEncoderWindowContract exprLoweringProps intCallCallee venomState venomExecSemantics
  exprSimAbiEncodeSemantic exprSimAbiEncodeMemoryLength list

Definition abi_encode_exec_frame_def:
  abi_encode_exec_frame fn s t <=>
    t.vs_alloca_next + pending_alloca_size fn t <=
      s.vs_alloca_next + pending_alloca_size fn s /\
    t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    abi_encode_semantic_obs t = abi_encode_semantic_obs s /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
End

Definition abi_encode_framed_contract_def:
  abi_encode_framed_contract ei <=>
    !dst src st out st' ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,st') /\
      abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
      ?t. window_strong_result ctx func st st' out at av d s t /\
          abi_encode_exec_frame func s t
End

Theorem abi_encode_exec_frame_refl[simp]:
  abi_encode_exec_frame fn s s
Proof
  simp[abi_encode_exec_frame_def]
QED

Theorem abi_encode_exec_frame_trans:
  abi_encode_exec_frame fn s t /\ abi_encode_exec_frame fn t u ==>
  abi_encode_exec_frame fn s u
Proof
  simp[abi_encode_exec_frame_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_encode_exec_frame_inst_idx[simp]:
  abi_encode_exec_frame fn s (t with vs_inst_idx := ix) =
  abi_encode_exec_frame fn s t
Proof
  simp[abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_exec_frame_mcopy[simp]:
  abi_encode_exec_frame fn s (mcopy d sb n s)
Proof
  simp[abi_encode_exec_frame_def, pending_alloca_size_def,
       mcopy_def, write_memory_with_expansion_def, abi_encode_semantic_obs_def,
       LENGTH_TAKE, LENGTH_DROP] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem abi_encode_exec_frame_semantic:
  abi_encode_exec_frame fn s t ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  simp[abi_encode_exec_frame_def]
QED

Theorem abi_encode_exec_frame_bridge_updates:
  abi_encode_exec_frame func s t ==>
  abi_encode_exec_frame func s (t with vs_returndata := rd) /\
  abi_encode_exec_frame func s (t with vs_prev_bb := prev)
Proof
  simp[abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_exec_frame_memory_length:
  abi_encode_exec_frame fn s t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp[abi_encode_exec_frame_def]
QED

Theorem abi_encode_exec_frame_mstore[simp]:
  !fn b w s. abi_encode_exec_frame fn s (mstore b w s)
Proof
  rpt gen_tac >> rewrite_tac[abi_encode_exec_frame_def] >>
  rpt conj_tac
  >- simp[pending_alloca_size_def, mstore_def]
  >- simp[mstore_def]
  >- simp[mstore_def]
  >- simp[mstore_def]
  >- simp[abi_encode_semantic_obs_def, mstore_def]
  >> irule abi_encode_mstore_memory_length
QED
