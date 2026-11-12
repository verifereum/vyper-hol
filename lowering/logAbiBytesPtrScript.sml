(* Clean-output boundaries for the bytestring ABI encoder. *)
Theory logAbiBytesPtr
Ancestors
  logValueFramePtr abiEncoderBytesCode abiEncoderRounding
  fragExecPtr decoderGhostFramePtr ptrDiscipline
  venomInst venomState words pred_set arithmetic list

Theorem abi_bytes_clean_cover:
  !dst len i.
    dst <= i /\ i < dst + 32 + contractABI$ceil32 len ==>
    (dst <= i /\ i < dst + 32 + len) \/
    (dst + contractABI$ceil32 len <= i /\
     i < dst + contractABI$ceil32 len + 32)
Proof
  rpt strip_tac >> mp_tac (Q.INST [`cnt` |-> `len`] abi_encoder_ceil32_bounds) >>
  decide_tac
QED

Theorem abi_bytes_clean_cover_edges:
  contractABI$ceil32 0 = 0 /\ contractABI$ceil32 32 = 32 /\
  contractABI$ceil32 33 = 64
Proof
  EVAL_TAC
QED

Theorem abi_bytes_output_clean:
  !dst len old clean i.
    (!j. dst <= j /\ j < dst+32+len ==> j NOTIN clean) /\
    (!j. dst+contractABI$ceil32 len <= j /\
         j < dst+contractABI$ceil32 len+32 ==> j NOTIN old) /\
    (!j. ~(dst <= j /\ j < dst+32+len) ==> (j IN clean <=> j IN old)) /\
    dst <= i /\ i < dst+32+contractABI$ceil32 len ==>
    i NOTIN clean
Proof
  rpt strip_tac >> drule_all abi_bytes_clean_cover >> strip_tac >>
  metis_tac[]
QED
