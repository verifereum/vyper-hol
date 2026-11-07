Theory exprSimAbiEncodeFrameTransfer
Ancestors
  abiEncoderRegisteredEffect valueEncoding venomState finite_map pred_set list

Theorem abi_encode_registered_protected_byte:
  abi_encoder_registered_effect ids outs s t /\
  lo <= a /\ a < lo+n /\
  EVERY (\(b,k). lo+n <= b \/ b+k <= lo) outs /\
  (!i b k. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,k) ==>
       lo+n <= b \/ b+k <= lo) ==>
  mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  qpat_x_assum `!a. EVERY _ outs /\ _ ==> _` irule >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> decide_tac) >>
  fs[EVERY_MEM] >> Cases >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> decide_tac
QED
