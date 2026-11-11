(* Fixed arbitrary-byte observations, independent of successful decoding. *)
Theory abiMalformedRuntime
Ancestors
  abiMalformedPrefix abiDecoderReentry abiDecoderFrame abiDecoderContract
  compileEnv venomState valueEncoding valueEncodingProps words list arithmetic

Definition abi_malformed_window_def:
  abi_malformed_window opc base_op hi src dst B L p d outsz b k xs s <=>
    abi_decode_source_opcode opc /\ hi <> Lit 0w /\
    eval_operand base_op s = SOME (n2w B) /\
    eval_operand hi s = SOME (n2w L) /\
    eval_operand src s = SOME (n2w p) /\
    eval_operand dst s = SOME (n2w d) /\
    B + L < dimword (:256) /\ p < dimword (:256) /\
    d + outsz < dimword (:256) /\
    mem_bytes_at B L (abi_decode_source opc s) = xs /\
    (d + outsz <= b \/ b + k <= d) /\
    (opc = MLOAD ==> abi_footprint_disjoint B L [(d,outsz);(b,k)])
End

Theorem abi_malformed_window_prune:
  abi_decoder_operand_live next base_op /\ abi_decoder_operand_live next hi /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst ==>
  (abi_malformed_window opc base_op hi src dst B L p d outsz b k xs
     (abi_decoder_prune_vars next s) <=>
   abi_malformed_window opc base_op hi src dst B L p d outsz b k xs s)
Proof
  strip_tac >> simp[abi_malformed_window_def, abi_decoder_prune_eval]
QED

Theorem abi_malformed_window_frame:
  abi_malformed_window opc base_op hi src dst B L p d outsz b k xs s /\
  abi_decode_footprint_frame [(d,outsz);(b,k)] s t /\
  (!op w. MEM op [base_op;hi;src;dst] /\ eval_operand op s = SOME w ==>
          eval_operand op t = SOME w) ==>
  abi_malformed_window opc base_op hi src dst B L p d outsz b k xs t
Proof
  simp[abi_malformed_window_def] >> strip_tac >> simp[] >>
  `mem_bytes_at B L (abi_decode_source opc t) =
   mem_bytes_at B L (abi_decode_source opc s)` by
    (gvs[abi_decode_source_opcode_def, abi_decode_source_def,
         abi_decode_footprint_frame_def] >> metis_tac[]) >>
  metis_tac[]
QED

Definition abi_malformed_loop_def:
  abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
      env ty array_xs next ip ip_value n j avs s <=>
    abi_malformed_window opc base_op hi src dst B L p d outsz b k xs s /\
    j <= n /\ eval_operand ip s = SOME ip_value /\
    abi_decoder_operand_live next ip /\
    mload (w2n ip_value) s = n2w j /\
    abi_reflected_prefix env ty array_xs j avs
End

Theorem abi_malformed_loop_prune:
  abi_decoder_operand_live next base_op /\ abi_decoder_operand_live next hi /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip ==>
  (abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
     env ty array_xs next ip ip_value n j avs (abi_decoder_prune_vars next s) <=>
   abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
     env ty array_xs next ip ip_value n j avs s)
Proof
  strip_tac >> simp[abi_malformed_loop_def, abi_malformed_window_prune,
    abi_decoder_prune_eval, mload_def, abi_decoder_prune_vars_def]
QED

Theorem abi_malformed_loop_init:
  abi_malformed_window opc base_op hi src dst B L p d outsz b k xs s /\
  eval_operand ip s = SOME ip_value /\ abi_decoder_operand_live next ip /\
  mload (w2n ip_value) s = 0w ==>
  abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
    env ty array_xs next ip ip_value n 0 [] s
Proof
  simp[abi_malformed_loop_def, abi_reflected_prefix_empty]
QED

Theorem abi_malformed_loop_advance:
  abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
    env ty array_xs next ip ip_value n j avs s /\ j < n /\
  abi_malformed_window opc base_op hi src dst B L p d outsz b k xs t /\
  eval_operand ip t = SOME ip_value /\ mload (w2n ip_value) t = n2w (SUC j) /\
  abi_reflected_head_ok a array_xs j /\
  vyper_decode_valid_enc a (abi_reflected_child a array_xs j) /\
  abi_vyper_admissible env ty (dec a (abi_reflected_child a array_xs j)) /\
  a = vyper_to_abi_type env ty ==>
  abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
    env ty array_xs next ip ip_value n (SUC j)
    (avs ++ [dec a (abi_reflected_child a array_xs j)]) t
Proof
  simp_tac bool_ss [abi_malformed_loop_def] >> strip_tac >>
  `abi_reflected_prefix env ty array_xs (SUC j)
     (avs ++ [dec a (abi_reflected_child a array_xs j)])` by
    (irule abi_reflected_prefix_append >> metis_tac[]) >>
  gvs[]
QED
