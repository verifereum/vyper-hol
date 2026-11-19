Theory bodyFullAbiDecodeRecursive
Ancestors
  bodyFullAbiDecodeRecursiveConditional bodyFullAbiDecodeArrayCases
Libs
  bodyFullAbiDecodeLoopObservedSyntaxLib

val public_mutual =
  snd (dest_imp (concl abi_decode_joint_mutual_from_array_clause));

Theorem abi_decode_joint_mutual:
  ^public_mutual
Proof
  MATCH_MP_TAC abi_decode_joint_mutual_from_array_clause >>
  BETA_TAC >> rpt gen_tac >>
  MATCH_ACCEPT_TAC abi_decode_array_guarded_conditional
QED

val guarded_to_buf_entry = bodyFullAbiDecodeRuntimeLoopSyntaxLib.guarded_to_buf_entry;
val guarded_producer = close_statement ``
  (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
    start cut s G tn d /\
  (^contained) protected /\ (^input_origin) s ==>
  (^observed_decoder_post) ((^robust_at_typed) tv d) live protected start cut s G tn``;

Theorem abi_decode_guarded_to_buf_joint:
  ^guarded_producer
Proof
  BETA_TAC >> rpt gen_tac >>
  MATCH_ACCEPT_TAC (GEN_ALL (SPEC_ALL (BETA_RULE (CONJUNCT1 abi_decode_joint_mutual))))
QED
