Theory bodyFullAbiDecodeCutMember
Ancestors
  bodyFullAbiDecodeCutComplexBind bodyFullAbiDecodeComplexPrefixSlice
  bodyFullAbiDecodeCutMemberBind bodyFullAbiDecodeMemberPrefix

(* Keep the constructor clauses, including their selected post, verbatim
   from the bind theorems; only the exact-prefix antecedent is removed. *)
Theorem abi_decode_cut_complex_clause:
  ^(snd (dest_imp (concl abi_decode_cut_complex_from_prefix)))
Proof
  MATCH_MP_TAC abi_decode_cut_complex_from_prefix >> rpt gen_tac >>
  MATCH_ACCEPT_TAC (GEN_ALL (SPEC_ALL
    (BETA_RULE abi_decode_complex_prefix_observed_slice)))
QED

Theorem abi_decode_cut_member_clause:
  ^(snd (dest_imp (concl abi_decode_cut_member_from_prefix)))
Proof
  MATCH_MP_TAC abi_decode_cut_member_from_prefix >> rpt gen_tac >>
  MATCH_ACCEPT_TAC (GEN_ALL (SPEC_ALL
    (BETA_RULE abi_decode_member_prefix_joint_observed_slice)))
QED
