(* lower_abi_decode does not depend on its entry block's label or on the IDs
   of the instructions already in it, and the code it emits meets the
   relabeled bridges' shape premises. *)
Theory exprSimAbiDecodeOblivious
Ancestors
  exprSimAbiGasBridge exprSimAbiDecodeCertificate exprSimAbiDecodeTrace
  builtinAbi compileEnv fragExec

Theorem lower_abi_decode_start_oblivious:
  !data di mn mx msz.
    frag_start_oblivious (lower_abi_decode data di mn mx msz)
Proof
  rpt gen_tac >> irule decode_certificate_oblivious >>
  simp[decode_certificate_lower]
QED

Theorem lower_abi_decode_frag_facts:
  !data di mn mx msz sa out sb.
    lower_abi_decode data di mn mx msz sa = (out,sb) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    (sa.cs_blocks = sb.cs_blocks /\ data <> Label sa.cs_current_bb ==>
     frag_gas_free sa sb)
Proof
  cheat
QED
