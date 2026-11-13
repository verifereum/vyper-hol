(* lower_abi_encode does not depend on its entry block's label or on the IDs
   of the instructions already in it, and the code it emits meets the
   relabeled bridges' shape premises. *)
Theory exprSimAbiEncodeOblivious
Ancestors
  exprSimAbiGasBridge builtinAbi compileEnv fragExec
  exprSimAbiEncodeObliviousContext exprSimAbiEncodeObliviousSimulation
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousOperands

Theorem lower_abi_encode_start_oblivious:
  !ensure mid src info maxlen.
    frag_start_oblivious (lower_abi_encode ensure mid src info maxlen)
Proof
  simp[entry_action_oblivious, entry_action_lower_abi_encode]
QED

Theorem lower_abi_encode_frag_facts:
  !ensure mid src info maxlen sa out sb.
    lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
    (!l. src <> Label l) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    (sa.cs_blocks = sb.cs_blocks ==> frag_gas_free sa sb)
Proof
  metis_tac[lower_abi_encode_structural_facts, lower_abi_encode_no_block_gas_free]
QED
