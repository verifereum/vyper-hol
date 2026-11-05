(* Concrete obstruction to the frozen, unrestricted fragment-facts claim. *)
Theory exprSimAbiDecodeCounterexample
Ancestors
  exprSimAbiGasBridge builtinAbi compileEnv fragExec

Definition decode_witness_start_def:
  decode_witness_start : compile_state =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Theorem lower_abi_decode_label_counterexample:
  let sa = decode_witness_start;
      sb = SND (lower_abi_decode (Label "entry") (DecComplex F []) 0 0 0 sa)
  in sa.cs_blocks = sb.cs_blocks /\ ~frag_gas_free sa sb
Proof
  EVAL_TAC
QED

Theorem lower_abi_decode_frag_facts_false:
  ~(!data di mn mx msz sa out sb.
    lower_abi_decode data di mn mx msz sa = (out,sb) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    (sa.cs_blocks = sb.cs_blocks ==> frag_gas_free sa sb))
Proof
  mp_tac lower_abi_decode_label_counterexample >>
  pure_rewrite_tac [LET_THM] >>
  Cases_on `lower_abi_decode (Label "entry") (DecComplex F []) 0 0 0
              decode_witness_start` >>
  simp[] >> metis_tac[]
QED
