(* Checked counterexample to the unrestricted Label-source fragment facts. *)
Theory exprSimAbiEncodeObliviousCounterexample
Ancestors
  exprSimAbiGasBridge builtinAbi abiEncoder compileEnv fragExec

Definition counterexample_start_def:
  counterexample_start = (ARB : compile_state) with
    <| cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_next_id := 0; cs_next_var := 0 |>
End

Definition counterexample_end_def:
  counterexample_end = SND
    (lower_abi_encode F NONE (Label "entry") AbiPrimWord 0
      counterexample_start)
End

Theorem counterexample_blocks_and_gas:
  counterexample_start.cs_blocks = counterexample_end.cs_blocks /\
  ~frag_gas_free counterexample_start counterexample_end
Proof
  simp[counterexample_end_def, lower_abi_encode_def,
       compile_abi_encode_child_def, compile_abi_encode_static_def,
       contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def,
       counterexample_start_def, frag_gas_free_def, frag_code_def,
       emitted_blocks_def, exprLoweringPropsTheory.emitted_insts_def]
QED

Theorem lower_abi_encode_frag_facts_false:
  ~(!ensure mid src info maxlen sa out sb.
    lower_abi_encode ensure mid src info maxlen sa = (out,sb) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    (sa.cs_blocks = sb.cs_blocks ==> frag_gas_free sa sb))
Proof
  strip_tac >>
  first_x_assum (qspecl_then
    [`ARB`, `NONE`, `Label "entry"`, `AbiPrimWord`, `0`,
     `counterexample_start`] mp_tac) >>
  mp_tac counterexample_blocks_and_gas >>
  pure_rewrite_tac[counterexample_end_def, lower_abi_encode_def] >>
  qmatch_goalsub_abbrev_tac `SND witness_result` >>
  Cases_on `witness_result` >> simp[] >> metis_tac[]
QED
