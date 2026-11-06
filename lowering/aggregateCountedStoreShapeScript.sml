(* Representative multi-block typed-copy boundary probe. *)
Theory aggregateCountedStoreShape
Ancestors
  exprSimAbiGasBridge context compileEnv vyperAST venomExecSemantics

Theorem aggregate_typed_sarray_counted_shape_probe:
  let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
              cs_current_bb := "entry"; cs_current_insts := [];
              cs_blocks := []; cs_data_sections := [] |> in
  let sb = SND (compile_copy_sarray_typed ce (Var "dst") (BaseT (UintT 256))
                  (Var "src") (TupleT []) 2 sa) in
  let bb = <| bb_label := sb.cs_current_bb;
              bb_instructions := [mk_inst 1000 PHI [] ["phi"]] |> in
  let fn = (ARB:ir_function) with fn_blocks := bb :: sb.cs_blocks in
  frag_gas_free sa sb /\
  sb.cs_current_insts = [] /\
  LENGTH (emitted_blocks sa sb) = 3 /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 1
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED
