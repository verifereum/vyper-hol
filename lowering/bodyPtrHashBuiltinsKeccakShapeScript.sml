(* Hide the compiler's concrete fresh names from dynamic hash consumers. *)
Theory bodyPtrHashBuiltinsKeccakShape
Ancestors builtinHashing emitHelper emitHelperProps compileEnv
  exprLoweringProps venomInst ASCIInumbers rich_list

Theorem hash_keccak_bytes_emission:
  !x sa op sb.
    compile_keccak256_bytes x sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [x]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) ADD [x;Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+2) SHA3
         [Var (STRING #"%" (toString (sa.cs_next_var+1)));
          Var (STRING #"%" (toString sa.cs_next_var))]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_keccak256_bytes_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem hash_keccak_bytes_shape:
  !x sa op sb.
    compile_keccak256_bytes x sa = (op,sb) ==>
    ?il ia ih l p h.
      emitted_insts sa sb =
        [mk_inst il MLOAD [x] [l]; mk_inst ia ADD [x;Lit 32w] [p];
         mk_inst ih SHA3 [Var p;Var l] [h]] /\
      op = Var h /\ ALL_DISTINCT [l;p;h] /\
      (!z. not_fresh_at sa z ==> z <> l /\ z <> p /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule hash_keccak_bytes_emission >> strip_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED
