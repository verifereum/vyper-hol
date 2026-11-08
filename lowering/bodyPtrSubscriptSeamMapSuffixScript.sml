(* Exact instruction layout of the mapping-slot hash. *)
Theory bodyPtrSubscriptSeamMapSuffix
Ancestors
  bodyPtrSubscriptSeamMapKey bodyPtrSubscriptScratchTransfer
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsKeccak
  exprLowering exprLoweringProps context compileEnv emitHelper emitHelperProps
  venomInst ASCIInumbers rich_list arithmetic list

Theorem mapping_slot_hash_emission:
  !slot key sa op sb.
    compile_mapping_subscript slot key sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var));slot] [];
       mk_inst (sa.cs_next_id+2) ADD
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var+1)));key] [];
       mk_inst (sa.cs_next_id+4) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, ADD_ASSOC] >>
  strip_tac >> gvs[APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem mapping_slot_hash_shape:
  !slot key sa op sb.
    compile_mapping_subscript slot key sa = (op,sb) ==>
    ?ia is ip ik ih p q h.
      emitted_insts sa sb =
        [mk_inst ia ALLOCA [Lit 64w] [p];
         mk_inst is MSTORE [Var p;slot] [];
         mk_inst ip ADD [Var p;Lit 32w] [q];
         mk_inst ik MSTORE [Var q;key] [];
         mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;q;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> q /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule mapping_slot_hash_emission >> strip_tac >>
  qexistsl [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `sa.cs_next_id+3`, `sa.cs_next_id+4`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED
