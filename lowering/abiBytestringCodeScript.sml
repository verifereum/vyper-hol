(* TOP-LEVEL: the bytestring ABI encoder emits this exact ten-instruction
   program, with eight distinct generated names. These are descriptions of
   the existing compiler's output, not a replacement lowering algorithm. *)
Theory abiBytestringCode
Ancestors
  abiEncoder context compileEnv emitHelper exprLoweringProps
  venomInst list rich_list ASCIInumbers

Definition compiler_var_names_def:
  compiler_var_names base count =
    GENLIST (\i. STRING #"%" (toString (base + i))) count
End

Theorem compiler_var_names_length[simp]:
  !base count. LENGTH (compiler_var_names base count) = count
Proof
  simp[compiler_var_names_def]
QED

Theorem compiler_var_names_distinct:
  !base count. ALL_DISTINCT (compiler_var_names base count)
Proof
  simp[compiler_var_names_def, ALL_DISTINCT_GENLIST]
QED

Theorem compiler_var_names_EL:
  !base count i. i < count ==>
    EL i (compiler_var_names base count) = STRING #"%" (toString (base + i))
Proof
  simp[compiler_var_names_def, EL_GENLIST]
QED

Theorem compiler_var_names_later:
  !base num_names n.
    base + num_names <= n ==>
    EVERY (\name. Var (STRING #"%" (toString n)) <> Var name)
      (compiler_var_names base num_names)
Proof
  simp[compiler_var_names_def, EVERY_GENLIST] >> decide_tac
QED

Definition bytestring_encoder_insts_def:
  bytestring_encoder_insts id names dst src =
    [mk_inst id MLOAD [src] [EL 0 names];
     mk_inst (id + 1) ADD [Lit 31w; Var (EL 0 names)] [EL 1 names];
     mk_inst (id + 2) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (EL 1 names)] [EL 2 names];
     mk_inst (id + 3) ADD [dst; Var (EL 2 names)] [EL 3 names];
     mk_inst (id + 4) MSTORE [Var (EL 3 names); Lit 0w] [];
     mk_inst (id + 5) ADD [Lit 32w; Var (EL 0 names)] [EL 4 names];
     mk_inst (id + 6) MCOPY [dst; src; Var (EL 4 names)] [];
     mk_inst (id + 7) ADD [Lit 31w; Var (EL 0 names)] [EL 5 names];
     mk_inst (id + 8) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (EL 5 names)] [EL 6 names];
     mk_inst (id + 9) ADD [Lit 32w; Var (EL 6 names)] [EL 7 names]]
End

Theorem bytestring_encoder_straight:
  !id names dst src.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (bytestring_encoder_insts id names dst src)
Proof
  simp[bytestring_encoder_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem compile_abi_bytestring_code:
  !dst src cap cs op cs'.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') ==>
    emitted_insts cs cs' = bytestring_encoder_insts cs.cs_next_id
      (compiler_var_names cs.cs_next_var 8) dst src /\
    op = Var (EL 7 (compiler_var_names cs.cs_next_var 8)) /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 8 /\ cs'.cs_next_id = cs.cs_next_id + 10
Proof
  rw[Once compile_abi_encode_child_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp[bytestring_encoder_insts_def, compiler_var_names_EL,
    emitted_insts_def, DROP_APPEND1, DROP_LENGTH_NIL, same_blocks_def]
QED
