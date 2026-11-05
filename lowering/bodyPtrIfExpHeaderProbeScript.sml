Theory bodyPtrIfExpHeaderProbe
Ancestors
  bodyPtrIfExpCallerLayout stmtLowering exprLoweringProps builtinSimple
  venomState venomExecSemantics context compileEnv exprLowering vyperAST
  emitHelper venomInst vyperCompiler integer words venomMemProps

val header_probe_conv = computeLib.CBV_CONV
  (computeLib.add_thms [integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def]
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))));

(* Named fixtures keep the concrete compiler experiment readable. They are
   not replacement contracts or new simulation predicates. *)
Definition header_probe_ty_def:
  header_probe_ty = TupleT [BaseT (BytesT (Dynamic 32));
                            ArrayT (BaseT (UintT 256)) (Dynamic 1)]
End

Definition header_probe_expr_def:
  header_probe_expr = Builtin header_probe_ty (MakeArray NONE (Fixed 2))
    [TypeBuiltin (BaseT (BytesT (Dynamic 32))) Empty
       (BaseT (BytesT (Dynamic 32))) [];
     TypeBuiltin (ArrayT (BaseT (UintT 256)) (Dynamic 1)) Empty
       (ArrayT (BaseT (UintT 256)) (Dynamic 1)) []]
End

Theorem header_probe_sizes:
  !ce. type_memory_bytes ce header_probe_ty = 128 /\
    type_memory_bytes ce (BaseT (BytesT (Dynamic 32))) = 64 /\
    type_memory_bytes ce (BaseT (BytesT (Dynamic 64))) = 96
Proof
  simp[header_probe_ty_def, type_memory_bytes_def]
QED

Theorem header_probe_compile:
  !ce. (SND (lower_value compile_expr ce header_probe_ty header_probe_expr
      (initial_compile_state "entry"))).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
     mk_inst 1 ALLOCA [Lit 64w] ["%1"];
     mk_inst 2 MSTORE [Var "%1"; Lit 0w] [];
     mk_inst 3 ADD [Var "%0"; Lit 0w] ["%2"];
     mk_inst 4 MLOAD [Var "%1"] ["%3"];
     mk_inst 5 ADD [Var "%3"; Lit 31w] ["%4"];
     mk_inst 6 AND [Var "%4"; Lit (i2w (-32))] ["%5"];
     mk_inst 7 ADD [Var "%5"; Lit 32w] ["%6"];
     mk_inst 8 MCOPY [Var "%2"; Var "%1"; Var "%6"] [];
     mk_inst 9 ALLOCA [Lit 64w] ["%7"];
     mk_inst 10 MSTORE [Var "%7"; Lit 0w] [];
     mk_inst 11 ADD [Var "%0"; Lit 64w] ["%8"];
     mk_inst 12 MCOPY [Var "%8"; Var "%7"; Lit 64w] []]
Proof
  simp[header_probe_expr_def, header_probe_ty_def,
       lower_value_def, compile_expr_component_eq,
       compile_builtin_dispatch_component_eq, compile_builtin_dispatch_body_def,
       compile_make_tuple_def, compile_type_builtin_dispatch_component_eq,
       compile_type_builtin_dispatch_body_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       expr_type_def, is_word_type_def, is_bytestring_type_def,
       type_memory_bytes_def, lowered_value_type_def,
       compile_builtin_empty_complex_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, mk_inst_def, initial_compile_state_def,
       unwrap_value_def, as_ptr_val_def, base_ptr_def,
       compile_store_memory_def, compile_copy_memory_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def,
       mk_ptr_def]
  >> simp[oneline compile_copy_memory_def, emit_void_def, fresh_id_def,
          emit_def, mk_inst_def, as_ptr_val_def, unwrap_value_def,
          mk_ptr_def, is_word_type_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def]
  >> EVAL_TAC
QED

(* The return path uses equal physical types, hence copies the entire
   128-byte source buffer, including its dead array-data word at offset 96. *)
Theorem header_probe_return_compile:
  !ce src dst rpc st.
  compile_internal_return_from_env
    (ce with <| ce_return_buf := SOME (PtrVar dst 128);
                ce_returns_count := 0 |>)
    header_probe_ty header_probe_ty src rpc st =
  (do emit_void MCOPY [dst; src; Lit 128w];
      emit_inst RET [rpc] []
   od) st
Proof
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       header_probe_ty_def, compile_store_memory_def,
       is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
       oneline compile_copy_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]
QED

(* This is a local fixed run, NOT an admissible body frame or the frozen
   IfExp counterexample: the complete module and universal operand premise
   are deliberately not asserted. The MCOPY is the return writer above. *)
Theorem header_probe_return_run:
  !ce. case run_inst_seq
    ((SND (lower_value compile_expr ce header_probe_ty header_probe_expr
      (initial_compile_state "entry"))).cs_current_insts ++
     [mk_inst 13 MCOPY [Lit 256w; Var "%0"; Lit 128w] []])
    ((init_venom_state "entry") with vs_memory := REPLICATE 256 1w) of
    OK s => mload 320 s = 0w /\ mload 352 s <> 0w /\
      val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 32));
                  ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
        (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 s.vs_memory /\
      ~val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 64));
                  ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
        (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 s.vs_memory
  | _ => F
Proof
  rewrite_tac[header_probe_compile]
  >> simp[integer_wordTheory.i2w_def]
  >> CONV_TAC header_probe_conv
QED

Theorem header_probe_zero_memory_run:
  !ce. case run_inst_seq
    ((SND (lower_value compile_expr ce header_probe_ty header_probe_expr
      (initial_compile_state "entry"))).cs_current_insts ++
     [mk_inst 13 MCOPY [Lit 256w; Var "%0"; Lit 128w] []])
    ((init_venom_state "entry") with vs_memory := REPLICATE 256 0w) of
    OK s => mload 320 s = 0w /\ mload 352 s = 0w /\
      val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 64));
                  ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
        (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 s.vs_memory
  | _ => F
Proof
  rewrite_tac[header_probe_compile]
  >> simp[integer_wordTheory.i2w_def]
  >> CONV_TAC header_probe_conv
QED
