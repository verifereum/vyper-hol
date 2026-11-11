Theory bodyPtrIfExpScalarProbe
Ancestors
  bodyPtrIfExpHeaderProbe supportedProgram
  stmtLowering exprLoweringProps builtinSimple venomState venomExecSemantics
  context compileEnv exprLowering vyperAST emitHelper venomInst vyperCompiler
  integer words venomMemProps

(* Named finite AST fixtures make compiler computation readable; these
   definitions assert neither a call simulation nor a body frame. *)
Definition scalar_probe_ty_def:
  scalar_probe_ty = TupleT [BaseT (BytesT (Dynamic 32)); BaseT (UintT 256)]
End

Definition scalar_probe_expr_def:
  scalar_probe_expr = Builtin scalar_probe_ty (MakeArray NONE (Fixed 2))
    [TypeBuiltin (BaseT (BytesT (Dynamic 32))) Empty
       (BaseT (BytesT (Dynamic 32))) [];
     Literal (BaseT (UintT 256)) (IntL 42)]
End

Definition scalar_probe_tops_def:
  scalar_probe_tops =
    [FunctionDecl Internal Pure F F "helper" [] [] scalar_probe_ty
      [Return (SOME scalar_probe_expr)]]
End

Theorem scalar_probe_supported_returns:
  supported_return_type scalar_probe_tops scalar_probe_ty /\
  supported_return_type scalar_probe_tops
    (TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)])
Proof
  EVAL_TAC
QED

Theorem scalar_probe_supported_module:
  supported_program scalar_probe_tops
Proof
  EVAL_TAC
QED

Theorem scalar_probe_compile:
  !ce. (SND (lower_value compile_expr ce scalar_probe_ty scalar_probe_expr
      (initial_compile_state "entry"))).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 96w] ["%0"];
     mk_inst 1 ALLOCA [Lit 64w] ["%1"];
     mk_inst 2 MSTORE [Var "%1"; Lit 0w] [];
     mk_inst 3 ADD [Var "%0"; Lit 0w] ["%2"];
     mk_inst 4 MLOAD [Var "%1"] ["%3"];
     mk_inst 5 ADD [Var "%3"; Lit 31w] ["%4"];
     mk_inst 6 AND [Var "%4"; Lit (i2w (-32))] ["%5"];
     mk_inst 7 ADD [Var "%5"; Lit 32w] ["%6"];
     mk_inst 8 MCOPY [Var "%2"; Var "%1"; Var "%6"] [];
     mk_inst 9 ADD [Var "%0"; Lit 64w] ["%7"];
     mk_inst 10 MSTORE [Var "%7"; Lit 42w] []]
Proof
  simp[scalar_probe_expr_def, scalar_probe_ty_def,
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
       mk_ptr_def] >> EVAL_TAC >> simp[]
QED

Theorem scalar_probe_return_run:
  !ce. case run_inst_seq
    ((SND (lower_value compile_expr ce scalar_probe_ty scalar_probe_expr
      (initial_compile_state "entry"))).cs_current_insts ++
     [mk_inst 11 MCOPY [Lit 256w; Var "%0"; Lit 96w] []])
    ((init_venom_state "entry") with vs_memory := REPLICATE 512 0w) of
    OK s => mload 320 s = 42w /\ mload 352 s = 0w /\
      val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (UintT 256)])
        (ArrayV (TupleV [BytesV []; IntV 42])) 256 s.vs_memory /\
      ~val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
        (ArrayV (TupleV [BytesV []; IntV 42])) 256 s.vs_memory
  | _ => F
Proof
  rewrite_tac[scalar_probe_compile] >>
  simp[integer_wordTheory.i2w_def] >>
  CONV_TAC (computeLib.CBV_CONV
    (computeLib.add_thms [integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def]
      (wordsLib.add_words_compset true
        (computeLib.copy (computeLib.the_compset()))))) >> simp[]
QED

(* The copied physical return has uint42 at +64, not annotation offset +96.
   expr_post and ptr_val_ok of an arm with bytes64 annotation require the
   latter interpretation. Thus this run fails that operand post already;
   it is not evidence of an IfExp violating a satisfied operand judgment.
   No whole-call reachability or universal operand validity is asserted. *)
