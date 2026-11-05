(* Local generated-code probe only: not a deployment counterexample. *)
Theory ctorDeployMemoryRunMemPrefixDynamic
Ancestors
  ctorDeployMemoryRunMemPrefixPrimitive abiEncoder compileEnv emitHelper
  exprLoweringProps venomState venomExecSemantics instMemFrontier venomInst
  vyperCompiler list words

Theorem ctor_prefix_dynamic_pointer_compile:
  st.cs_next_var = 0 /\ st.cs_next_id = 0 ==>
  compile_getelemptr_abi (Lit 0w) T 0 MLOAD (Lit 128w) st =
    (Var "%2", st with <| cs_next_var := 5; cs_next_id := 6;
      cs_current_insts := st.cs_current_insts ++
        [mk_inst 0 ADD [Lit 0w; Lit 0w] ["%0"];
         mk_inst 1 MLOAD [Var "%0"] ["%1"];
         mk_inst 2 ADD [Lit 0w; Var "%1"] ["%2"];
         mk_inst 3 LT [Var "%2"; Lit 0w] ["%3"];
         mk_inst 4 ISZERO [Var "%3"] ["%4"];
         mk_inst 5 ASSERT [Var "%4"] []] |>)
Proof
  strip_tac >>
  simp[compile_getelemptr_abi_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, APPEND_ASSOC] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, APPEND_ASSOC] >> EVAL_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem ctor_prefix_dynamic_bytes_compile:
  st.cs_next_var = 5 /\ st.cs_next_id = 6 ==>
  compile_abi_decode_to_buf (Lit 64w) (Var "%2") MLOAD (Lit 128w)
    (DecBytestring 0) st =
    ((), st with <| cs_next_var := 12; cs_next_id := 16;
      cs_current_insts := st.cs_current_insts ++
        [mk_inst 6 MLOAD [Var "%2"] ["%5"];
         mk_inst 7 GT [Var "%5"; Lit 0w] ["%6"];
         mk_inst 8 ISZERO [Var "%6"] ["%7"];
         mk_inst 9 ASSERT [Var "%7"] [];
         mk_inst 10 ADD [Var "%2"; Lit 32w] ["%8"];
         mk_inst 11 ADD [Var "%8"; Var "%5"] ["%9"];
         mk_inst 12 GT [Var "%9"; Lit 128w] ["%10"];
         mk_inst 13 ISZERO [Var "%10"] ["%11"];
         mk_inst 14 ASSERT [Var "%11"] [];
         mk_inst 15 MCOPY [Lit 64w; Var "%2"; Lit 32w] []] |>)
Proof
  strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, APPEND_ASSOC] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, APPEND_ASSOC] >> EVAL_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem ctor_prefix_dynamic_pointer_run:
  case run_inst_seq
    [mk_inst 0 ADD [Lit 0w; Lit 0w] ["%0"];
     mk_inst 1 MLOAD [Var "%0"] ["%1"];
     mk_inst 2 ADD [Lit 0w; Var "%1"] ["%2"];
     mk_inst 3 LT [Var "%2"; Lit 0w] ["%3"];
     mk_inst 4 ISZERO [Var "%3"] ["%4"];
     mk_inst 5 ASSERT [Var "%4"] []]
    ((init_venom_state "entry") with
       <| vs_memory := REPLICATE 30 0w ++ [16w; 0w]; vs_alloca_next := 128 |>) of
    OK t => t.vs_alloca_next = 128 /\
            eval_operand (Var "%2") t = SOME 4096w /\
            ~inst_mem_below_frontier (mk_inst 6 MLOAD [Var "%2"] ["%5"]) t
  | _ => F
Proof
  EVAL_TAC >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

(* Includes the actual compiler calls: the preceding execution lemma alone
   would not establish that the unsafe read is compiler-generated. *)
Theorem ctor_prefix_dynamic_read_probe:
  let c0 = initial_compile_state "entry";
      (ptr,c1) = compile_getelemptr_abi (Lit 0w) T 0 MLOAD (Lit 128w) c0;
      (u,c2) = compile_abi_decode_to_buf (Lit 64w) ptr MLOAD (Lit 128w)
                 (DecBytestring 0) c1;
      code = emitted_insts c0 c2;
      s = (init_venom_state "entry") with
        <| vs_memory := REPLICATE 30 0w ++ [16w; 0w]; vs_alloca_next := 128 |>
  in
    LENGTH (emitted_insts c0 c1) = 6 /\
    (EL 6 code).inst_opcode = MLOAD /\
    case run_inst_seq (TAKE 6 code) s of
      OK t => t.vs_alloca_next = 128 /\
              eval_operand (Var "%2") t = SOME 4096w /\
              ~inst_mem_below_frontier (EL 6 code) t
    | _ => F
Proof
  simp[ctor_prefix_dynamic_pointer_compile, ctor_prefix_dynamic_bytes_compile,
    initial_compile_state_def, emitted_insts_def] >>
  ACCEPT_TAC ctor_prefix_dynamic_pointer_run
QED
