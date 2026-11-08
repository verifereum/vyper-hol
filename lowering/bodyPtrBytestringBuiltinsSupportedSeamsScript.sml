(* Selector-bearing ABI encode is supported; this concrete prologue is a
   two-sided barrier for Concat headers. It does not certify encoder tails. *)
Theory bodyPtrBytestringBuiltinsSupportedSeams
Ancestors bodyPtrBytestringBuiltinsWindows venomInst words list
  builtinAbi abiEncoder context emitHelper compileEnv abiBuiltinEncodeCode

Theorem selector_prologue_window_barrier:
  !xs ys i0 i1 i2 i3 bytes buf data midptr selector
     j0 j1 j2 j3 size b d off.
  (?p q.
     xs ++ ([mk_inst i0 ALLOCA [Lit (n2w bytes)] [buf];
            mk_inst i1 ADD [Var buf; Lit 36w] [data];
            mk_inst i2 ADD [Var buf; Lit 32w] [midptr];
            mk_inst i3 MSTORE [Var midptr; Lit selector] []] ++ ys) =
     p ++ [mk_inst j0 ALLOCA [Lit (n2w size)] [b];
           mk_inst j1 ADD [Var b; Lit 32w] [d];
           mk_inst j2 ALLOCA [Lit 64w] [off];
           mk_inst j3 MSTORE [Var off; Lit 0w] []] ++ q) ==>
  (?p q. xs = p ++ [mk_inst j0 ALLOCA [Lit (n2w size)] [b];
                    mk_inst j1 ADD [Var b; Lit 32w] [d];
                    mk_inst j2 ALLOCA [Lit 64w] [off];
                    mk_inst j3 MSTORE [Var off; Lit 0w] []] ++ q) \/
  (?p q. ys = p ++ [mk_inst j0 ALLOCA [Lit (n2w size)] [b];
                    mk_inst j1 ADD [Var b; Lit 32w] [d];
                    mk_inst j2 ALLOCA [Lit 64w] [off];
                    mk_inst j3 MSTORE [Var off; Lit 0w] []] ++ q)
Proof
  rpt gen_tac >>
  once_rewrite_tac[four_window_append] >>
  once_rewrite_tac[four_window_append] >>
  simp[mk_inst_def] >> strip_tac
  >- metis_tac[]
  >- (`p = [] /\ q = []` by
        (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >>
         simp_tac (srw_ss()) [LENGTH_APPEND, LENGTH] >> strip_tac >>
         `LENGTH p = 0 /\ LENGTH q = 0` by decide_tac >> gvs[]) >>
      gvs[]) >>
  metis_tac[]
QED

Theorem selector_setup_instructions:
  abi_builtin_encode_setup (SOME selector) maxlen sa = (ops,sm) ==>
  ?buf data midptr.
    ops = (Var buf,Var data) /\
    sm.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA
         [Lit (n2w (32 + 32 * word_size (maxlen + 4)))] [buf];
       mk_inst (sa.cs_next_id + 1) ADD [Var buf; Lit 36w] [data];
       mk_inst (sa.cs_next_id + 2) ADD [Var buf; Lit 32w] [midptr];
       mk_inst (sa.cs_next_id + 3) MSTORE
         [Var midptr; Lit (selector << 224)] []]
Proof
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[GSYM APPEND_ASSOC] >> metis_tac[]
QED

(* This connects the barrier's literal list to an actual compiler call. The
   recursive encoder and final length store deliberately remain opaque. *)
Theorem lower_abi_encode_selector_seam:
  lower_abi_encode ensure (SOME selector) src info maxlen sa = (out,sb) ==>
  ?buf data midptr sm len se.
    out = Var buf /\
    sm.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA
         [Lit (n2w (32 + 32 * word_size (maxlen + 4)))] [buf];
       mk_inst (sa.cs_next_id + 1) ADD [Var buf; Lit 36w] [data];
       mk_inst (sa.cs_next_id + 2) ADD [Var buf; Lit 32w] [midptr];
       mk_inst (sa.cs_next_id + 3) MSTORE
         [Var midptr; Lit (selector << 224)] []] /\
    compile_abi_encode_to_buf (Var data) src info sm = (len,se) /\
    abi_builtin_encode_finish (Var buf) len 4 se = ((),sb)
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule selector_setup_instructions >> strip_tac >> gvs[] >>
  metis_tac[]
QED
