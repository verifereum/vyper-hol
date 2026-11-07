(* Closed fixture definitions retain the actual compiler output, so that
   execution/ghost auditing cannot accidentally certify a hand-written program. *)
Theory bodyPtrBytestringBuiltinsConcatRunProbe
Ancestors bodyPtrBytestringBuiltinsConcatAccessProbe vyperCompiler compileVyper

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:160)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``];

Definition concat_probe_compiled_def:
  concat_probe_compiled = compile_expr
    (build_compile_env [] External Nonpayable "f" [] NoneT [] F)
    (BaseT (BytesT (Dynamic 2)))
    (Builtin (BaseT (BytesT (Dynamic 2))) (Concat 2)
      [Literal (BaseT (BytesT (Fixed 1))) (BytesL [1w]);
       Literal (BaseT (BytesT (Fixed 1))) (BytesL [2w])])
    (initial_compile_state "entry")
End

Theorem concat_probe_literal_callback:
  !ce st bs bound.
    expr_size (Literal (BaseT (BytesT (Fixed 1))) (BytesL bs)) < bound ==>
    lower_value (expr_child_callback bound compile_expr) ce
      (BaseT (BytesT (Fixed 1)))
      (Literal (BaseT (BytesT (Fixed 1))) (BytesL bs)) st =
    (Lit (typed_val_to_w256 (BaseTV (BytesT (Fixed 1))) (BytesV bs)),st)
Proof
  simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def,
       exprCallBoundsTheory.expr_child_callback_def,
       exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_expr_body_def, vyperASTTheory.expr_type_def,
       exprLoweringTheory.compile_literal_vv_def,
       exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def]
QED

Theorem concat_probe_compilation:
  (SND concat_probe_compiled).cs_current_insts =
    MAP (\(id,opc,ops,outs). mk_inst id opc ops outs)
    [(0,ALLOCA,[Lit 64w],["%0"]);
     (1,ADD,[Var "%0";Lit 32w],["%1"]);
     (2,ALLOCA,[Lit 64w],["%2"]);
     (3,MSTORE,[Var "%2";Lit 0w],[]);
     (4,MLOAD,[Var "%2"],["%3"]);
     (5,ADD,[Var "%1";Var "%3"],["%4"]);
     (6,MSTORE,[Var "%4";Lit (word_of_bytes_be (PAD_RIGHT 0w 32 [1w]))],[]);
     (7,ADD,[Var "%3";Lit 1w],["%5"]);
     (8,MSTORE,[Var "%2";Var "%5"],[]);
     (9,MLOAD,[Var "%2"],["%6"]);
     (10,ADD,[Var "%1";Var "%6"],["%7"]);
     (11,MSTORE,[Var "%7";Lit (word_of_bytes_be (PAD_RIGHT 0w 32 [2w]))],[]);
     (12,ADD,[Var "%6";Lit 1w],["%8"]);
     (13,MSTORE,[Var "%2";Var "%8"],[]);
     (14,MLOAD,[Var "%2"],["%9"]);
     (15,MSTORE,[Var "%0";Var "%9"],[])]
Proof
  simp[concat_probe_compiled_def, exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_expr_body_def,
       exprLoweringTheory.compile_builtin_dispatch_component_eq,
       exprLoweringTheory.compile_builtin_dispatch_body_def,
       exprLoweringTheory.compile_concat_def,
       exprLoweringTheory.lower_value_def,
       exprLoweringTheory.compile_literal_vv_def,
       exprLoweringTheory.unwrap_value_def] >>
  simp[vyperASTTheory.expr_type_def, compileEnvTheory.is_bytestring_type_def,
       exprLoweringTheory.compile_concat_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def] >>
  simp[concat_probe_literal_callback, vyperASTTheory.expr_size_def,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``] >>
  EVAL_TAC
QED

(* A finite prefix fold keeps failed machine steps explicit as NONE and threads
   the real instruction ghost update; it is only a closed audit fixture. *)
Definition concat_probe_prefix_def:
  concat_probe_prefix =
    FOLDL (\acc inst.
      case acc of NONE => NONE | SOME (s,G) =>
        case step_inst_base inst s of
          OK u => SOME (u with vs_inst_idx := SUC s.vs_inst_idx,
                        step_prov [] G inst u)
        | _ => NONE)
      (SOME ((init_venom_state "entry") with vs_alloca_next := 256,FEMPTY))
      (TAKE 11 (SND concat_probe_compiled).cs_current_insts)
End

Theorem concat_probe_prefix_destination:
  ?s G. concat_probe_prefix = SOME (s,G) /\
    lookup_var "%7" s = SOME 289w /\
    FLOOKUP G "%7" = SOME (256,64) /\
    s.vs_inst_idx = 11
Proof
  rewrite_tac[concat_probe_prefix_def, concat_probe_compilation] >>
  CONV_TAC (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.the_compset ()))) >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
       venomStateTheory.lookup_var_def]
QED

Theorem concat_probe_second_store:
  EL 11 (SND concat_probe_compiled).cs_current_insts =
    mk_inst 11 MSTORE
      [Var "%7";Lit (word_of_bytes_be (PAD_RIGHT 0w 32 [2w]))] []
Proof
  simp[concat_probe_compilation]
QED

Theorem concat_probe_prefix_unsafe_store:
  ?s G. concat_probe_prefix = SOME (s,G) /\
    !lo fn. ~in_revert_forward fn s ==>
      ~access_ok lo G fn
        (EL 11 (SND concat_probe_compiled).cs_current_insts) s
Proof
  mp_tac concat_probe_prefix_destination >> strip_tac >>
  qexistsl_tac [`s`,`G`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_tac >> rewrite_tac[concat_probe_second_store] >>
  irule concat_overhang_access_failure >>
  simp[venomStateTheory.eval_operand_def] >> qexists_tac `256` >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED
