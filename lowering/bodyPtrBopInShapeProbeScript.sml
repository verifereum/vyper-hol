(* Exact compiler-shape diagnostic, not a counterexample frame. *)
Theory bodyPtrBopInShapeProbe
Ancestors bodyPtrBopInSourceFrame words venomExecSemantics

Theorem probe_exact_instructions:
  (SND (compile_expr probe_cenv (BaseT BoolT) probe_expr
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>)).cs_current_insts =
  [mk_inst 0 ALLOCA [Lit 64w] ["%0"];
   mk_inst 1 MSTORE [Var "%0"; Lit 1w] [];
   mk_inst 2 ADD [Var "%0"; Lit 32w] ["%1"];
   mk_inst 3 MSTORE [Var "%1"; Lit (n2w (97 * 2 ** 248))] [];
   mk_inst 4 ALLOCA [Lit 64w] ["%2"];
   mk_inst 5 MSTORE [Var "%2"; Lit 1w] [];
   mk_inst 6 ADD [Var "%2"; Lit 32w] ["%3"];
   mk_inst 7 MSTORE [Var "%3"; Lit (n2w (97 * 2 ** 248))] [];
   mk_inst 8 EQ [Var "%0"; Var "%2"] ["%4"]]
Proof
  EVAL_TAC >> simp[w2n_n2w, n2w_11, dimword_def,
    venomMemPropsTheory.dimindex_256, dimindex_8, bool_to_word_def]
QED

(* Compiler-producer audit (source locations in this checkout):
   exprLowering:705-713: singleton membership emits EQ of the two raw
     allocated pointers. Membership is rejected by supportedExprForms:68-69.
   exprLowering:561-570: Eq/NotEq can emit that raw EQ, but support at
     supportedExprForms:59-60 requires supported_word_type of the left operand.
     The two StringT literals here do not meet that restriction.
   exprLowering:3060-3069: bytestring equality instead hashes both buffers
     before EQ. It neither supplies this suffix nor meets the word-only support
     restriction. It is not a supported incidental-code candidate.
   exprLowering:738-775: array membership loop compares a loaded element with
     needle, with control-flow and stride instructions, not this straight-line
     pair of literal buffers. Membership is also unsupported.
   Other EQ producers: moduleLowering:34,69,253 compare method selectors;
     context:179,396,404 compare counters or lock words with literals;
     stmtLowering:1201,1283 compare loop counters and bounds;
     builtinStrings:47,51 compare counters with zero;
     abiEncoder:46 compares a word with its canonicalization;
     exprLowering:303,327,353,357,400,1711 compare arithmetic/check results.
     None directly consumes this pair of fresh literal allocation results.
   Pipeline boundary: compileVyper:1402-1428 calls run_lowering, whose
     vyperCompiler:630-648 extracts the raw generated context and checks it.
     There is no optimization pass in the cu_context used by body_inv;
     the policy's final-assembly choice does not rewrite that context here.
   Result: no plausible supported candidate identified by this trace, so no
     whole-program candidate was evaluated. This is NOT a universal exclusion:
     arbitrary prefixes, other nested source shapes, and exact code placement
     in supported contexts remain unresolved. *)
