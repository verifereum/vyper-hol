(* Finite supported-word alternatives, not a full entry witness. *)
Theory bodyPtrBopInWordProbe
Ancestors bodyPtrBopInSourceFrame exprLowering vyperCompiler supportedProgram
  ptrSafeRun ptrDiscipline words venomMemProps vyperTypeSystem

Theorem bool_singleton_matches_eq:
  compile_expr probe_cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT BoolT) (BoolL T);
       Builtin (ArrayT (BaseT BoolT) (Fixed 1))
         (MakeArray (SOME (BaseT BoolT)) (Fixed 1))
         [Literal (BaseT BoolT) (BoolL T)]])
    (initial_compile_state "entry") =
  compile_expr probe_cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop Eq)
      [Literal (BaseT BoolT) (BoolL T);
       Literal (BaseT BoolT) (BoolL T)])
    (initial_compile_state "entry")
Proof
  EVAL_TAC
QED

Theorem bool_equality_program_supported:
  supported_program
    [FunctionDecl External View F F "probe" [] [] (BaseT BoolT)
      [Return (SOME (Builtin (BaseT BoolT) (Bop Eq)
        [Literal (BaseT BoolT) (BoolL T);
         Literal (BaseT BoolT) (BoolL T)]))]]
Proof
  EVAL_TAC >> simp[dimword_def, dimindex_256]
QED

Theorem literal_eq_ignores_arbitrary_ghost:
  access_ok 0 G fn (mk_inst 0 EQ [Lit 1w; Lit 1w] ["%0"]) s /\
  taint_ok fn tn (mk_inst 0 EQ [Lit 1w; Lit 1w] ["%0"]) s
Proof
  EVAL_TAC >> simp[]
QED

Theorem uint_singleton_notin_matches_neq:
  compile_expr probe_cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop NotIn)
      [Literal (BaseT (UintT 256)) (IntL 7);
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
         [Literal (BaseT (UintT 256)) (IntL 7)]])
    (initial_compile_state "entry") =
  compile_expr probe_cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop NotEq)
      [Literal (BaseT (UintT 256)) (IntL 7);
       Literal (BaseT (UintT 256)) (IntL 7)])
    (initial_compile_state "entry")
Proof
  EVAL_TAC
QED

Theorem word_membership_source_results:
  evaluate_binop BoolTV (ArrayTV (BaseTV BoolT) (Fixed 1)) In
    (BoolV T) (ArrayV (DynArrayV [BoolV T])) = INL (BoolV T) /\
  evaluate_binop (Unsigned 256) (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) NotIn
    (IntV 7) (ArrayV (DynArrayV [IntV 7])) = INL (BoolV F)
Proof
  EVAL_TAC >> simp[dimword_def, dimindex_256]
QED

Theorem empty_membership_codegen:
  compile_list_membership_in needle [] st = (Lit 0w, st) /\
  compile_list_membership_notin needle [] st = (Lit 1w, st)
Proof
  simp[compile_list_membership_in_def, compile_list_membership_notin_def,
       compileEnvTheory.comp_return_def]
QED

Theorem wrong_arity_membership_untyped:
  ~well_typed_expr env (Builtin (BaseT BoolT) (Bop In) []) /\
  ~well_typed_expr env (Builtin (BaseT BoolT) (Bop NotIn) [e])
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def]
QED

