(* Source-level computations, not independent bytecode parity claims. *)
Theory evalCompilerGettersConstantsRegression
Ancestors compileVyper supportedDecls supportedProgram

Definition regression_uint_def:
  regression_uint = BaseT (UintT 256)
End

Definition regression_ref_def:
  regression_ref n = TopLevelName regression_uint (NONE,n)
End

Definition regression_constant_def:
  regression_constant n e = VariableDecl Private (Constant e) n regression_uint NONE
End

Definition regression_function_def:
  regression_function vis n =
    FunctionDecl vis View F F n [] [regression_ref "B"] regression_uint
      [Return (SOME (regression_ref "B"))]
End

Theorem getters_follow_explicit_functions_in_declaration_order:
  FST (classify_functions
    [VariableDecl (Public F) Storage "g" regression_uint (SOME 0);
     regression_function External "f";
     VariableDecl (Public T) Transient "h" regression_uint (SOME 1)]) =
  [(View,F,F,"f",[],[regression_ref "B"],regression_uint,
      [Return (SOME (regression_ref "B"))]);
   (View,F,F,"g",[],[],regression_uint,[Return (SOME (regression_ref "g"))]);
   (View,T,F,"h",[],[],regression_uint,[Return (SOME (regression_ref "h"))])]
Proof
  EVAL_TAC
QED

Theorem constants_expand_in_declaration_order:
  module_consts_env
    [regression_constant "A" (Name regression_uint "literal");
     regression_constant "B" (regression_ref "A")] [] =
    [("A", Name regression_uint "literal");("B", Name regression_uint "literal")]
Proof
  EVAL_TAC
QED

Theorem constants_reach_all_function_categories_and_defaults:
  classify_functions
    [regression_constant "A" (Name regression_uint "literal");
     regression_constant "B" (regression_ref "A");
     regression_function External "f";
     regression_function Internal "i";
     regression_function External "__default__";
     regression_function Deploy "__init__"] =
  ([(View,F,F,"f",[],[Name regression_uint "literal"],regression_uint,
       [Return (SOME (Name regression_uint "literal"))])],
   [(View,F,F,"i",[],[Name regression_uint "literal"],regression_uint,
       [Return (SOME (Name regression_uint "literal"))])],
   SOME (View,F,F,"__default__",[],[Name regression_uint "literal"],regression_uint,
       [Return (SOME (Name regression_uint "literal"))]),
   SOME (View,F,F,"__init__",[],[Name regression_uint "literal"],regression_uint,
       [Return (SOME (Name regression_uint "literal"))]))
Proof
  EVAL_TAC
QED

Theorem public_constant_getter_is_substituted:
  FST (classify_functions
    [VariableDecl (Public F) (Constant (Name regression_uint "literal"))
       "A" regression_uint NONE]) =
  [(View,F,F,"A",[],[],regression_uint,
       [Return (SOME (Name regression_uint "literal"))])]
Proof
  EVAL_TAC
QED

Theorem supported_public_literal_constant_getter:
  ?decl.
    decl = VariableDecl (Public F) (Constant (Literal regression_uint (IntL 7)))
      "A" regression_uint NONE /\
    supported_program [decl] /\
    public_getter decl =
      SOME (View,F,F,"A",[],[],regression_uint,[Return (SOME (regression_ref "A"))]) /\
    FST (classify_functions [decl]) =
      [(View,F,F,"A",[],[],regression_uint,
         [Return (SOME (Literal regression_uint (IntL 7)))])]
Proof
  qexists_tac `VariableDecl (Public F) (Constant (Literal regression_uint (IntL 7)))
    "A" regression_uint NONE` >>
  EVAL_TAC
QED

(* An unresolved top-level reference survives substitution and folding. *)
Theorem unsupported_constant_replacement_is_rejected:
  ?tops.
    tops = [regression_constant "A" (regression_ref "B")] /\
    supported_declaration_headers tops /\
    supported_declaration_names tops /\
    ALL_DISTINCT (supported_internal_function_names tops) /\
    EVERY (supported_declaration_body tops) tops /\
    ~supported_program tops
Proof
  qexists_tac `[regression_constant "A" (regression_ref "B")]` >>
  EVAL_TAC
QED

Theorem public_header_slot_and_constant_boundaries:
  supported_declaration_header []
    (VariableDecl (Public F) Storage "g" regression_uint (SOME 0)) /\
  supported_declaration_header []
    (VariableDecl (Public T) Transient "g" regression_uint (SOME 0)) /\
  ~supported_declaration_header []
    (VariableDecl (Public F) Storage "g" regression_uint NONE) /\
  supported_declaration_header []
    (regression_constant "A" (Literal regression_uint (IntL 7)))
Proof
  EVAL_TAC
QED

Theorem dynarray_and_map_getter_arguments:
  public_getter
    (VariableDecl (Public F) Storage "g"
      (ArrayT regression_uint (Dynamic 3)) (SOME 0)) =
    SOME (View,F,F,"g",[("0",regression_uint)],[],regression_uint,
      [Return (SOME (Subscript regression_uint
        (TopLevelName (ArrayT regression_uint (Dynamic 3)) (NONE,"g"))
        (Name regression_uint "0")))]) /\
  public_getter
    (HashMapDecl (Public T) F "m" regression_uint (Type regression_uint) (SOME 1)) =
    SOME (View,T,F,"m",[("0",regression_uint)],[],regression_uint,
      [Return (SOME (Subscript regression_uint
        (TopLevelName NoneT (NONE,"m")) (Name regression_uint "0")))])
Proof
  EVAL_TAC
QED

(* Record actual integrated header coverage, rather than the historical issue's
   assumption that transient and nested maps are rejected here. *)
Theorem current_public_map_header_coverage:
  supported_declaration_header []
    (HashMapDecl (Public F) F "g" regression_uint (Type regression_uint) (SOME 0)) /\
  supported_declaration_header []
    (HashMapDecl (Public F) T "g" regression_uint (Type regression_uint) (SOME 0)) /\
  supported_declaration_header []
    (HashMapDecl (Public F) F "g" regression_uint
      (HashMapT regression_uint (Type regression_uint)) (SOME 0)) /\
  ~supported_declaration_header []
    (HashMapDecl (Public F) F "g" regression_uint (Type regression_uint) NONE)
Proof
  EVAL_TAC
QED
