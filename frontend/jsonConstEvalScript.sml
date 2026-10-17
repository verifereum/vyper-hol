Theory jsonConstEval
Ancestors
  jsonConstAST jsonToVyperExpr vyperConstEval vyperValue vyperValueOperation
  alist

(* Elaborate integer expressions with declaration types, before resolving
   array bounds. Constants are substituted from the already evaluated prefix;
   compiler-provided types and folded values are not used. *)
Definition elaborate_integer_def:
  elaborate_integer constants locals ty (JE_Int i _) =
    (case type_to_int_bound ty of
     | SOME bounds => if within_int_bound bounds i
                      then SOME (Literal ty (IntL i)) else NONE
     | NONE => NONE) /\
  elaborate_integer constants locals ty (JE_Name name _ _ _) =
    (case ALOOKUP constants name of
     | SOME i =>
         (case type_to_int_bound ty of
          | SOME bounds => if within_int_bound bounds i
                           then SOME (Literal ty (IntL i)) else NONE
          | NONE => NONE)
     | NONE => if ALOOKUP locals name = SOME ty
               then SOME (Name ty name) else NONE) /\
  elaborate_integer constants locals ty (JE_Folded original _) =
    elaborate_integer constants locals ty original /\
  elaborate_integer constants locals ty (JE_BinOp left bop right _) =
    (case (elaborate_integer constants locals ty left,
           elaborate_integer constants locals ty right) of
     | (SOME l, SOME r) => SOME (Builtin ty (Bop (translate_binop bop)) [l; r])
     | _ => NONE) /\
  elaborate_integer constants locals ty _ = NONE
Termination
  WF_REL_TAC `measure (\(_,_,_,e). json_expr_size e)` >> simp[]
End

Definition evaluate_constant_def:
  evaluate_constant constants ty source =
    case elaborate_integer constants [] ty source of
    | SOME e => OPTION_MAP (\i. (e,i)) (eval_integer_constant e)
    | NONE => NONE
End

Theorem evaluate_constant_sound:
  evaluate_constant constants ty source = SOME (e,i) ==>
  eval_expr cx e st = (INL (Value (IntV i)), st)
Proof
  rw[evaluate_constant_def, AllCaseEqs()] >>
  irule eval_integer_constant_sound >> simp[]
QED

Theorem evaluate_constant_literal_equivalent:
  evaluate_constant constants ty source = SOME (e,i) ==>
  eval_expr cx e st = eval_expr cx (Literal ty (IntL i)) st
Proof
  strip_tac >> drule evaluate_constant_sound >>
  simp[vyperInterpreterTheory.evaluate_def, evaluate_literal_def,
       vyperStateTheory.return_def]
QED

Definition resolve_constant_annotation_def:
  resolve_constant_annotation constants (CA_Integer bits signed) =
    (if (if signed then 1 < bits else 0 < bits) /\ bits <= 256
     then SOME (BaseT (if signed then IntT bits else UintT bits)) else NONE) /\
  resolve_constant_annotation constants (CA_Array element bound) =
    (case (resolve_constant_annotation constants element,
           evaluate_constant constants (BaseT (UintT 256)) bound) of
     | (SOME ty, SOME (_,i)) =>
         if 0 < i then SOME (ArrayT ty (Fixed (Num i))) else NONE
     | _ => NONE)
End

Theorem resolved_array_bound_sound:
  resolve_constant_annotation constants (CA_Array element bound) = SOME ty ==>
  ?elem e i.
    ty = ArrayT elem (Fixed (Num i)) /\ 0 < i /\
    elaborate_integer constants [] (BaseT (UintT 256)) bound = SOME e /\
    eval_expr cx e st = (INL (Value (IntV i)), st)
Proof
  rw[resolve_constant_annotation_def, evaluate_constant_def, AllCaseEqs()] >>
  drule eval_integer_constant_sound >> metis_tac[]
QED

Definition resolve_constant_args_def:
  resolve_constant_args constants [] = SOME [] /\
  resolve_constant_args constants ((name,ann)::args) =
    (case (resolve_constant_annotation constants ann,
           resolve_constant_args constants args) of
     | (SOME ty, SOME rest) => SOME ((name,ty)::rest)
     | _ => NONE)
End

(* Constants precede their uses; missing names and forward references fail.
   The original elaborated initializer remains in the runtime declaration. *)
Definition translate_constant_declarations_def:
  translate_constant_declarations constants [] = SOME [] /\
  translate_constant_declarations constants
      (CD_Constant name ann source :: rest) =
    (if IS_SOME (ALOOKUP constants name) then NONE else
     case resolve_constant_annotation constants ann of
     | NONE => NONE
     | SOME ty =>
       case evaluate_constant constants ty source of
       | NONE => NONE
       | SOME (e,i) => OPTION_MAP
           (CONS (VariableDecl Private (Constant e) name ty NONE))
           (translate_constant_declarations ((name,i)::constants) rest)) /\
  translate_constant_declarations constants
      (CD_Function name args result source :: rest) =
    (case (resolve_constant_args constants args,
           resolve_constant_annotation constants result) of
     | (SOME params, SOME ty) =>
       if EXISTS (\(name,_). IS_SOME (ALOOKUP constants name)) params \/
          ~ALL_DISTINCT (MAP FST params) then NONE else
       case elaborate_integer constants params ty source of
       | NONE => NONE
       | SOME e => OPTION_MAP
           (CONS (FunctionDecl External Pure F F name params [] ty
             [Return (SOME e)]))
           (translate_constant_declarations constants rest)
     | _ => NONE)
End

(* This entry point never invokes the legacy folded-value translator. *)
Definition translate_constant_module_def:
  translate_constant_module decls =
    if ALL_DISTINCT (MAP (\d. case d of CD_Constant name _ _ => name
                                       | CD_Function name _ _ _ => name) decls)
    then OPTION_MAP (\tops. [(NONE : num option,tops)])
           (translate_constant_declarations [] decls)
    else NONE
End
