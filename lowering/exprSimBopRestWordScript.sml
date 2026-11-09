(*
 * Expression simulation: the binary operators left over by
 * exprSimOperators' word and address/bytesN cases (compile_bop_rest_case),
 * but for those held for #742 (exprSimBopHeld): in and not in on an array
 * whose elements are words, and any ill-typed rest.
 *
 * TOP-LEVEL:
 *   compile_bop_rest_word_case — that case
 *)

Theory exprSimBopRestWord
Ancestors
  exprSimBopRestWordLoads exprSimBopRestWordCompose exprSimBopRestWordFacts
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

(* Why it holds.
   - Typing (expr_body_pre_bop, well_typed_binop) leaves one case: In or
     NotIn with expr_type e2 = ArrayT (expr_type e1) bd and
     is_word_type (expr_type e1), e2 not an array literal.  Every other
     operator takes operands of word_value_type, and == / != take a
     comparable type (BaseT _ or FlagT _), all covered by word_value_type,
     bytestrings, address or bytesN.  A bytesN wider than 32 does not
     evaluate (expr_body_pre_type_evaluates).
   - The lowering (compile_builtin_dispatch_body) takes the needle with
     lower_value of e1 (a word, expr_val_rel: typed_val_to_w256), then the
     array with compile_expr of e2 (a value_vv, vv_post / vv_holds:
     memory, storage, transient or immutable, or a StackValue pointer
     into memory), and runs compile_var_array_membership: for a dynamic
     array it loads the length, ASSERTs it is at most the capacity, and
     the loop of compile_array_membership_loop compares each element
     word, loaded with compile_ptr_load, with EQ against the needle.
   - The source evaluates e1, e2 (eval_exprs reads both) and
     evaluate_binop In -> evaluate_in_array.  e2's read value has its
     type (expr_body_pre_runtime_typed): a static array's keys are
     sorted and below n, so LENGTH al < n exactly when some index is
     absent, and there memory holds default_value (val_in_memory), whose
     word is 0; storage word slots are canonical (slots_in_range, part of
     storage_holds) and a word type has no dead bytes, so SLOAD gives the
     element's typed word.  typed_val_to_w256 is injective on values of
     one word type, so EQ on the words is equality on the values.
   - The loop writes no memory and only fresh variables; DLOAD/ILOAD read
     immutables without writing memory.
   - Composition of the operands is as in exprSimOperators'
     compile_bop_bytes_eq_case (compile_bop_typed_sim), but the second
     operand goes through expr_vv_sim as in exprSimLen's
     compile_len_vv_case.  A counted Venom loop is done in
     storageCopyGasPath. *)
Theorem compile_bop_rest_word_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) ==>
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac [expr_sim_case_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  drule_all rest_word_typed_membership >> strip_tac >>
  irule compile_rest_word_membership_sim >> metis_tac[]
QED
