(* Ordinary unary expression simulation composition. *)
Theory exprSimUnop
Ancestors
  exprUnopStraight exprUnopSimDefs exprSimUnopCompose
  exprSimUnopProps
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps arithmeticProps vyperArith
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem
Libs
  intLib pairLib




Theorem compile_not_frag:
  !ctx func cenv cx ann tys v1 es0 tv1.
    (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
     is_flag_type ann) /\
    evaluate_type (get_tenv cx) ann = SOME tv1 /\ value_has_type tv1 v1 /\
    (!nsid m. ann = FlagT nsid /\ tv1 = FlagTV m ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    unop_frag ctx func cenv cx
      (\x. if ann = BaseT BoolT then emit_op ISZERO [x]
           else compile_invert x ann cenv)
      (typed_val_to_w256 tv1 v1) ann (unop_result cx ann Not tys v1 es0) es0
Proof
  cheat
QED

Theorem compile_abs_frag:
  !ctx func cenv cx tys v1 es0.
    value_has_type (BaseTV (IntT 256)) v1 ==>
    unop_frag ctx func cenv cx compile_builtin_abs
      (typed_val_to_w256 (BaseTV (IntT 256)) v1) (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Abs tys v1 es0) es0
Proof
  cheat
QED


Theorem compile_neg_frag:
  !ctx func cenv cx t tv v es.
    is_numeric_type t /\ ~is_uint_type t /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v ==>
    unop_frag ctx func cenv cx (\x. compile_neg x t)
      (typed_val_to_w256 tv v) t (unop_result cx t Neg [t] v es) es
Proof
  cheat
QED
