(*
 * The right-hand side of an Assign or AnnAssign to a memory-backed local
 * (#637): the facts about e that stmtSimAssignMem's and stmtSimDeclMem's
 * statement lemmas take, derived from e's typing and the allocation
 * check.
 *
 * TOP-LEVEL:
 *   lowered_value_type_memory_bound — the size of the type e is lowered
 *                     at, below e's own
 *   memory_rhs_destination_bound, memory_rhs_read_destination_footprint —
 *                     e's value fits the local's buffer
 *   memory_rhs_read_destination_typed,
 *   memory_rhs_read_local_type — e's value (read through read_result) has
 *                     the local's type
 *   memory_rhs_runtime_layout, memory_rhs_lowered_runtime_layout — the
 *                     types evaluate, at the sizes type_memory_bytes gives
 *   memory_rhs_empty_read_total, memory_rhs_empty_read_destination,
 *   memory_rhs_empty_eval_destination — an empty value reads as the
 *                     local type's default
 *)

Theory memoryLocalRhsProps
Ancestors
  exprSimProps
  exprSimHypsDefs
  compileEnv exprLowering stmtLowering vyperTypeSystem exprSimAggregates
  vyperAST vyperInterpreter vyperValue vyperState
  exprSimAggregateSource vyperValueOperation abiCallerAbiBound supportedTypes
  supportedExprs supportedExprForms vyperABI exprSimHyps
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeCallGraph
  valueTypingMemoryProps valueCopyBytes compileVyper supportedNames loweringShapeProps supportedProgram supportedDecls
Libs
  monadsyntax

Theorem build_func_return_type_distinct:
  !tops vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_return_type tops name = ret
Proof
  cheat
QED

Theorem supported_internal_function_lookup[local]:
  !tops id mut nr rr args dflts ret body.
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) ==>
    FST id = NONE /\
    lookup_function NONE (SND id) Internal tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    MEM (FunctionDecl Internal mut nr rr (SND id) args dflts ret body) tops
Proof
  cheat
QED

Theorem supported_internal_return_type:
  !tops id mut nr rr args dflts ret body cenv.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) /\
    cenv.ce_func_return_type = build_func_return_type tops ==>
    cenv.ce_func_return_type (nsid_to_string id) = ret
Proof
  cheat
QED

Theorem supported_internal_signature_return:
  !tops id mut nr rr args dflts ret body cenv cx env es sig.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    get_module_code cx NONE = SOME tops /\
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.fn_sigs id = SOME sig ==>
    cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty
Proof
  cheat
QED

Theorem supported_internal_return_admissible:
  !tops id mut nr rr args dflts ret body.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut,nr,rr,args,dflts,ret,body) ==>
    supported_return_type tops ret
Proof
  cheat
QED

Theorem eval_empty_bytes_read:
  !cx ann es.
    (do r <- eval_expr cx (Literal ann (BytesL []));
        read_result cx r od) es = (INL (BytesV []), es)
Proof
  cheat
QED

Theorem eval_empty_dynamic_array_read:
  !cx ann et n tv es.
    evaluate_type (get_tenv cx) et = SOME tv ==>
    (do r <- eval_expr cx (Builtin ann (MakeArray (SOME et) (Dynamic n)) []);
        read_result cx r od) es =
    (INL (default_value (ArrayTV tv (Dynamic n))), es)
Proof
  cheat
QED

Theorem allocation_limit_word_room:
  !sz. sz < 2 ** 64 ==> sz + 64 < dimword (:256)
Proof
  cheat
QED

Theorem arg_type_fits_bytestring_memory_bytes:
  !cenv t u.
    is_bytestring_type t /\ arg_type_fits t u ==>
    type_memory_bytes cenv t <= type_memory_bytes cenv u
Proof
  cheat
QED

Theorem supported_tuple_abi_size_bound:
  !sf tenv t.
    supported_tuple_type t ==>
    abi_size_bound sf t = vyper_abi_size_bound tenv t
Proof
  cheat
QED

Theorem lowered_value_type_memory_bound:
  !cenv e env tops.
    supported_expr tops e /\ well_typed_expr env e /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    type_memory_bytes cenv (lowered_value_type cenv e) <=
    type_memory_bytes cenv (expr_type e)
Proof
  cheat
QED

Theorem arg_type_fits_bytestring_source:
  !t u. is_bytestring_type u /\ arg_type_fits t u ==> is_bytestring_type t
Proof
  cheat
QED

Theorem memory_rhs_destination_bound:
  !cenv e env tops ty tenv.
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to tenv (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <=
      type_memory_bytes cenv ty
Proof
  cheat
QED

Theorem abi_encode_lowered_well_typed:
  !env a mid ty target sf.
    supported_tuple_type (expr_type a) /\ LENGTH mid = 4 /\
    well_typed_expr env (TypeBuiltin ty (AbiEncode F (SOME mid)) target [a]) ==>
    well_typed_expr env
      (TypeBuiltin
        (BaseT (BytesT (Dynamic (abi_size_bound sf (expr_type a) + 4))))
        (AbiEncode F (SOME mid)) target [a])
Proof
  cheat
QED

Theorem frame_signature_return_well_formed[local]:
  !cenv cx env es id sig.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig ==>
    well_formed_type env.type_defs sig.ret_ty
Proof
  cheat
QED

Theorem internal_call_annotation_eval[local]:
  !cx a b id args drv.
    eval_expr cx (Call a (IntCall id) args drv) =
    eval_expr cx (Call b (IntCall id) args drv)
Proof
  cheat
QED

Theorem internal_call_read_signature_typed[local]:
  !cenv cx env es ann id args drv sig v es'.
    expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env sig.ret_ty v
Proof
  cheat
QED

Theorem memory_rhs_read_lowered_typed:
  !cenv e env tops cx es v es'.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (lowered_value_type cenv e) v
Proof
  cheat
QED

Theorem memory_rhs_read_destination_typed:
  !cenv cx env e es v es' ty.
    expr_body_pre cenv cx env e es /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env ty v
Proof
  cheat
QED

Theorem memory_rhs_runtime_layout:
  !cenv cx env es ty v.
    expr_sim_inv cenv cx env es /\ value_runtime_typed env ty v ==>
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         value_has_type tv v /\ type_memory_bytes cenv ty = type_memory_size tv
Proof
  cheat
QED

Theorem eval_empty_type_read:
  !cx ann t tv es.
    evaluate_type (get_tenv cx) t = SOME tv ==>
    (do r <- eval_expr cx (TypeBuiltin ann Empty t []);
        read_result cx r od) es = (INL (default_value tv), es)
Proof
  cheat
QED

Theorem memory_rhs_empty_read_total:
  !cx env e es.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         (do r <- eval_expr cx e; read_result cx r od) es =
         (INL (default_value tv), es)
Proof
  cheat
QED

Theorem memory_rhs_empty_read_destination:
  !cx env e es ty tyv.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word (expr_type e) /\
    type_widens_to env.type_defs (expr_type e) ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv ==>
    (do r <- eval_expr cx e; read_result cx r od) es =
    (INL (default_value tyv), es)
Proof
  cheat
QED

Theorem type_widens_to_has_length_word:
  !t u tenv.
    has_length_word t /\ type_widens_to tenv t u ==> has_length_word u
Proof
  cheat
QED

Theorem memory_rhs_read_destination_footprint:
  !cenv cx env e es tops ty tyv v es1.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  cheat
QED

Theorem padded_bytes_bound_256[local]:
  !n. 32 * ((n + 31) DIV 32) + 32 < 2 ** 64 ==> n < dimword (:256)
Proof
  cheat
QED

Theorem bytestring_memory_bound_evaluates:
  !cenv tenv t.
    is_bytestring_type t /\ type_memory_bytes cenv t < 2 ** 64 ==>
    ?tv. evaluate_type tenv t = SOME tv
Proof
  cheat
QED

Theorem memory_rhs_lowered_runtime_layout:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es /\
    type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64 /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    ?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
          type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv
Proof
  cheat
QED

Theorem type_widens_to_has_length_word_source:
  !tenv t u.
    type_widens_to tenv t u /\ has_length_word u ==> has_length_word t
Proof
  cheat
QED

Theorem eval_empty_value_result:
  !cx e es r es1.
    is_empty_value_expr e /\ eval_expr cx e es = (INL r,es1) ==>
    ?v. r = Value v
Proof
  cheat
QED

Theorem memory_rhs_empty_eval_destination:
  !cx env e es ty tyv r es1.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    eval_expr cx e es = (INL r,es1) ==>
    r = Value (default_value tyv)
Proof
  cheat
QED

Theorem memory_rhs_read_local_type:
  !cenv cx env e es ty id tyv v es1 entry.
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry ==> entry.type = tyv
Proof
  cheat
QED
