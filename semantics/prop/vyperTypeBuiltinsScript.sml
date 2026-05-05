(*
 * Builtin, type-builtin, binop, account/env, and call-target typing lemmas.
 *)

Theory vyperTypeBuiltins
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
Libs
  wordsLib

(* ===== Environment/account items ===== *)

Theorem Env_builtin_sound:
  context_well_typed cx /\ evaluate_type tenv (env_item_type item) = SOME tv ==>
  ?v. evaluate_builtin cx acc (env_item_type item) (Env item) [] = INL v /\
      value_has_type tv v
Proof
  cheat
QED

Theorem Acc_builtin_sound:
  accounts_well_typed acc /\ evaluate_type tenv (account_item_type item) = SOME tv /\
  value_has_type (BaseTV AddressT) addr_v ==>
  ?v. evaluate_builtin cx acc (account_item_type item) (Acc item) [addr_v] = INL v /\
      value_has_type tv v
Proof
  cheat
QED

(* ===== Binary operations ===== *)

Theorem well_typed_binop_sound:
  well_typed_binop ty bop t1 t2 /\
  evaluate_type tenv ty = SOME result_tv /\
  evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 /\
  u = (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) ==>
  ?v. evaluate_binop u result_tv bop v1 v2 = INL v /\ value_has_type result_tv v
Proof
  cheat
QED

(* ===== Builtins ===== *)

Theorem well_typed_builtin_app_length:
  well_typed_builtin_app ty blt ts ==> builtin_args_length_ok blt (LENGTH ts)
Proof
  cheat
QED

Theorem well_typed_builtin_app_sound:
  well_typed_builtin_app ty blt ts /\
  MAP (evaluate_type tenv) ts = MAP SOME tvs /\
  evaluate_type tenv ty = SOME tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx /\ accounts_well_typed acc ==>
  ?v. evaluate_builtin cx acc ty blt vs = INL v /\ value_has_type tv v
Proof
  cheat
QED

Theorem Len_builtin_sound:
  well_typed_builtin_app ty Len [arg_ty] /\
  evaluate_type tenv ty = SOME tv /\ toplevel_value_typed arg_tv arg_runtime_tv /\
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  value_has_type tv (IntV (&n))
Proof
  cheat
QED

(* ===== Type builtins ===== *)

Theorem well_typed_type_builtin_args_length:
  well_typed_type_builtin_args tb target_ty ts ==> type_builtin_args_length_ok tb (LENGTH ts)
Proof
  cheat
QED

Theorem valid_conversion_sound:
  valid_conversion from_ty to_ty /\
  evaluate_type tenv from_ty = SOME from_tv /\ evaluate_type tenv to_ty = SOME to_tv /\
  value_has_type from_tv v ==>
  ?v'. evaluate_type_builtin cx Convert to_ty [v] = INL v' /\ value_has_type to_tv v'
Proof
  cheat
QED

Theorem well_typed_type_builtin_sound:
  well_typed_type_builtin_args tb target_ty ts /\
  MAP (evaluate_type tenv) ts = MAP SOME tvs /\
  evaluate_type tenv result_ty = SOME result_tv /\
  LIST_REL value_has_type tvs vs /\ context_well_typed cx ==>
  ?v. evaluate_type_builtin cx tb target_ty vs = INL v /\ value_has_type result_tv v
Proof
  cheat
QED

(* ===== Calls / special targets ===== *)

Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
Proof
  cheat
QED

Theorem internal_call_signature_sound:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src,fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    sig.param_types = MAP SND params /\ sig.num_defaults = LENGTH dflts
Proof
  rw[fn_sigs_consistent_def]
QED

Theorem ext_call_args_typed:
  well_typed_expr env (Call ty (ExtCall stat fsig) args drv) ==>
  well_typed_exprs env args /\ well_typed_opt env drv
Proof
  Cases_on `fsig` >> Cases_on `r` >> rw[well_typed_expr_def]
QED

