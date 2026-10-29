(* Independent location-sensitive source computations. In particular ABI
   arguments are locations until the separate staging phase, not snapshots. *)
Theory sourceMeaningLocationDefs
Ancestors
  sourceMeaningRuntime sourceMeaningDefs sourceMeaningValue sourceExprDefs
  vyperInterpreter vyperAbiOperand vyperState vyperAST vyperValue
  vyperValueOperation vyperContext list

Datatype:
  source_reference = SMR_Local string | SMR_Global nsid
End

Definition source_reference_read_def:
  source_reference_read cx (SMR_Local id) = source_meaning_local id /\
  source_reference_read cx (SMR_Global (src,id)) = lookup_global cx src id
End

Definition source_reference_abi_def:
  source_reference_abi cx (SMR_Local id) = lookup_abi_local cx id /\
  source_reference_abi cx (SMR_Global (src,id)) = lookup_abi_global cx src id
End

Definition source_reference_target_def:
  source_reference_target cx (SMR_Local id) = do
    sc <- get_scopes;
    type_check (IS_SOME (lookup_scopes id sc)) "NameTarget not in scope";
    return (ScopedVar id,[])
  od /\
  source_reference_target cx (SMR_Global (src,id)) = do
    ts <- lift_option_type (get_module_code cx src) "TopLevelNameTarget get_module_code";
    if is_immutable_decl id ts then return (ImmutableVar src id,[])
    else return (TopLevelVar src id,[])
  od
End

Datatype:
  source_location_meaning = SML_Core source_meaning
    | SML_Reference type source_reference
    | SML_Apply type builtin (source_location_meaning list)
    | SML_Length type source_location_meaning
    | SML_If type source_location_meaning source_location_meaning source_location_meaning
    | SML_Subscript type source_location_meaning source_location_meaning
    | SML_TypeApply type type_builtin type (source_location_meaning list)
    | SML_Revert type source_location_meaning
    | SML_RawCall type raw_call_flags source_location_meaning source_location_meaning source_location_meaning
End

Definition source_location_type_def:
  source_location_type (SML_Core m) = source_meaning_type m /\
  source_location_type (SML_Reference ty r) = ty /\
  source_location_type (SML_Apply ty b ms) = ty /\
  source_location_type (SML_Length ty m) = ty /\
  source_location_type (SML_If ty c l r) = ty /\
  source_location_type (SML_Subscript ty a i) = ty /\
  source_location_type (SML_TypeApply ty b t ms) = ty /\
  source_location_type (SML_Revert ty m) = ty /\
  source_location_type (SML_RawCall ty flags t d v) = ty
End

(* All four computations recurse on semantic terms, never runtime expressions.
   Metadata for local/global locations comes from the actual runtime cell. *)
Definition source_location_eval_def:
  source_location_eval cx (SML_Core m) =
    source_meaning_eval cx (\p. source_meaning_local (LAST p)) m /\
  source_location_eval cx (SML_Reference ty r) = source_reference_read cx r /\
  source_location_eval cx (SML_Apply ty b ms) = do
    type_check (builtin_args_length_ok b (LENGTH ms)) "Builtin args";
    v <- (do
      vs <- source_location_evals cx ms;
      acc <- get_accounts;
      lift_sum (evaluate_builtin cx acc ty b (MAP source_location_type ms) vs)
    od);
    return (Value v)
  od /\
  source_location_eval cx (SML_Length ty m) = do
    type_check (builtin_args_length_ok Len 1) "Builtin args";
    v <- (do
      tv <- source_location_eval cx m;
      len <- toplevel_array_length cx tv;
      return (IntV (&len))
    od);
    return (Value v)
  od /\
  source_location_eval cx (SML_If ty c l r) = do
    tv <- source_location_eval cx c;
    switch_BoolV tv (source_location_eval cx l) (source_location_eval cx r)
  od /\
  source_location_eval cx (SML_Subscript ty a i) = do
    tv <- source_location_eval cx a;
    iv <- source_location_eval cx i;
    v <- get_Value iv;
    at <- lift_option_type (evaluate_type (get_tenv cx) (source_location_type a)) "Subscript array type";
    check_array_bounds cx tv v;
    res <- lift_sum (evaluate_subscript (get_tenv cx) at tv v);
    case res of INL v => return v | INR (tr,slot,t) => do
      v <- read_storage_slot cx tr slot t;
      return (Value v)
    od
  od /\
  source_location_eval cx (SML_TypeApply ty b t ms) = do
    type_check (type_builtin_args_length_ok b (LENGTH ms)) "TypeBuiltin args";
    vs <- (case b of AbiEncode _ _ => do
      mark <- mark_abi_captures;
      finally (do args <- source_location_abis cx ms;
        stage_abi_operands cx args od) (release_abi_captures mark)
      od | _ => source_location_evals cx ms);
    v <- lift_sum (evaluate_type_builtin cx b t (MAP source_location_type ms) vs);
    return (Value v)
  od /\
  source_location_eval cx (SML_Revert ty m) = do
    vs <- source_meaning_args cx [source_location_eval cx m];
    type_check (LENGTH vs = 1) "raw_revert args";
    raise (Error (RuntimeError "raw_revert"))
  od /\
  source_location_eval cx (SML_RawCall ty flags t d v) = do
    vs <- source_meaning_args cx [source_location_eval cx t;source_location_eval cx d;
      source_location_eval cx v];
    type_check (LENGTH vs = 3) "raw_call args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
    eval_raw_call cx flags target data amount
  od /\
  source_location_evals cx [] = return [] /\
  source_location_evals cx (m::ms) = do
    tv <- source_location_eval cx m;
    v <- materialise cx tv;
    vs <- source_location_evals cx ms;
    return (v::vs)
  od /\
  source_location_abi cx (SML_Reference ty r) = source_reference_abi cx r /\
  source_location_abi cx (SML_If ty c l r) = do
    tv <- source_location_eval cx c;
    arg <- switch_BoolV tv (source_location_abi cx l) (source_location_abi cx r);
    unwrap_abi_operand cx arg
  od /\
  source_location_abi cx (SML_Subscript ty a i) = do
    arg <- source_location_abi cx a;
    iv <- source_location_eval cx i;
    v <- get_Value iv;
    at <- lift_option_type (evaluate_type (get_tenv cx) (source_location_type a)) "Subscript array type";
    subscript_abi_operand cx at arg v
  od /\
  source_location_abi cx m = do
    tv <- source_location_eval cx m;
    v <- materialise cx tv;
    return (AbiSnapshot v)
  od /\
  source_location_abis cx [] = return [] /\
  source_location_abis cx (m::ms) = do
    arg <- source_location_abi cx m;
    arg <- unwrap_abi_operand cx arg;
    args <- source_location_abis cx ms;
    return (arg::args)
  od
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (cx,m) => 2 * source_location_meaning_size m
    | INR (INL (cx,ms)) => 2 * list_size source_location_meaning_size ms
    | INR (INR (INL (cx,m))) => 2 * source_location_meaning_size m + 1
    | INR (INR (INR (cx,ms))) => 2 * list_size source_location_meaning_size ms + 1)` >>
  simp[]
End
