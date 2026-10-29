(* Original source rules for location-sensitive expressions. There are no
   emitted expressions, elaborators, or runtime evaluators in these rules. *)
Theory sourceMeaningLocationSource
Ancestors
  sourceMeaningLocationDefs sourceMeaningDefs sourceMeaningConst sourceSyntax
  sourceResolve sourceExprDefs sourceConstValue sourceConstBuiltin
  sourceTypeDefs vyperAST alist list words

Theorem source_location_stage_unique:
  source_meaning_stage scopes table constants original result ==>
  !other. source_meaning_stage scopes table constants original other <=> other = result
Proof
  simp[source_meaning_stage_def] >> strip_tac >> gvs[] >> simp[EQ_SYM_EQ]
QED

Definition source_location_flag_def:
  source_location_flag scopes table constants kws key default b <=>
    (ALOOKUP kws key = NONE /\ b = default) \/
    ?original. ALOOKUP kws key = SOME original /\
      source_meaning_stage scopes table constants original (SC_Value (SCV_Bool b))
End

Definition source_location_selector_def:
  source_location_selector scopes table constants kws mid <=>
    (ALOOKUP kws "method_id" = NONE /\ mid = NONE) \/
    (?original bs. ALOOKUP kws "method_id" = SOME original /\
      source_meaning_stage scopes table constants original (SC_Value (SCV_Bytes bs)) /\
      LENGTH bs = 4 /\ mid = SOME (MAP n2w bs)) \/
    (?original s. ALOOKUP kws "method_id" = SOME original /\
      source_meaning_stage scopes table constants original (SC_Value (SCV_Hex s)) /\
      LENGTH s = 10 /\ mid = SOME (MAP n2w (source_const_hex_decode (DROP 2 s))))
End

Definition source_location_intrinsic_def:
  source_location_intrinsic scopes table callee name <=>
    ?names. source_expr_path callee = SOME names /\
      source_resolve_name scopes table names = SOME (["$builtin";name],SR_Function)
End

Definition source_location_type_operand_def:
  source_location_type_operand scopes table constants type_ids (SX_Name name) ty =
    (?path kind. source_resolve_name scopes table [name] = SOME (path,kind) /\
      (kind = SR_Type \/ ?n. kind = SR_FixedBytes n) /\ ALOOKUP type_ids path = SOME ty) /\
  source_location_type_operand scopes table constants type_ids (SX_Tuple children) ty =
    (case ty of TupleT ts => children <> [] /\
      LIST_REL (source_location_type_operand scopes table constants type_ids) children ts
     | _ => F) /\
  source_location_type_operand scopes table constants type_ids (SX_Subscript base index) ty =
    (case ty of ArrayT et (Fixed n) => 0 < n /\
       source_location_type_operand scopes table constants type_ids base et /\
       source_meaning_stage scopes table constants index (SC_Value (SCV_Int (&n)))
     | _ => F) /\
  source_location_type_operand scopes table constants type_ids _ ty = F
Termination
  WF_REL_TAC `measure (\(scopes,table,constants,type_ids,e,ty). source_expr_size e)` >>
  simp[] >> rpt strip_tac >> res_tac >> simp[]
End

Definition source_location_boolean_def:
  source_location_boolean op [] = SML_Core (SM_Literal (BaseT BoolT) (BoolL (op = SCB_And))) /\
  source_location_boolean op (m::ms) = if ms = [] then m else
    SML_If (BaseT BoolT) m
      (if op = SCB_And then source_location_boolean op ms
       else SML_Core (SM_Literal (BaseT BoolT) (BoolL T)))
      (if op = SCB_And then SML_Core (SM_Literal (BaseT BoolT) (BoolL F))
       else source_location_boolean op ms)
End

(* refs and type_ids are source declaration metadata, not AST bindings.
   The code bridge independently checks their actual runtime representation. *)
Inductive source_location_source:
[staged:]
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_meaning_source [] scopes table constants ty original core ==>
  source_location_source refs type_ids scopes table constants ty original (SML_Core core)
[reference:]
  source_expr_path original = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Dynamic) /\
  ALOOKUP refs path = SOME (ty,reference) ==>
  source_location_source refs type_ids scopes table constants ty original (SML_Reference ty reference)
[sender:]
  source_expr_path original = SOME names /\
  source_resolve_name scopes table names = SOME (["$builtin";"msg";"sender"],SR_Dynamic) ==>
  source_location_source refs type_ids scopes table constants (BaseT AddressT) original
    (SML_Apply (BaseT AddressT) (Env Sender) [])
[unary:]
  source_meaning_stage scopes table constants (SX_Unary uop child) SC_NotConstant /\
  source_expr_unary_domain uop ty /\
  source_location_source refs type_ids scopes table constants ty child m ==>
  source_location_source refs type_ids scopes table constants ty (SX_Unary uop child)
    (SML_Apply ty (source_expr_unary uop) [m])
[binary:]
  source_meaning_stage scopes table constants (SX_Binary op left right) SC_NotConstant /\
  op <> SCB_LShift /\ op <> SCB_RShift /\ source_expr_binary_domain op ty /\
  source_location_source refs type_ids scopes table constants ty left l /\
  source_location_source refs type_ids scopes table constants ty right r ==>
  source_location_source refs type_ids scopes table constants ty (SX_Binary op left right)
    (SML_Apply ty (Bop (source_expr_binary op)) [l;r])
[compare:]
  source_meaning_stage scopes table constants (SX_Compare cop left right) SC_NotConstant /\
  source_expr_compare cop = SOME cmp /\
  source_location_source refs type_ids scopes table constants et left l /\
  source_location_source refs type_ids scopes table constants et right r ==>
  source_location_source refs type_ids scopes table constants (BaseT BoolT) (SX_Compare cop left right)
    (SML_Apply (BaseT BoolT) (Bop cmp) [l;r])
[conditional:]
  source_location_source refs type_ids scopes table constants (BaseT BoolT) condition c /\
  source_location_source refs type_ids scopes table constants ty left l /\
  source_location_source refs type_ids scopes table constants ty right r ==>
  source_location_source refs type_ids scopes table constants ty (SX_IfExp condition left right)
    (SML_If ty c l r)
[boolean:]
  source_meaning_stage scopes table constants (SX_Boolean boolop children) SC_NotConstant /\
  2 <= LENGTH children /\
  LIST_REL (source_location_source refs type_ids scopes table constants (BaseT BoolT)) children ms ==>
  source_location_source refs type_ids scopes table constants (BaseT BoolT) (SX_Boolean boolop children)
    (source_location_boolean boolop ms)
[tuple:]
  LIST_REL (\original m. source_location_source refs type_ids scopes table constants
    (source_location_type m) original m) children ms /\ children <> [] ==>
  source_location_source refs type_ids scopes table constants (TupleT (MAP source_location_type ms))
    (SX_Tuple children) (SML_Apply (TupleT (MAP source_location_type ms))
      (MakeArray NONE (Fixed (LENGTH ms))) ms)
[array:]
  LIST_REL (source_location_source refs type_ids scopes table constants et) children ms ==>
  source_location_source refs type_ids scopes table constants (ArrayT et bd) (SX_List children)
    (SML_Apply (ArrayT et bd) (MakeArray (SOME et) bd) ms)
[array_subscript:]
  source_location_source refs type_ids scopes table constants (ArrayT et bd) receiver a /\
  source_location_source refs type_ids scopes table constants (BaseT (UintT 256)) index i ==>
  source_location_source refs type_ids scopes table constants et (SX_Subscript receiver index)
    (SML_Subscript et a i)
[tuple_subscript:]
  source_location_source refs type_ids scopes table constants (TupleT ts) receiver a /\
  source_meaning_stage scopes table constants index (SC_Value (SCV_Int (&n))) /\ n < LENGTH ts ==>
  source_location_source refs type_ids scopes table constants (EL n ts) (SX_Subscript receiver index)
    (SML_Subscript (EL n ts) a (SML_Core (SM_Literal (BaseT (UintT 256)) (IntL (&n)))))
[builtin:]
  source_expr_builtin_identity scopes table callee = SOME b /\ b <> SCB_MethodId /\
  source_expr_builtin b = SOME bt /\ bt <> Len /\
  source_meaning_stage scopes table constants (SX_Call callee args []) SC_NotConstant /\
  LIST_REL (\original m. source_location_source refs type_ids scopes table constants
    (source_location_type m) original m) args ms ==>
  source_location_source refs type_ids scopes table constants ty (SX_Call callee args [])
    (SML_Apply ty bt ms)
[length:]
  source_expr_builtin_identity scopes table callee = SOME SCB_Len /\
  source_location_source refs type_ids scopes table constants et arg m ==>
  source_location_source refs type_ids scopes table constants (BaseT (UintT 256)) (SX_Call callee [arg] [])
    (SML_Length (BaseT (UintT 256)) m)
[encode:]
  source_location_intrinsic scopes table callee "abi_encode" /\
  ALL_DISTINCT (MAP FST kws) /\ EVERY (\k. k = "ensure_tuple" \/ k = "method_id") (MAP FST kws) /\
  source_location_flag scopes table constants kws "ensure_tuple" T ensure /\
  source_location_selector scopes table constants kws mid /\
  LIST_REL (\original m. source_location_source refs type_ids scopes table constants
    (source_location_type m) original m) args ms ==>
  source_location_source refs type_ids scopes table constants ty (SX_Call callee args kws)
    (SML_TypeApply ty (AbiEncode ensure mid) (TupleT (MAP source_location_type ms)) ms)
[decode:]
  source_location_intrinsic scopes table callee "abi_decode" /\
  ALL_DISTINCT (MAP FST kws) /\ EVERY ($= "unwrap_tuple") (MAP FST kws) /\
  source_location_flag scopes table constants kws "unwrap_tuple" T unwrap /\
  source_location_type_operand scopes table constants type_ids target ty /\
  source_location_source refs type_ids scopes table constants et data m ==>
  source_location_source refs type_ids scopes table constants ty (SX_Call callee [data;target] kws)
    (SML_TypeApply ty (AbiDecode unwrap) ty [m])
[raw_call:]
  source_location_intrinsic scopes table callee "raw_call" /\
  ALL_DISTINCT (MAP FST kws) /\
  EVERY (\k. MEM k ["value";"max_outsize";"is_delegate_call";"is_static_call";"revert_on_failure"]) (MAP FST kws) /\
  source_location_flag scopes table constants kws "is_delegate_call" F flags.rcf_is_delegate /\
  source_location_flag scopes table constants kws "is_static_call" F flags.rcf_is_static /\
  source_location_flag scopes table constants kws "revert_on_failure" T flags.rcf_revert_on_failure /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((ALOOKUP kws "max_outsize" = NONE /\ flags.rcf_max_outsize = 0) \/
    ?out. ALOOKUP kws "max_outsize" = SOME out /\
      source_meaning_stage scopes table constants out (SC_Value (SCV_Int (&flags.rcf_max_outsize)))) /\
  source_location_source refs type_ids scopes table constants (BaseT AddressT) target tm /\
  source_location_source refs type_ids scopes table constants et data dm /\
  ((ALOOKUP kws "value" = NONE /\ vm = SML_Core (SM_Literal (BaseT (UintT 256)) (IntL 0))) \/
    ?value. ALOOKUP kws "value" = SOME value /\
      source_location_source refs type_ids scopes table constants (BaseT (UintT 256)) value vm) ==>
  source_location_source refs type_ids scopes table constants ty (SX_Call callee [target;data] kws)
    (SML_RawCall ty flags tm dm vm)
[revert:]
  source_location_intrinsic scopes table callee "raw_revert" /\

  source_location_source refs type_ids scopes table constants et data m ==>
  source_location_source refs type_ids scopes table constants ty (SX_Call callee [data] [])
    (SML_Revert ty m)
End
