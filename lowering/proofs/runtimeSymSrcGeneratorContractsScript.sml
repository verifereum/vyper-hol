(* Named propositions, not new compiler semantics: separating signatures from
   their proofs lets the mutually recursive body proofs use generator facts
   without importing generator implementations or assuming compiler correctness.

   Clause ledger (owner is the last digit of C1.1.3):
   lower_value/with_loc [6]: all value operands in the three open bodies.
   subscript/attribute [6]: Subscript/Attribute in compile_expr_body.
   get_target_ptr [6]: Pop in compile_expr_body; target indices only.
   multi_vvs [6]: compile_call argument staging.
   multi_exprs [6]: Bop array-literal membership.
   make_tuple/array/array_elems [6]: MakeArray (NONE/SOME).
   struct_lit [6]: StructLit fields; abi_encode_args [6]: AbiEncode.
   concat [6]: Concat (currently rejected by supported_builtin_form).
   call/acc [7]: Call and Acc. Call children are precisely args and default.

   supported_builtin_form currently rejects Slice, Keccak256, Sha256, Len,
   Ceil, Floor, Concat and MethodId; supported_type_builtin_form rejects
   Extract32. Bop In/NotIn are rejected by supported_binop. We still expose
   aggregate signatures independently of those whitelist decisions. *)
Theory runtimeSymSrcGeneratorContracts
Ancestors
  runtimeSymSrcInterfaces exprCallBounds list supportedExprForms supportedExprs
  supportedExprTraverse

(* List-domain callback hypotheses are bounded to members, never all ASTs.
   Requested types remain arbitrary because different helpers request different
   types for the same child. Environments remain explicit at each call site. *)
Definition runtime_sym_lower_value_clause_def:
  runtime_sym_lower_value_clause tops <=>
  !cfn ce ty e s op s'.
    runtime_sym_expr_contract tops cfn ce ty e /\ runtime_sym_env ce /\
    (supported_expr tops e \/ supported_place_expr tops e \/
     supported_effect_place_expr tops e) /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce ty e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_lower_value_with_loc_clause_def:
  runtime_sym_lower_value_with_loc_clause tops <=>
  !cfn ce ty e s op loc s'.
    runtime_sym_expr_contract tops cfn ce ty e /\ runtime_sym_env ce /\
    (supported_expr tops e \/ supported_place_expr tops e \/
     supported_effect_place_expr tops e) /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value_with_loc cfn ce ty e s = ((op,loc),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_subscript_clause_def:
  runtime_sym_subscript_clause tops <=>
  !cfn ce rt ty base key s v s'.
    (!t. runtime_sym_expr_contract tops cfn ce t base /\
         runtime_sym_expr_contract tops cfn ce t key) /\
    runtime_sym_env ce /\
    (supported_expr tops (Subscript rt base key) \/
     supported_place_expr tops (Subscript rt base key) \/
     supported_effect_place_expr tops (Subscript rt base key)) /\
    ~supported_expr_exists is_self_code (Subscript rt base key) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_subscript cfn ce rt ty base key s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_attribute_clause_def:
  runtime_sym_attribute_clause tops <=>
  !cfn ce rt ty base field s v s'.
    runtime_sym_expr_contract tops cfn ce ty base /\ runtime_sym_env ce /\
    (supported_expr tops (Attribute rt base field) \/
     supported_place_expr tops (Attribute rt base field) \/
     supported_effect_place_expr tops (Attribute rt base field)) /\
    ~supported_expr_exists is_self_code (Attribute rt base field) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_attribute cfn ce rt ty base field s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_target_ptr_clause_def:
  runtime_sym_target_ptr_clause tops <=>
  !cfn ce target s op loc pt s'.
    (!e ty. supported_target_exists (\x. x = e) target ==>
            runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\
    ~supported_target_exists is_self_code target /\
    (!e. supported_target_exists (\x. x = e) target ==>
         supported_expr tops e \/ supported_place_expr tops e \/
         supported_effect_place_expr tops e) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr cfn ce target s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_multi_vvs_clause_def:
  runtime_sym_multi_vvs_clause tops <=>
  !cfn ce es s vs s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_multi_vvs cfn ce es s = (vs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY runtime_sym_value vs
End

Definition runtime_sym_multi_exprs_clause_def:
  runtime_sym_multi_exprs_clause tops <=>
  !cfn ce es s ops s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_multi_exprs cfn ce es s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops
End

Definition runtime_sym_make_tuple_clause_def:
  runtime_sym_make_tuple_clause tops <=>
  !cfn ce es buf off s op s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\ ~is_label_operand buf /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_make_tuple cfn ce es buf off s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_make_array_clause_def:
  runtime_sym_make_array_clause tops <=>
  !cfn ce es ety stride lw buf s op s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\ ~is_label_operand buf /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_make_array cfn ce es ety stride lw buf s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_make_array_elems_clause_def:
  runtime_sym_make_array_elems_clause tops <=>
  !cfn ce es ety stride lw buf idx s op s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\ ~is_label_operand buf /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_make_array_elems cfn ce es ety stride lw buf idx s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_struct_lit_clause_def:
  runtime_sym_struct_lit_clause tops <=>
  !cfn ce ty fields buf off s op s'.
    (!e t. MEM e (MAP SND fields) ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops o SND) fields /\
    ~supported_fields_exists is_self_code fields /\ ~is_label_operand buf /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_struct_lit cfn ce ty fields buf off s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

Definition runtime_sym_abi_encode_args_clause_def:
  runtime_sym_abi_encode_args_clause tops <=>
  !cfn ce es s ops s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_args cfn ce es s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops
End

Definition runtime_sym_concat_clause_def:
  runtime_sym_concat_clause tops <=>
  !cfn ce es dst infos off s s'.
    (!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e) /\
    runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\
    ~is_label_operand dst /\ ~is_label_operand off /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_concat cfn ce es dst infos off s = ((),s') ==>
    EVERY runtime_sym_inst (state_insts s')
End

Definition runtime_sym_call_clause_def:
  runtime_sym_call_clause tops <=>
  !cfn ce rt ty target es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt target es default) /\
    ~supported_expr_exists is_self_code (Call rt target es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) target es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_acc_clause_def:
  runtime_sym_acc_clause tops <=>
  !cfn ce e item s op s'.
    runtime_sym_expr_contract tops cfn ce (BaseT AddressT) e /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_acc cfn ce e item s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
End

(* Reachable direct-body primitive ledger:
   context [2]: unwrap_value (ECAdd/ECMul/ABI), compile_ifexp_arm (IfExp),
     compile_alloc_buffer (StructLit/MakeArray/ABI), widen_copy (Convert).
   expr primitives [3]: literal_vv (Literal), env_var (Env), binop (Bop),
     invert (Not), neg (Neg), type_convert (Convert), dynarray_pop (Pop),
     addmod_names/mulmod_names/powmod256_names (expression fast paths).
   math [3]: addmod/mulmod/pow_mod256 (matching builtins).
   byte/simple [4]: abs, calldatasize, slice_calldata, uint2str,
     empty_complex, blockhash/blobhash, ecrecover/ecadd_points/ecmul_point,
     as_wei_value_int/decimal (matching builtins).
   ABI [5]: lower_abi_encode/decode, compile_store_abi_tuple (ABI builtins).
   Existing exports (not duplicated in this bundle): compile_name_vv [shared],
     fresh_var/fresh_label, emit_inst/emit_op/emit_void, new_block [1].
   compile_expr and both dispatchers are recursive interfaces, NOT generators.
   TopLevelName/FlagMember and literal constructors have no stateful call.
   bytestring_hash is unreachable: supported_binop accepts Eq/NotEq only at
   supported_word_type, whereas is_bytestring_type accepts dynamic bytes/string.
   Definitions below group only finite nonrecursive signatures; each conjunct
   is a universally quantified proposition about one concrete generator. *)
Definition runtime_sym_context_clauses_def:
  runtime_sym_context_clauses <=>
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
     EVERY runtime_sym_inst (state_insts s) /\
     unwrap_value ce v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce rt at v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_ifexp_arm ce rt at v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (b,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!n v m s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_bytestring_widen_copy n v m s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op)
End

Definition runtime_sym_expr_primitive_clauses_def:
  runtime_sym_expr_primitive_clauses <=>
  (!ty lit s v s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_literal_vv ty lit s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!item s op s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_env_var item s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!bop x y ty bl el s op s'. ~is_label_operand x /\ ~is_label_operand y /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_binop bop x y ty bl el s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce v ty s op s'. runtime_sym_env ce /\ ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_invert v ty ce s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v ty s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\ compile_neg v ty s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v cv s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_type_convert v cv s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!base ws size ctor imm loc s op s'. ~is_label_operand base /\
     (!v. imm = SOME v ==> ~is_label_operand v) /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_dynarray_pop base ws size ctor imm loc s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op)
End

Definition runtime_sym_name_fastpath_clauses_def:
  runtime_sym_name_fastpath_clauses <=>
  (!ce rt aty a bty b mty m s v s'. runtime_sym_env ce /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_addmod_names ce rt aty a bty b mty m s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!ce rt aty a bty b mty m s v s'. runtime_sym_env ce /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_mulmod_names ce rt aty a bty b mty m s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!ce rt aty a bty b s v s'. runtime_sym_env ce /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_powmod256_names ce rt aty a bty b s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v)
End

Definition runtime_sym_math_clauses_def:
  runtime_sym_math_clauses <=>
  (!a b m s op s'. EVERY (\x. ~is_label_operand x) [a;b;m] /\
     EVERY runtime_sym_inst (state_insts s) /\ compile_addmod a b m s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!a b m s op s'. EVERY (\x. ~is_label_operand x) [a;b;m] /\
     EVERY runtime_sym_inst (state_insts s) /\ compile_mulmod a b m s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!a b s op s'. ~is_label_operand a /\ ~is_label_operand b /\
     EVERY runtime_sym_inst (state_insts s) /\ compile_pow_mod256 a b s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op)
End

Definition runtime_sym_simple_clauses_def:
  runtime_sym_simple_clauses <=>
  (!v s op s'. ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_builtin_abs v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s op s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_builtin_calldatasize s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!start len n s op s'. ~is_label_operand start /\ ~is_label_operand len /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_slice_calldata start len n s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v digits size s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_uint2str v digits size s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!size lw s buf s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_builtin_empty_complex size lw s = (buf,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand buf.buf_operand)
End

Definition runtime_sym_misc_clauses_def:
  runtime_sym_misc_clauses <=>
  (!v s op s'. ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_blockhash v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v s op s'. ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_blobhash v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!h v r x s op s'. EVERY (\a. ~is_label_operand a) [h;v;r;x] /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_ecrecover h v r x s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!p q s op s'. ~is_label_operand p /\ ~is_label_operand q /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_ecadd_points p q s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!p q s op s'. ~is_label_operand p /\ ~is_label_operand q /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_ecmul_point p q s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v scale signed s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_as_wei_value_int v scale signed s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v scale divisor s op s'. ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_as_wei_value_decimal v scale divisor s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op)
End

Definition runtime_sym_abi_clauses_def:
  runtime_sym_abi_clauses <=>
  (!ensure mid src info n s op s'. ~is_label_operand src /\
     EVERY runtime_sym_inst (state_insts s) /\
     lower_abi_encode (ensure : bool) mid src info n s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!src info lo hi size s op s'. ~is_label_operand src /\
     EVERY runtime_sym_inst (state_insts s) /\
     lower_abi_decode src info lo hi size s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce buf off vs s s'. ~is_label_operand buf /\
     EVERY (\v. ~is_label_operand (FST v)) vs /\ runtime_sym_env ce /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_store_abi_tuple ce buf off vs s = ((),s') ==>
     EVERY runtime_sym_inst (state_insts s'))
End

Definition runtime_sym_generator_contracts_def:
  runtime_sym_generator_contracts tops <=>
    runtime_sym_lower_value_clause tops /\
    runtime_sym_lower_value_with_loc_clause tops /\
    runtime_sym_subscript_clause tops /\ runtime_sym_attribute_clause tops /\
    runtime_sym_target_ptr_clause tops /\ runtime_sym_multi_vvs_clause tops /\
    runtime_sym_multi_exprs_clause tops /\ runtime_sym_make_tuple_clause tops /\
    runtime_sym_make_array_clause tops /\ runtime_sym_make_array_elems_clause tops /\
    runtime_sym_struct_lit_clause tops /\ runtime_sym_abi_encode_args_clause tops /\
    runtime_sym_concat_clause tops /\ runtime_sym_call_clause tops /\
    runtime_sym_acc_clause tops /\ runtime_sym_context_clauses /\
    runtime_sym_expr_primitive_clauses /\ runtime_sym_name_fastpath_clauses /\
    runtime_sym_math_clauses /\ runtime_sym_simple_clauses /\
    runtime_sym_misc_clauses /\ runtime_sym_abi_clauses
End

Theorem runtime_sym_generators_lower_value:
  runtime_sym_generator_contracts tops ==> runtime_sym_lower_value_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_lower_value_with_loc:
  runtime_sym_generator_contracts tops ==> runtime_sym_lower_value_with_loc_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_subscript:
  runtime_sym_generator_contracts tops ==> runtime_sym_subscript_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_attribute:
  runtime_sym_generator_contracts tops ==> runtime_sym_attribute_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_target_ptr:
  runtime_sym_generator_contracts tops ==> runtime_sym_target_ptr_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_multi_vvs:
  runtime_sym_generator_contracts tops ==> runtime_sym_multi_vvs_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_multi_exprs:
  runtime_sym_generator_contracts tops ==> runtime_sym_multi_exprs_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_make_tuple:
  runtime_sym_generator_contracts tops ==> runtime_sym_make_tuple_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_make_array:
  runtime_sym_generator_contracts tops ==> runtime_sym_make_array_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_make_array_elems:
  runtime_sym_generator_contracts tops ==> runtime_sym_make_array_elems_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_struct_lit:
  runtime_sym_generator_contracts tops ==> runtime_sym_struct_lit_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_abi_encode_args:
  runtime_sym_generator_contracts tops ==> runtime_sym_abi_encode_args_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_concat:
  runtime_sym_generator_contracts tops ==> runtime_sym_concat_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_call:
  runtime_sym_generator_contracts tops ==> runtime_sym_call_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_acc:
  runtime_sym_generator_contracts tops ==> runtime_sym_acc_clause tops
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_context:
  runtime_sym_generator_contracts tops ==> runtime_sym_context_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_expr_primitive:
  runtime_sym_generator_contracts tops ==> runtime_sym_expr_primitive_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_name_fastpath:
  runtime_sym_generator_contracts tops ==> runtime_sym_name_fastpath_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_math:
  runtime_sym_generator_contracts tops ==> runtime_sym_math_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_simple:
  runtime_sym_generator_contracts tops ==> runtime_sym_simple_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_misc:
  runtime_sym_generator_contracts tops ==> runtime_sym_misc_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

Theorem runtime_sym_generators_abi:
  runtime_sym_generator_contracts tops ==> runtime_sym_abi_clauses
Proof
  simp[runtime_sym_generator_contracts_def]
QED

(* Whitelist boundaries, rather than impossible inhabited dead-branch probes. *)
Theorem runtime_sym_builtin_rejected:
  ~supported_builtin_form tops ty (Slice n) es /\
  ~supported_builtin_form tops ty Keccak256 es /\
  ~supported_builtin_form tops ty Sha256 es /\
  ~supported_builtin_form tops ty Len es /\
  ~supported_builtin_form tops ty Ceil es /\
  ~supported_builtin_form tops ty Floor es /\
  ~supported_builtin_form tops ty (Concat n) es /\
  ~supported_builtin_form tops ty MethodId es
Proof
  simp[supported_builtin_form_def]
QED

Theorem runtime_sym_extract32_rejected:
  ~supported_type_builtin_form tops ty Extract32 target es
Proof
  Cases_on `es` >- simp[supported_type_builtin_form_def]
  >> Cases_on `t` >> simp[supported_type_builtin_form_def]
QED

Theorem runtime_sym_membership_rejected:
  ~supported_binop In ty rhs lb ne /\ ~supported_binop NotIn ty rhs lb ne
Proof
  simp[supported_binop_def]
QED

Theorem runtime_sym_make_array_children:
  supported_expr tops (Builtin rt (MakeArray elem bound) es) /\
  ~supported_expr_exists is_self_code (Builtin rt (MakeArray elem bound) es) /\
  MEM e es ==>
  supported_pure_expr tops e /\ ~supported_expr_exists is_self_code e /\
  expr_size e < list_size expr_size es
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       supported_pure_exprs_every, supported_expr_exists_def] >>
  rpt strip_tac
  >- gvs[EVERY_MEM]
  >- (gvs[supported_exprs_exists_every, EVERY_MEM])
  >> irule expr_list_member_bound >> simp[]
QED

Theorem runtime_sym_pop_target_domain:
  supported_expr tops (Pop ty target) ==>
  (?id. target = TopLevelNameTarget id /\ supported_storage_dynamic_array tops id) /\
  (!p. ~supported_target_exists p target)
Proof
  Cases_on `target` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       supported_expr_exists_def]
QED

(* An inhabited nested aggregate: callbacks must accept aggregate children,
   not just word leaves, and remain bounded at each list boundary. *)
Theorem runtime_sym_nested_make_array_probe:
  supported_expr []
    (Builtin (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Fixed 1))
      (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Fixed 1))
      [Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
        (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
        [Name (BaseT (UintT 256)) "x"]]) /\
  expr_size (Name (BaseT (UintT 256)) "x") <
    list_size expr_size [Name (BaseT (UintT 256)) "x"]
Proof
  EVAL_TAC
QED
