Theory vyperCheckContractLibTest
Ancestors
  vyperTypeContract evalCompilerSubsetAbiBuiltins vyperABI vyperContext
  vyperTypeSystem vyperTyping vyperValueOperation
Libs
  vyperCheckContractLib cv_transLib

val empty_layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``
val empty_modules =
  ``([(NONE, [])] : (num option # toplevel list) list)``
val zero_address = ``(0w : address)``

(* AddressV is represented as twenty bytes. Wider destinations need different
   padding from ordinary byte strings and deliberately remain unsupported. *)
Theorem address_bytes_conversion_boundary:
  valid_conversion (BaseT AddressT) (BaseT (BytesT bd)) <=> bd = Fixed 20
Proof
  Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem address_bytes20_preserves_value:
  value_has_type (BaseTV AddressT) v ==>
  evaluate_convert tenv v (BaseT (BytesT (Fixed 20))) = INL v
Proof
  Cases_on `v` >>
  simp[value_has_type_def, evaluate_convert_def, listTheory.PAD_RIGHT] >>
  strip_tac >> gvs[]
QED

Theorem address_bytes20_values_eval:
  evaluate_convert FEMPTY (AddressV 0w) (BaseT (BytesT (Fixed 20))) =
    INL (BytesV (REPLICATE 20 0w)) /\
  evaluate_convert FEMPTY (AddressV 1w) (BaseT (BytesT (Fixed 20))) =
    INL (BytesV (REPLICATE 19 0w ++ [1w])) /\
  evaluate_convert FEMPTY (AddressV 1461501637330902918203684832716283019655932542975w)
    (BaseT (BytesT (Fixed 20))) = INL (BytesV (REPLICATE 20 255w))
Proof
  EVAL_TAC
QED

Theorem address_bytes_conversion_widths_eval:
  EVERY (λn. valid_conversion (BaseT AddressT) (BaseT (BytesT (Fixed n))) =
             (n = 20)) (GENLIST SUC 32) /\
  ¬valid_conversion (BaseT AddressT) (BaseT (BytesT (Dynamic 20))) /\
  ¬valid_conversion (BaseT AddressT) (BaseT (BytesT (Dynamic 32)))
Proof
  EVAL_TAC
QED

(* ABI encoding's bound follows the evaluator's singleton wrapping mode.
   The unchanged encode_dynamic fixture has an inner bound of 192 bytes,
   plus its four-byte method id, not a 224-byte outer tuple plus method id. *)
Theorem abi_encode_dynamic_exact_bound:
  type_builtin_result_ok FEMPTY (AbiEncode ensure method_id)
    (BaseT (BytesT (Dynamic n)))
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]] <=>
  (if ensure then 224 else 192) + abi_encode_method_id_size method_id <= n
Proof
  Cases_on `ensure` >>
  simp[type_builtin_result_ok_def, abi_encode_size_ok_def,
       vyper_abi_size_bound_def, vyper_is_dynamic_def, contractABITheory.ceil32_def]
QED

Theorem abi_encode_dynamic_wrapping_bounds:
  abi_encode_size_ok FEMPTY F
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    (SOME [222w; 173w; 190w; 239w]) 196 /\
  ¬abi_encode_size_ok FEMPTY T
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    (SOME [222w; 173w; 190w; 239w]) 196 /\
  abi_encode_size_ok FEMPTY T
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    (SOME [222w; 173w; 190w; 239w]) 228 /\
  abi_encode_size_ok FEMPTY F
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]]) NONE 192 /\
  abi_encode_size_ok FEMPTY T
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]]) NONE 224
Proof
  EVAL_TAC
QED

(* All other target shapes keep their previous bound; no method-id restriction
   is smuggled into the size predicate. Argument validation remains separate. *)
Theorem abi_encode_other_targets_unchanged:
  (!ts. target_ty <> TupleT ts) ==>
  (abi_encode_size_ok tenv ensure target_ty method_id n <=>
   vyper_abi_size_bound tenv target_ty + abi_encode_method_id_size method_id <= n)
Proof
  Cases_on `target_ty` >> simp[abi_encode_size_ok_def]
QED

Theorem abi_encode_nonsingleton_tuples_unchanged:
  LENGTH ts <> 1 ==>
  (abi_encode_size_ok tenv ensure (TupleT ts) method_id n <=>
   vyper_abi_size_bound tenv (TupleT ts) + abi_encode_method_id_size method_id <= n)
Proof
  Cases_on `ts` >> simp[abi_encode_size_ok_def] >>
  strip_tac >> rename1 `rest <> []` >> Cases_on `rest` >> gvs[]
QED

(* Targeted CV translation/check of the changed checker predicate, rather than
   relying solely on its kernel computation path. *)
val () = cv_auto_trans abi_encode_method_id_size_def;
val () = cv_auto_trans abi_encode_size_ok_def;

Theorem abi_encode_dynamic_result_bound_cv:
  type_builtin_result_ok FEMPTY (AbiEncode F (SOME [222w; 173w; 190w; 239w]))
    (BaseT (BytesT (Dynamic 196)))
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]] /\
  ¬type_builtin_result_ok FEMPTY (AbiEncode T (SOME [222w; 173w; 190w; 239w]))
    (BaseT (BytesT (Dynamic 196)))
    (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
    [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]]
Proof
  simp[type_builtin_result_ok_def] >> CONV_TAC cv_eval
QED

(* Maximal well-typed dynamic inputs attain the four advertised bounds in the
   evaluator, including both method-id and wrapping choices. *)
Definition abi_encode_wrapping_cases_ok_def:
  abi_encode_wrapping_cases_ok = EVERY (λ(ensure, method_id, n).
    case evaluate_type_builtin empty_evaluation_context (AbiEncode ensure method_id)
      (TupleT [TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
      [ArrayV (TupleV [StringV "abcdefghijklmnop"; BytesV (REPLICATE 16 1w)])] of
      INL (BytesV bs) => LENGTH bs = n
    | _ => F)
    [(F, NONE, 192); (T, NONE, 224);
     (F, SOME [222w; 173w; 190w; 239w], 196);
     (T, SOME [222w; 173w; 190w; 239w], 228)]
End
val () = cv_auto_trans abi_encode_wrapping_cases_ok_def;

Theorem abi_encode_wrapping_lengths_eval:
  abi_encode_wrapping_cases_ok
Proof
  EVAL_TAC
QED

Theorem abi_encode_wrapping_lengths_cv:
  abi_encode_wrapping_cases_ok
Proof
  CONV_TAC cv_eval
QED

Theorem abi_dynamic_fixture_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, task090_abi_dynamic_program)])
Proof
  simp[task090_abi_dynamic_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_dynamic_fixture_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, task090_abi_dynamic_program)])
Proof
  simp[task090_abi_dynamic_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

fun assert_some th =
  if optionSyntax.is_some (rhs (concl th)) then ()
  else raise Fail "expected successful check_contract result"

(* ecrecover takes v as uint8 or uint256 only; r and s stay uint256 or bytes32. *)
Theorem ecrecover_narrow_argument_rejection_test:
  ~well_typed_builtin_app (BaseT AddressT) ECRecover
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 16); BaseT (UintT 256);
     BaseT (UintT 256)] /\
  ~well_typed_builtin_app (BaseT AddressT) ECRecover
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 256); BaseT (UintT 8);
     BaseT (UintT 256)] /\
  ~well_typed_builtin_app (BaseT AddressT) ECRecover
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 256); BaseT (UintT 256);
     BaseT (UintT 8)]
Proof
  simp[well_typed_builtin_app_def]
QED

fun assert_none th =
  if optionSyntax.is_none (rhs (concl th)) then ()
  else raise Fail "expected rejected check_contract result"

fun check_address_bytes bd in_deploy = let
  val modules =
    ``([(NONE,
         [FunctionDecl External Pure F F "f"
            [("a", BaseT AddressT)] [] (BaseT (BytesT ^bd))
            [Return (SOME
               (TypeBuiltin (BaseT (BytesT ^bd)) Convert
                 (BaseT (BytesT ^bd)) [Name (BaseT AddressT) "a"]))]])]
        : (num option # toplevel list) list)``
in
  vyperCheckContractLib.check_contract_conv
    ``check_contract ^(if in_deploy then T else F) ^empty_layouts
        ^zero_address ^modules``
end

val () = List.app (fn in_deploy =>
  (assert_some (check_address_bytes ``Fixed 20`` in_deploy);
   List.app (fn bd => assert_none (check_address_bytes bd in_deploy))
     [``Fixed 19``, ``Fixed 21``, ``Fixed 32``,
      ``Dynamic 20``, ``Dynamic 32``])) [false, true]

(* Basic API and ML-Boolean construction. *)
val empty_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = empty_modules}
val () = assert_some empty_check

(* Storage layout lookup and public getter artifact construction. *)
val storage_modules =
  ``([(NONE,
       [VariableDecl Public Storage "stored" (BaseT (UintT 256)) (SOME 0);
        FunctionDecl External View F F "read" [] [] (BaseT (UintT 256))
          [Return (SOME
             (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]])]
      : (num option # toplevel list) list)``
val storage_layouts =
  ``([((0w : address),
       ([((NONE, "stored"), 0)] : storage_layout, [] : storage_layout))]
      : (address # (storage_layout # storage_layout)) list)``
val storage_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = storage_layouts,
   address = zero_address, modules = storage_modules}
val () = assert_some storage_check

(* This requires the checker-specific existential witness conversion, default
   argument typing, string computation, and internal call-graph evaluation. *)
val internal_modules =
  ``([(NONE,
       [FunctionDecl Internal Nonpayable F F "bar"
          [("x", BaseT (UintT 256))]
          [Literal (BaseT (UintT 256)) (IntL 7)]
          (BaseT (UintT 256))
          [Return (SOME (Name (BaseT (UintT 256)) "x"))];
        FunctionDecl External Nonpayable F F "foo" [] []
          (BaseT (UintT 256))
          [Return (SOME
             (Call (BaseT (UintT 256)) (IntCall (NONE, "bar")) [] NONE))]])]
      : (num option # toplevel list) list)``
val internal_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = internal_modules}
val () = assert_some internal_check
val call_graph_constant = prim_mk_const
  {Thy = "vyperTypeCallGraph", Name = "contract_call_graph_acyclic"}
val internal_graph_application = mk_comb (call_graph_constant, internal_modules)
val internal_graph_result = vyperCheckContractLib.check_contract_conv
  internal_graph_application
val () = if aconv (lhs (concl internal_graph_result)) internal_graph_application andalso
                aconv (rhs (concl internal_graph_result)) T then ()
         else raise Fail "acyclic internal-call graph was rejected"

(* Compiler-generated integer conversions require valid_conversion to compute. *)
val conversion_modules =
  ``([(NONE,
       [FunctionDecl External Pure F F "widen"
          [("x", BaseT (UintT 8))] [] (BaseT (UintT 256))
          [Return (SOME
             (TypeBuiltin (BaseT (UintT 256)) Convert
               (BaseT (UintT 256))
               [Name (BaseT (UintT 8)) "x"]))]])]
      : (num option # toplevel list) list)``
val conversion_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = conversion_modules}
val () = assert_some conversion_check

(* len() requires sized-type classification to compute. *)
val sized_modules =
  ``([(NONE,
       [FunctionDecl External Pure F F "array_len"
          [("xs", ArrayT (BaseT AddressT) (Dynamic 4))] []
          (BaseT (UintT 256))
          [Return (SOME
             (Builtin (BaseT (UintT 256)) Len
               [Name (ArrayT (BaseT AddressT) (Dynamic 4)) "xs"]))]])]
      : (num option # toplevel list) list)``
val sized_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = sized_modules}
val () = assert_some sized_check

(* The conversion itself computes rejection to NONE. The success-only API must
   fail closed on that result. *)
val recursive_modules =
  ``([(NONE,
       [FunctionDecl Internal Nonpayable F F "loop" [] []
          (BaseT (UintT 256))
          [Return (SOME
             (Call (BaseT (UintT 256)) (IntCall (NONE, "loop")) [] NONE))]])]
      : (num option # toplevel list) list)``
val recursive_application = vyperCheckContractLib.mk_check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = recursive_modules}
val recursive_check =
  vyperCheckContractLib.check_contract_conv recursive_application
val () = assert_none recursive_check

(* The specialized call-graph conversion also proves longer cycles directly. *)
val two_cycle_modules =
  ``([(NONE,
       [FunctionDecl Internal Nonpayable F F "left" [] [] NoneT
          [Expr (Call NoneT (IntCall (NONE, "right")) [] NONE)];
        FunctionDecl Internal Nonpayable F F "right" [] [] NoneT
          [Expr (Call NoneT (IntCall (NONE, "left")) [] NONE)]])]
      : (num option # toplevel list) list)``
val two_cycle_application = mk_comb (call_graph_constant, two_cycle_modules)
val two_cycle_result = vyperCheckContractLib.check_contract_conv
  two_cycle_application
val () = if aconv (lhs (concl two_cycle_result)) two_cycle_application andalso
                aconv (rhs (concl two_cycle_result)) F then ()
         else raise Fail "two-node call cycle was not rejected"

fun fails thunk = ((thunk (); false) handle _ => true)
val () =
  if fails (fn () => ignore (vyperCheckContractLib.check_contract
       {in_deploy = false, layouts = empty_layouts,
        address = zero_address, modules = recursive_modules})) then ()
  else raise Fail "success API accepted a rejected contract"

(* Open inputs are rejected before conversion. *)
val () =
  if fails (fn () => ignore (vyperCheckContractLib.mk_check_contract
       {in_deploy = false, layouts = empty_layouts,
        address = mk_var ("address", type_of zero_address),
        modules = empty_modules})) then ()
  else raise Fail "open checker input was accepted"

(* The exported compset is cached and sealed, while copy permits functional
   caller extension without changing the library instance. *)
val checker_copy =
  vyperCheckContractLib.check_contract_compset |> computeLib.copy
val copied_empty_check = computeLib.CBV_CONV checker_copy
  (vyperCheckContractLib.mk_check_contract
    {in_deploy = false, layouts = empty_layouts,
     address = zero_address, modules = empty_modules})
val () = assert_some copied_empty_check

(* Closed list computations exercise the checker-local list fragment directly. *)
fun timed_checker_conv label tm = let
  val timer = Timer.startRealTimer ()
  val theorem = computeLib.CBV_CONV
    vyperCheckContractLib.check_contract_compset tm
  val elapsed = Time.toReal (Timer.checkRealTimer timer)
  val () = print (label ^ " duration=" ^ Real.toString elapsed ^ "s\n")
in
  (theorem, elapsed)
end

fun assert_closed_result input expected theorem = let
  val () = if null (hyp theorem) then ()
    else raise Fail "checker conversion theorem has assumptions"
  val (actual_input, actual_result) = dest_eq (concl theorem)
in
  if aconv actual_input input andalso aconv actual_result expected then ()
  else raise Fail "unexpected checker conversion result"
end

val all_distinct_input = ``ALL_DISTINCT [NONE : num option]``
val (all_distinct_result, _) =
  timed_checker_conv "ALL_DISTINCT singleton" all_distinct_input
val () = assert_closed_result all_distinct_input ``T`` all_distinct_result

val endpoint_ty = ``:num option # string``
fun mk_endpoint i = pairSyntax.mk_pair
  (optionSyntax.mk_some (numSyntax.mk_numeral (Arbnum.fromInt i)),
   stringSyntax.fromMLstring ("function_" ^ Int.toString i))
fun endpoint_indices start count = List.tabulate (count, fn i => start + i)
fun mk_endpoint_indices indices =
  listSyntax.mk_list (map mk_endpoint indices, endpoint_ty)
fun mk_endpoint_list count =
  mk_endpoint_indices (List.tabulate (count, fn i => i mod 35))
fun mk_nub_input count =
  mk_comb
    (Term.inst [alpha |-> endpoint_ty] ``list$nub``, mk_endpoint_list count)

val nub_40_input = mk_nub_input 40
val expected_nub_40 =
  mk_endpoint_indices (endpoint_indices 5 30 @ endpoint_indices 0 5)
val (nub_40_result, nub_40_elapsed) =
  timed_checker_conv "nub 40 endpoints" nub_40_input
val () = assert_closed_result nub_40_input expected_nub_40 nub_40_result

val nub_80_input = mk_nub_input 80
val expected_nub_80 =
  mk_endpoint_indices (endpoint_indices 10 25 @ endpoint_indices 0 10)
val (nub_80_result, nub_80_elapsed) =
  timed_checker_conv "nub 80 endpoints" nub_80_input
val () = assert_closed_result nub_80_input expected_nub_80 nub_80_result

val set_membership_input = ``(1 : num) IN {1; 2}``
val (set_membership_result, _) =
  timed_checker_conv "predicate-set membership" set_membership_input
val () = assert_closed_result set_membership_input ``T`` set_membership_result

(* The compset leaves INSERT chains undeduplicated, so FDOM of a map with a
   re-inserted key keeps the duplicate; membership must still decide. *)
val reinserted_fdom = ``FDOM (FEMPTY |+ ("x", 1n) |+ ("y", 2n) |+ ("x", 3n))``
val fresh_input = ``"z" NOTIN ^reinserted_fdom``
val (fresh_result, _) =
  timed_checker_conv "fresh key, re-inserted domain" fresh_input
val () = assert_closed_result fresh_input ``T`` fresh_result
val stale_input = ``"x" NOTIN ^reinserted_fdom``
val (stale_result, _) =
  timed_checker_conv "declared key, re-inserted domain" stale_input
val () = assert_closed_result stale_input ``F`` stale_result

(* One contract per builtin and type-builtin constructor, per account item,
   and per raw_create argument shape, each returning the builtin's result from
   an external function. The checker must decide each one; an unevaluated
   result means checker_defs lacks an auxiliary definition of that
   constructor's typing rule. *)
fun builtin_modules mutability params ret_ty result =
  ``[(NONE,
      [FunctionDecl External ^mutability F F "f" ^params ([] : expr list)
         ^ret_ty [Return (SOME ^result)]])]
    : (num option # toplevel list) list``

val no_params = ``[] : (string # type) list``
val u256_params = ``[("a", BaseT (UintT 256)); ("b", BaseT (UintT 256))]``
val u256x3_params =
  ``[("a", BaseT (UintT 256)); ("b", BaseT (UintT 256));
     ("c", BaseT (UintT 256))]``
val address_params = ``[("a", BaseT AddressT)]``
val bytes10_params = ``[("b", BaseT (BytesT (Dynamic 10)))]``
val point_ty = ``ArrayT (BaseT (UintT 256)) (Fixed 2)``

val builtin_cases = [
  ("Len", ``Pure``, bytes10_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) Len [Name (BaseT (BytesT (Dynamic 10))) "b"]``),
  ("CalldataLen", ``View``, no_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) CalldataLen []``),
  ("CalldataSlice", ``View``, no_params, ``BaseT (BytesT (Dynamic 4))``,
   ``Builtin (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4)
       [Literal (BaseT (UintT 256)) (IntL 0)]``),
  ("Not", ``Pure``, ``[("x", BaseT BoolT)]``, ``BaseT BoolT``,
   ``Builtin (BaseT BoolT) Not [Name (BaseT BoolT) "x"]``),
  ("Neg", ``Pure``, ``[("x", BaseT (IntT 256))]``, ``BaseT (IntT 256)``,
   ``Builtin (BaseT (IntT 256)) Neg [Name (BaseT (IntT 256)) "x"]``),
  ("Abs", ``Pure``, ``[("x", BaseT (IntT 256))]``, ``BaseT (IntT 256)``,
   ``Builtin (BaseT (IntT 256)) Abs [Name (BaseT (IntT 256)) "x"]``),
  ("Keccak256", ``Pure``, bytes10_params, ``BaseT (BytesT (Fixed 32))``,
   ``Builtin (BaseT (BytesT (Fixed 32))) Keccak256
       [Name (BaseT (BytesT (Dynamic 10))) "b"]``),
  ("Sha256", ``Pure``, bytes10_params, ``BaseT (BytesT (Fixed 32))``,
   ``Builtin (BaseT (BytesT (Fixed 32))) Sha256
       [Name (BaseT (BytesT (Dynamic 10))) "b"]``),
  ("AsWeiValue", ``Pure``, ``[("x", BaseT (UintT 256))]``, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) (AsWeiValue Gwei) [Name (BaseT (UintT 256)) "x"]``),
  ("Concat", ``Pure``,
   ``[("a", BaseT (BytesT (Dynamic 4))); ("b", BaseT (BytesT (Dynamic 6)))]``,
   ``BaseT (BytesT (Dynamic 10))``,
   ``Builtin (BaseT (BytesT (Dynamic 10))) (Concat 10)
       [Name (BaseT (BytesT (Dynamic 4))) "a";
        Name (BaseT (BytesT (Dynamic 6))) "b"]``),
  ("Slice", ``Pure``, bytes10_params, ``BaseT (BytesT (Dynamic 2))``,
   ``Builtin (BaseT (BytesT (Dynamic 2))) (Slice 2)
       [Name (BaseT (BytesT (Dynamic 10))) "b";
        Literal (BaseT (UintT 256)) (IntL 1);
        Literal (BaseT (UintT 256)) (IntL 2)]``),
  ("Uint2Str", ``Pure``, ``[("x", BaseT (UintT 256))]``, ``BaseT (StringT 78)``,
   ``Builtin (BaseT (StringT 78)) (Uint2Str 78) [Name (BaseT (UintT 256)) "x"]``),
  ("MakeArray array", ``Pure``, ``[("x", BaseT (UintT 256))]``, point_ty,
   ``Builtin ^point_ty (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
       [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 2)]``),
  ("MakeArray tuple", ``Pure``, ``[("x", BaseT (UintT 256))]``,
   ``TupleT [BaseT (UintT 256); BaseT BoolT]``,
   ``Builtin (TupleT [BaseT (UintT 256); BaseT BoolT]) (MakeArray NONE (Fixed 2))
       [Name (BaseT (UintT 256)) "x"; Literal (BaseT BoolT) (BoolL T)]``),
  ("Ceil", ``Pure``, ``[("x", BaseT DecimalT)]``, ``BaseT (IntT 256)``,
   ``Builtin (BaseT (IntT 256)) Ceil [Name (BaseT DecimalT) "x"]``),
  ("Floor", ``Pure``, ``[("x", BaseT DecimalT)]``, ``BaseT (IntT 256)``,
   ``Builtin (BaseT (IntT 256)) Floor [Name (BaseT DecimalT) "x"]``),
  ("AddMod", ``Pure``, u256x3_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) AddMod
       [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b";
        Name (BaseT (UintT 256)) "c"]``),
  ("MulMod", ``Pure``, u256x3_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) MulMod
       [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b";
        Name (BaseT (UintT 256)) "c"]``),
  ("Bop", ``Pure``, u256_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) (Bop Add)
       [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b"]``),
  ("BlockHash", ``View``, no_params, ``BaseT (BytesT (Fixed 32))``,
   ``Builtin (BaseT (BytesT (Fixed 32))) BlockHash
       [Builtin (BaseT (UintT 256)) (Bop Sub)
          [Builtin (BaseT (UintT 256)) (Env BlockNumber) [];
           Literal (BaseT (UintT 256)) (IntL 1)]]``),
  ("BlobHash", ``View``, no_params, ``BaseT (BytesT (Fixed 32))``,
   ``Builtin (BaseT (BytesT (Fixed 32))) BlobHash
       [Literal (BaseT (UintT 256)) (IntL 0)]``),
  ("Env", ``View``, no_params, ``BaseT AddressT``,
   ``Builtin (BaseT AddressT) (Env Sender) []``),
  ("Acc Balance", ``View``, address_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) (Acc Balance) [Name (BaseT AddressT) "a"]``),
  ("Acc Codehash", ``View``, address_params, ``BaseT (BytesT (Fixed 32))``,
   ``Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash)
       [Name (BaseT AddressT) "a"]``),
  ("Acc Codesize", ``View``, address_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) (Acc Codesize) [Name (BaseT AddressT) "a"]``),
  ("Acc IsContract", ``View``, address_params, ``BaseT BoolT``,
   ``Builtin (BaseT BoolT) (Acc IsContract) [Name (BaseT AddressT) "a"]``),
  ("Acc Code", ``View``, address_params, ``BaseT (BytesT (Dynamic 10))``,
   ``Builtin (BaseT (BytesT (Dynamic 10))) (Slice 10)
       [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Name (BaseT AddressT) "a"];
        Literal (BaseT (UintT 256)) (IntL 0);
        Literal (BaseT (UintT 256)) (IntL 10)]``),
  ("MethodId", ``Pure``, no_params, ``BaseT (BytesT (Dynamic 4))``,
   ``Builtin (BaseT (BytesT (Dynamic 4))) MethodId
       [Literal (BaseT (StringT 3)) (StringL "g()")]``),
  ("ECRecover", ``View``,
   ``[("h", BaseT (BytesT (Fixed 32))); ("v", BaseT (UintT 256));
      ("r", BaseT (UintT 256)); ("s", BaseT (UintT 256))]``,
   ``BaseT AddressT``,
   ``Builtin (BaseT AddressT) ECRecover
       [Name (BaseT (BytesT (Fixed 32))) "h"; Name (BaseT (UintT 256)) "v";
        Name (BaseT (UintT 256)) "r"; Name (BaseT (UintT 256)) "s"]``),
  ("ECRecover uint8 v", ``Pure``,
   ``[("h", BaseT (BytesT (Fixed 32))); ("v", BaseT (UintT 8));
      ("r", BaseT (BytesT (Fixed 32))); ("s", BaseT (BytesT (Fixed 32)))]``,
   ``BaseT AddressT``,
   ``Builtin (BaseT AddressT) ECRecover
       [Name (BaseT (BytesT (Fixed 32))) "h"; Name (BaseT (UintT 8)) "v";
        Name (BaseT (BytesT (Fixed 32))) "r"; Name (BaseT (BytesT (Fixed 32))) "s"]``),
  ("ECAdd", ``View``, ``[("a", ^point_ty); ("b", ^point_ty)]``, point_ty,
   ``Builtin ^point_ty ECAdd [Name ^point_ty "a"; Name ^point_ty "b"]``),
  ("ECMul", ``View``, ``[("a", ^point_ty); ("s", BaseT (UintT 256))]``, point_ty,
   ``Builtin ^point_ty ECMul [Name ^point_ty "a"; Name (BaseT (UintT 256)) "s"]``),
  ("PowMod256", ``Pure``, u256_params, ``BaseT (UintT 256)``,
   ``Builtin (BaseT (UintT 256)) PowMod256
       [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b"]``),
  ("Empty", ``Pure``, no_params, ``BaseT (UintT 256)``,
   ``TypeBuiltin (BaseT (UintT 256)) Empty (BaseT (UintT 256)) []``),
  ("MaxValue", ``Pure``, no_params, ``BaseT (UintT 256)``,
   ``TypeBuiltin (BaseT (UintT 256)) MaxValue (BaseT (UintT 256)) []``),
  ("MinValue", ``Pure``, no_params, ``BaseT (IntT 128)``,
   ``TypeBuiltin (BaseT (IntT 128)) MinValue (BaseT (IntT 128)) []``),
  ("Epsilon", ``Pure``, no_params, ``BaseT DecimalT``,
   ``TypeBuiltin (BaseT DecimalT) Epsilon (BaseT DecimalT) []``),
  ("Convert", ``Pure``, ``[("x", BaseT (UintT 8))]``, ``BaseT (UintT 256)``,
   ``TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
       [Name (BaseT (UintT 8)) "x"]``),
  ("Extract32", ``Pure``, ``[("b", BaseT (BytesT (Dynamic 64)))]``,
   ``BaseT (BytesT (Fixed 32))``,
   ``TypeBuiltin (BaseT (BytesT (Fixed 32))) Extract32 (BaseT (BytesT (Fixed 32)))
       [Name (BaseT (BytesT (Dynamic 64))) "b";
        Literal (BaseT (UintT 256)) (IntL 0)]``),
  ("AbiEncode", ``Pure``, ``[("x", BaseT (UintT 256))]``,
   ``BaseT (BytesT (Dynamic 64))``,
   ``TypeBuiltin (BaseT (BytesT (Dynamic 64))) (AbiEncode F NONE)
       (TupleT [BaseT (UintT 256)]) [Name (BaseT (UintT 256)) "x"]``),
  ("AbiDecode", ``Pure``, ``[("b", BaseT (BytesT (Dynamic 32)))]``,
   ``BaseT (UintT 256)``,
   ``TypeBuiltin (BaseT (UintT 256)) (AbiDecode F) (BaseT (UintT 256))
       [Name (BaseT (BytesT (Dynamic 32))) "b"]``),
  ("RawCreate", ``Nonpayable``, ``[("b", BaseT (BytesT (Dynamic 100)))]``,
   ``BaseT AddressT``,
   ``Call (BaseT AddressT) (CreateTarget RawCreate F T)
       [Name (BaseT (BytesT (Dynamic 100))) "b";
        Literal (BaseT (UintT 256)) (IntL 0)] NONE``),
  ("RawCreate salt", ``Nonpayable``,
   ``[("b", BaseT (BytesT (Dynamic 100))); ("s", BaseT (BytesT (Fixed 32)))]``,
   ``BaseT AddressT``,
   ``Call (BaseT AddressT) (CreateTarget RawCreate T T)
       [Name (BaseT (BytesT (Dynamic 100))) "b";
        Literal (BaseT (UintT 256)) (IntL 0);
        Name (BaseT (BytesT (Fixed 32))) "s"] NONE``),
  ("RawCreate ctor args and salt", ``Nonpayable``,
   ``[("b", BaseT (BytesT (Dynamic 100))); ("a", BaseT (UintT 256));
      ("s", BaseT (BytesT (Fixed 32)))]``,
   ``BaseT AddressT``,
   ``Call (BaseT AddressT) (CreateTarget RawCreate T T)
       [Name (BaseT (BytesT (Dynamic 100))) "b";
        Literal (BaseT (UintT 256)) (IntL 0);
        Name (BaseT (UintT 256)) "a";
        Name (BaseT (BytesT (Fixed 32))) "s"] NONE``)]

fun check_accepts label in_deploy layouts modules =
  ignore (vyperCheckContractLib.check_contract
    {in_deploy = in_deploy, layouts = layouts,
     address = zero_address, modules = modules})
  handle e => raise Fail (label ^ ": " ^ General.exnMessage e)

val () = List.app (fn (label, mutability, params, ret_ty, result) =>
    check_accepts label false empty_layouts
      (builtin_modules mutability params ret_ty result))
  builtin_cases

(* An interface value has type address, so `i.address` on an interface
   parameter i is Acc Address applied to an address-typed name. *)
val () = check_accepts "Acc Address" false empty_layouts
  ``[(NONE,
      [FunctionDecl External Pure F F "f" [("i", BaseT AddressT)]
         ([] : expr list) (BaseT AddressT)
         [Return (SOME
            (Builtin (BaseT AddressT) (Acc Address)
               [Name (BaseT AddressT) "i"]))]])]
    : (num option # toplevel list) list``

(* Account items in __init__ are typed only in deployment mode. *)
val () = check_accepts "Acc Balance in __init__" true storage_layouts
  ``[(NONE,
      [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
       FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
         [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
            (Builtin (BaseT (UintT 256)) (Acc Balance)
               [Builtin (BaseT AddressT) (Env SelfAddr) []])]])]
    : (num option # toplevel list) list``

(* Nested HashMap reads keyed by internal calls: typing the inner subscript
   looks up the call's signature inside the outer subscript's place type. *)
val nested_map_layouts =
  ``([((0w : address),
       ([((NONE, "m"), 0); ((NONE, "c"), 1)] : storage_layout,
        [] : storage_layout))]
      : (address # (storage_layout # storage_layout)) list)``
val nested_map_modules =
  ``[(NONE,
      [HashMapDecl Private F "m" (BaseT (UintT 256))
         (HashMapT (BaseT (UintT 256)) (Type (BaseT (UintT 256)))) (SOME 0);
       VariableDecl Private Storage "c" (BaseT (UintT 256)) (SOME 1);
       FunctionDecl Internal Nonpayable F F "g" [] [] (BaseT (UintT 256))
         [AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE, "c")) Add
            (Literal (BaseT (UintT 256)) (IntL 1));
          Return (SOME (TopLevelName (BaseT (UintT 256)) (NONE, "c")))];
       FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
         [AnnAssign "x" (BaseT (UintT 256))
            (Subscript (BaseT (UintT 256))
               (Subscript NoneT (TopLevelName NoneT (NONE, "m"))
                  (Call (BaseT (UintT 256)) (IntCall (NONE, "g")) [] NONE))
               (Literal (BaseT (UintT 256)) (IntL 1)));
          Return (SOME (Name (BaseT (UintT 256)) "x"))]])]
    : (num option # toplevel list) list``
val () = check_accepts "nested map read, runtime" false nested_map_layouts
  nested_map_modules
val () = check_accepts "nested map read, deployment" true nested_map_layouts
  nested_map_modules

val nested_map_both_keys_modules =
  ``[(NONE,
      [HashMapDecl Private F "m" (BaseT (UintT 256))
         (HashMapT (BaseT (UintT 256)) (Type (BaseT (UintT 256)))) (SOME 0);
       VariableDecl Private Storage "c" (BaseT (UintT 256)) (SOME 1);
       FunctionDecl Internal Nonpayable F F "g" [] [] (BaseT (UintT 256))
         [AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE, "c")) Add
            (Literal (BaseT (UintT 256)) (IntL 1));
          Return (SOME (TopLevelName (BaseT (UintT 256)) (NONE, "c")))];
       FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
         [AnnAssign "x" (BaseT (UintT 256))
            (Subscript (BaseT (UintT 256))
               (Subscript NoneT (TopLevelName NoneT (NONE, "m"))
                  (Call (BaseT (UintT 256)) (IntCall (NONE, "g")) [] NONE))
               (Call (BaseT (UintT 256)) (IntCall (NONE, "g")) [] NONE));
          Return (SOME (Name (BaseT (UintT 256)) "x"))]])]
    : (num option # toplevel list) list``
val () = check_accepts "nested map read, calls in both keys" false
  nested_map_layouts nested_map_both_keys_modules

(* Constant initializers are folded at check time, as Vyper folds them at
   compile time: an initializer that fails to evaluate is rejected, and so is
   a forward reference, which the deployment fold's declaration order cannot
   evaluate. *)
val u256 = ``BaseT (UintT 256)``
fun const_lit n = ``Literal ^u256 (IntL ^(intSyntax.term_of_int (Arbint.fromInt n)))``
fun const_bop bop a b = ``Builtin ^u256 (Bop ^bop) [^a; ^b]``
fun const_name id =
  ``TopLevelName ^u256 (NONE, ^(stringSyntax.fromMLstring id))``
fun const_decl id e =
  ``VariableDecl Private (Constant ^e) ^(stringSyntax.fromMLstring id) ^u256 NONE``
fun check_constants decls =
  vyperCheckContractLib.check_contract_conv
    ``check_contract F ^empty_layouts ^zero_address
        [(NONE, ^(listSyntax.mk_list (decls, ``:toplevel``)))]``
val max_u256 = ``TypeBuiltin ^u256 MaxValue ^u256 []``

val () = assert_some (check_constants
  [const_decl "A" (const_lit 1),
   const_decl "B" (const_bop ``vyperAST$Add`` (const_name "A") (const_lit 2)),
   const_decl "C" (const_bop ``vyperAST$Sub`` max_u256 (const_name "B"))])
val () = List.app (assert_none o check_constants)
  [[const_decl "X" (const_bop ``vyperAST$Div`` (const_lit 1) (const_lit 0))],
   [const_decl "X" (const_bop ``vyperAST$Sub`` (const_lit 0) (const_lit 1))],
   [const_decl "X" (const_bop ``vyperAST$Add`` max_u256 (const_lit 1))],
   [const_decl "B" (const_bop ``vyperAST$Add`` (const_name "A") (const_lit 1)),
    const_decl "A" (const_lit 1)]]


(* Every operation a constant initializer can use evaluates, rather than
   leaving check_contract stuck. *)
fun tdecl ty id e =
  ``VariableDecl Private (Constant ^e) ^(stringSyntax.fromMLstring id) ^ty NONE``
fun tbop ty bop a b = ``Builtin ^ty (Bop ^bop) [^a; ^b]``
fun tname ty id = ``TopLevelName ^ty (NONE, ^(stringSyntax.fromMLstring id))``
val dec = ``BaseT DecimalT``
val b32 = ``BaseT (BytesT (Fixed 32))``
fun dlit n =
  ``Literal ^dec (DecimalL ^(intSyntax.term_of_int (Arbint.fromString n)))``
fun int_const bop a b = [const_decl "X" (const_bop bop (const_lit a) (const_lit b))]
fun dec_const bop =
  [tdecl dec "X" (tbop dec bop (dlit "15000000000") (dlit "20000000000"))]
val keccak_a =
  ``Builtin ^b32 Keccak256 [Literal (BaseT (StringT 1)) (StringL "a")]``
val () = List.app (assert_some o check_constants)
  [int_const ``vyperAST$Div`` 7 2,
   int_const ``vyperAST$Mod`` 7 3,
   int_const ``vyperAST$Exp`` 10 18,
   int_const ``vyperAST$And`` 6 3,
   int_const ``vyperAST$Or`` 6 3,
   int_const ``vyperAST$XOr`` 6 3,
   int_const ``vyperAST$ShR`` 256 4,
   [const_decl "X" (const_bop ``vyperAST$Sub``
      (const_bop ``vyperAST$ShL`` (const_lit 1) (const_lit 160)) (const_lit 1))],
   dec_const ``vyperAST$Mul``,
   dec_const ``vyperAST$Div``,
   [tdecl b32 "K" keccak_a,
    tdecl ``BaseT BoolT`` "E"
      ``Builtin (BaseT BoolT) (Bop Eq) [^(tname b32 "K"); ^(tname b32 "K")]``]]
