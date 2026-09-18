Theory vyperCheckContractLibTest
Ancestors
  vyperTypeContract
Libs
  vyperCheckContractLib

val empty_layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``
val empty_modules =
  ``([(NONE, [])] : (num option # toplevel list) list)``
val zero_address = ``(0w : address)``

fun assert_some th =
  if optionSyntax.is_some (rhs (concl th)) then ()
  else raise Fail "expected successful check_contract result"

fun assert_none th =
  if optionSyntax.is_none (rhs (concl th)) then ()
  else raise Fail "expected rejected check_contract result"

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
