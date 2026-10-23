(* Independently evaluate the compiler on the side-effect witnesses. *)
Theory evalCompilerAssignmentEffects
Ancestors
  evalAssignmentOrderFrontend compileVyper concretizeMemLocDefs
  alist byte integer_word option
Libs
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../assignment-order/oracle", "../assignment-order/sources",
   "../assignment-order/fixtures.txt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

fun byte_string tm = let
  val (bytes,_) = listSyntax.dest_list tm
  fun byte b = let
    val n = Arbnum.toInt (Arbnum.mod
      (wordsSyntax.dest_word_literal b, Arbnum.fromInt 256))
    val s = Int.fmt StringCvt.HEX n
  in if size s = 1 then "0" ^ s else s end
in String.concat (List.map byte bytes) end;

fun evaluate_fixture (name, require_match) = let
  val program = prim_mk_const
    {Thy = "evalAssignmentOrderFrontend", Name = name ^ "_source_program"}
  val compiled = EVAL
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program``
  val actual = optionSyntax.dest_some (rhs (concl compiled))
  val expected = rhs (concl (EVAL (evalCompilerBytecodeLib.read_hex_bytes_from
    ("../assignment-order/oracle/" ^ name ^ ".hex"))))
  val equality = EVAL (mk_eq (actual, expected))
  val same = aconv (rhs (concl equality)) ``T``
  val certificate = if same then
      TRANS compiled (AP_TERM (rator (rhs (concl compiled))) (EQT_ELIM equality))
    else compiled
  val _ = save_thm (name ^ (if same then "_matches_python" else "_compiled"), certificate)
  val (deploy,runtime) = pairSyntax.dest_pair actual
  val _ = print ("HOL_BYTECODE " ^ name ^ " deploy=" ^ byte_string deploy ^ "\n")
  val _ = print ("HOL_BYTECODE " ^ name ^ " runtime=" ^ byte_string runtime ^ "\n")
  val _ = if require_match andalso not same then
    raise Fail (name ^ ": compiler differs from pinned Vyper") else ()
in print ("Vyper comparison " ^ name ^ ": " ^
     (if same then "MATCH" else "PARITY_DEFECT") ^ "\n") end;

val () = List.app evaluate_fixture
  [("c08_storage_arr_assign_computed_rhs", true),
   ("c09_storage_map_assign_computed_rhs", true),
   ("g6_write_order_side", true),
   ("x04_assign_sideeffect_order", true),
   ("s11_storage_map_assign_extcall_rhs", true),
   ("g19_aug_rhs_modifies_target", true),
   (* Exact x03 bytecode equality also depends on the separate #560 literal fix. *)
   ("x03_assign_elem_from_pop", false),
   ("assign_delayed_storage_read", false),
   ("assign_delayed_popped_read", false),
   ("assign_nested_popped_read", false),
   ("aug_storage_shrink", false),
   ("aug_memory_shrink", false),
   ("aug_memory_shrink_append", false)];
