(* Runs the branch_opt checker over parity fixtures with EVAL (see
   branchOptCheckCorpusScript.sml): per fixture it prints the functions, how
   many each variant rewrote and how many the check accepted, fails if the
   check rejects any, and saves the resulting theorem as
   <fixture>_branch_opt_corpus. *)
structure branchOptCorpusLib =
struct

open HolKernel boolLib bossLib
open branchOptCheckCorpusTheory

(* Loading wordsLib adds its word conversions to the compset; without them
   EVAL unfolds word arithmetic through its definitions and blows up. *)
val _ = wordsLib.WORD_ss

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
           (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
           (computeLib.add_thms [integer_wordTheory.i2w_pos])

(* The 101 hand-written programs of bytecode/python-o1-no-asm-opt, as listed
   in bytecode/native/compilerNativeEmitScript.sml; EMPTY is the program with
   no declarations. *)
val fixtures = [
  "EMPTY", "account_items_program", "add_arg_program",
  "assert_bare_program", "assert_reason_program", "deploy_storage_program",
  "ec_builtins_program", "env_block_program", "env_message_core_program",
  "env_tx_chain_program", "event_log_program", "for_accum_program",
  "for_break_program", "for_continue_program", "for_pass_program",
  "function_modes_program", "hash_builtins_program", "hashmap_read_program",
  "hashmap_write_program", "if_bool_program", "if_join_program",
  "indexed_event_log_program", "internal_call_arg_program",
  "internal_call_program", "local_uint_program", "loops_program",
  "mixed_event_log_program", "noop_program", "raise_bare_program",
  "raise_reason_program", "return_arg_program", "return_uint_program",
  "scalar_arith_decimal_div_program", "scalar_arith_decimal_mul_program",
  "scalar_arith_decimal_program", "scalar_arith_decimal_sub_program",
  "scalar_arith_int_program", "scalar_arith_pow_base_program",
  "scalar_arith_pow_program", "scalar_arith_uint_program",
  "scalar_arith_unsafe_int_program", "scalar_arith_unsafe_uint_program",
  "scalar_bits_program", "scalar_compare_eq_program",
  "scalar_compare_order_int_program", "scalar_compare_order_uint_program",
  "scalar_convert_address_program",
  "scalar_convert_bytes32_to_address_program",
  "scalar_convert_bytes32_to_bytes4_program",
  "scalar_convert_bytes32_to_decimal_program",
  "scalar_convert_bytes_dynamic_program",
  "scalar_convert_bytes_fixed_program", "scalar_convert_decimal_program",
  "scalar_convert_int_to_decimal_program", "scalar_convert_integer_program",
  "scalar_convert_uint_to_bytes32_program", "scalar_decimal_bounds_program",
  "scalar_decimal_max_program", "scalar_decimal_min_program",
  "scalar_empty_program", "scalar_integer_bounds_program",
  "scalar_integer_max_int256_program", "scalar_integer_min_int256_program",
  "scalar_integer_min_uint8_program", "scalar_literal_decimal_program",
  "scalar_literals_bool_program", "scalar_literals_bytes_program",
  "scalar_literals_int_small_program", "scalar_literals_int_wide_program",
  "scalar_minmax_int_program", "scalar_minmax_uint_program",
  "scalar_modular_program", "scalar_shifts_program", "scalar_unary_program",
  "scalar_wei_large_program", "scalar_wei_small_program",
  "scalar_widths_int_high_program", "scalar_widths_int_low_program",
  "scalar_widths_uint_high_program", "scalar_widths_uint_low_program",
  "storage_array_program", "storage_dynarray_program",
  "storage_mapping_program", "storage_read_program",
  "storage_scalar_loop_program", "storage_struct_program",
  "storage_write_program", "task090_abi_dynamic_program",
  "task090_abi_static_program", "task090_external_arrays_program",
  "task090_external_dynamic_program", "task090_external_scalars_program",
  "task090_external_struct_program", "task090_interface_calls_program",
  "task090_internal_bytes_call_program",
  "task090_internal_struct_call_program",
  "task090_internal_tuple_call_program",
  "task090_mixed_event_types_program", "task090_send_value_program",
  "transient_scalar_program", "two_external_program"];

fun count p l = length (List.filter p l)

val totals = ref (0, 0, 0, 0, 0)

fun check_fixture name = let
  val prog = if name = "EMPTY" then ``[] : toplevel list``
             else Parse.Term [QUOTE name]
  val timer = Timer.startRealTimer ()
  val th = EVAL ``bo_corpus ^prog``
  val secs = Time.toReal (Timer.checkRealTimer timer)
  val rhs_tm = rhs (concl th)
  val rows =
    if optionSyntax.is_some rhs_tm then
      map pairSyntax.strip_pair
        (fst (listSyntax.dest_list (optionSyntax.dest_some rhs_tm)))
    else if optionSyntax.is_none rhs_tm then
      raise Fail (name ^ ": no compiled unit")
    else raise Fail (name ^ ": evaluation stuck")
  fun is_t tm = aconv tm boolSyntax.T
  val n = length rows
  val rw1 = count (is_t o el 1) rows
  val ok1 = count (is_t o el 2) rows
  val rw2 = count (is_t o el 3) rows
  val ok2 = count (is_t o el 4) rows
  val (a, b, c, d, e) = !totals
  val () = totals := (a + n, b + rw1, c + ok1, d + rw2, e + ok2)
  val () = print (name ^ ": functions " ^ Int.toString n ^
    ", rewritten " ^ Int.toString rw1 ^ ", accepted " ^ Int.toString ok1 ^
    "; supply variant rewritten " ^ Int.toString rw2 ^
    ", accepted " ^ Int.toString ok2 ^ " (" ^
    Real.fmt (StringCvt.FIX (SOME 1)) secs ^ " s)\n")
  val () = if ok1 = n andalso ok2 = n then ()
           else raise Fail (name ^ ": the check rejects a function")
in save_thm ((if name = "EMPTY" then "empty_program" else name) ^
               "_branch_opt_corpus", th) end;

(* Checks fixtures [from, from + n) of the list and prints their totals. *)
fun check_fixtures from n = let
  val () = totals := (0, 0, 0, 0, 0)
  val () = List.app (ignore o check_fixture)
                    (List.take (List.drop (fixtures, from), n)
                     handle Subscript => List.drop (fixtures, from))
  val (a, b, c, d, e) = !totals
in
  print ("corpus: functions " ^ Int.toString a ^ ", rewritten " ^
    Int.toString b ^ ", accepted " ^ Int.toString c ^
    "; supply variant rewritten " ^ Int.toString d ^ ", accepted " ^
    Int.toString e ^ "\n")
end

end
