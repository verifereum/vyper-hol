(* Pinned Python bytecode witnesses and adversarial stack-checker cases. *)
Theory stackBoundWitnesses
Ancestors
  stackBoundCompute stackBoundDefs list words
Libs
  cv_transLib wordsLib evalCompilerBytecodeLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["stack-bound", "internal-frames/oracle/p09_int_chain.hex"];

fun define_bytes name bytes = let
  val def = new_definition (name ^ "_def",
    mk_eq (mk_var (name, type_of bytes), bytes))
  val _ = cv_auto_trans def
in lhs (concl def) end;

fun byte_chunks [] = []
  | byte_chunks bytes = let
      val n = Int.min (128, length bytes)
    in List.take (bytes, n) :: byte_chunks (List.drop (bytes, n)) end;

(* Bound the size of each translation proof for large bytecode constants. *)
fun define_runtime name path = let
  val bytes = pairSyntax.dest_pair
    (evalCompilerBytecodeLib.read_hex_bytes_from path) |> #2
  val (elements, byte_type) = listSyntax.dest_list bytes
  val parts = mapi (fn i => fn part =>
    define_bytes (name ^ "_bytes_" ^ Int.toString i)
      (listSyntax.mk_list (part, byte_type))) (byte_chunks elements)
  val nested = listSyntax.mk_list (parts, type_of bytes)
in define_bytes name ``FLAT ^nested`` end;

val _ = define_runtime "checked_internal_chain"
  "internal-frames/oracle/p09_int_chain.hex";
val _ = define_runtime "checked_deep_chain" "stack-bound/deep_chain.hex";

Theorem internal_chain_stack_check_passes:
  bytecode_stack_check 1000 1024 checked_internal_chain
Proof
  CONV_TAC cv_eval
QED

Theorem deep_chain_stack_check_rejects_1024:
  ~bytecode_stack_check 100000 1024 checked_deep_chain
Proof
  CONV_TAC cv_eval
QED

(* A larger limit passes with the same fuel, excluding exhaustion as the
   reason for the 1024 rejection. This is a checker witness, not an EVM limit. *)
Theorem deep_chain_stack_check_passes_2048:
  bytecode_stack_check 100000 2048 checked_deep_chain
Proof
  CONV_TAC cv_eval
QED

Theorem stack_check_fuel_exhaustion_rejects:
  ~bytecode_stack_check 0 1024 [0x00w]
Proof
  CONV_TAC cv_eval
QED

Theorem stack_check_unknown_jump_finds_overflow:
  ~bytecode_stack_check 100 1 [0x5Fw; 0x35w; 0x56w; 0x5Bw; 0x5Fw; 0x5Fw]
Proof
  CONV_TAC cv_eval
QED

Theorem stack_check_push_data_is_not_jumpdest:
  bytecode_stack_check 100 1 [0x60w; 0x5Bw; 0x56w; 0x5Fw; 0x5Fw]
Proof
  CONV_TAC cv_eval
QED
