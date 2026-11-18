(* Kernel-checked compiler parity for the assignment-order source fixtures. *)
structure assignmentOrderWitnessLib = struct
open HolKernel Parse boolLib bossLib
open compileVyperTheory supportedProgramTheory

(* Configure the caller's computation set after its ancestors have loaded. *)
fun prepare () =
  (computeLib.upd_compset finite_mapLib.add_finite_map_compset;
   computeLib.upd_compset (computeLib.add_thms
     [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]));

fun check_compiler_fixture name = let
  val () = prepare ()
  val program = prim_mk_const
    {Thy = "evalAssignmentOrder", Name = name ^ "_source_program"}
  val expected = evalCompilerBytecodeLib.read_hex_bytes_from
    ("../assignment-order/oracle/" ^ name ^ ".hex")
  val _ = save_thm (name ^ "_supported",
    EQT_ELIM (EVAL ``supported_program ^program``))
  val _ = save_thm (name ^ "_matches_python", EQT_ELIM (EVAL
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program = SOME ^expected``))
in () end;

fun check_decoder_divergence_fixture name = let
  val () = prepare ()
  val program = prim_mk_const
    {Thy = "evalAssignmentOrder", Name = name ^ "_source_program"}
  val expected = evalCompilerBytecodeLib.read_hex_bytes_from
    ("../assignment-order/oracle/" ^ name ^ ".hex")
  val compiled = EVAL
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program``
  fun on_compiled tm =
    EQT_ELIM ((DEPTH_CONV (REWR_CONV compiled) THENC EVAL) tm)
  val _ = save_thm (name ^ "_supported",
    EQT_ELIM (EVAL ``supported_program ^program``))
  val _ = save_thm (name ^ "_compiles", on_compiled
    ``IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities) ^program)``)
  val _ = save_thm (name ^ "_differs_from_pinned_decoder", on_compiled
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program <> SOME ^expected``)
in () end;
end
