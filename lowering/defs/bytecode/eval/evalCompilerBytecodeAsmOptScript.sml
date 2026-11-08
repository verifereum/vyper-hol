(*
 * Exact Python-oracle bytecode checks with the final assembly optimizer on:
 * HOL's compile_vyper with asm_opt_finalizer against Python's O1 output.
 *
 * Every rule fires on at least one of these fixtures. The rule branches no
 * fixture reaches are checked on hand-written lists at the end.
 *)

Theory evalCompilerBytecodeAsmOpt
Ancestors evalCompiler evalCompilerSubsetControlDeploy evalCompilerSubsetBuiltins compileVyper concretizeMemLocDefs asmOptimizer alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

(* Whole-compile evaluation runs outside a proof step, which the step timeout
   would stop; each parity theorem then only compares literals. *)
val noop_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           noop_program``

Theorem noop_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    noop_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "noop.hex")
Proof
  PURE_REWRITE_TAC [noop_asm_opt_eval] >> EVAL_TAC
QED

val return_uint_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           return_uint_program``

Theorem return_uint_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    return_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "return_uint.hex")
Proof
  PURE_REWRITE_TAC [return_uint_asm_opt_eval] >> EVAL_TAC
QED

val deploy_storage_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           deploy_storage_program``

Theorem deploy_storage_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    deploy_storage_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "deploy_storage.hex")
Proof
  PURE_REWRITE_TAC [deploy_storage_asm_opt_eval] >> EVAL_TAC
QED

val internal_call_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           internal_call_program``

Theorem internal_call_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    internal_call_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "internal_call.hex")
Proof
  PURE_REWRITE_TAC [internal_call_asm_opt_eval] >> EVAL_TAC
QED

val raise_bare_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           raise_bare_program``

Theorem raise_bare_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    raise_bare_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "raise_bare.hex")
Proof
  PURE_REWRITE_TAC [raise_bare_asm_opt_eval] >> EVAL_TAC
QED

val assert_bare_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           assert_bare_program``

Theorem assert_bare_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    assert_bare_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "assert_bare.hex")
Proof
  PURE_REWRITE_TAC [assert_bare_asm_opt_eval] >> EVAL_TAC
QED

val if_bool_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           if_bool_program``

Theorem if_bool_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    if_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "if_bool.hex")
Proof
  PURE_REWRITE_TAC [if_bool_asm_opt_eval] >> EVAL_TAC
QED

val if_join_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           if_join_program``

Theorem if_join_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    if_join_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "if_join.hex")
Proof
  PURE_REWRITE_TAC [if_join_asm_opt_eval] >> EVAL_TAC
QED

val hashmap_write_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           hashmap_write_program``

Theorem hashmap_write_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    hashmap_write_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "hashmap_write.hex")
Proof
  PURE_REWRITE_TAC [hashmap_write_asm_opt_eval] >> EVAL_TAC
QED

val for_pass_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           for_pass_program``

Theorem for_pass_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    for_pass_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "for_pass.hex")
Proof
  PURE_REWRITE_TAC [for_pass_asm_opt_eval] >> EVAL_TAC
QED

val for_accum_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           for_accum_program``

Theorem for_accum_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    for_accum_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "for_accum.hex")
Proof
  PURE_REWRITE_TAC [for_accum_asm_opt_eval] >> EVAL_TAC
QED

val for_break_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           for_break_program``

Theorem for_break_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    for_break_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "for_break.hex")
Proof
  PURE_REWRITE_TAC [for_break_asm_opt_eval] >> EVAL_TAC
QED

val for_continue_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           for_continue_program``

Theorem for_continue_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    for_continue_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "for_continue.hex")
Proof
  PURE_REWRITE_TAC [for_continue_asm_opt_eval] >> EVAL_TAC
QED

val env_message_core_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           env_message_core_program``

Theorem env_message_core_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    env_message_core_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "env_message_core.hex")
Proof
  PURE_REWRITE_TAC [env_message_core_asm_opt_eval] >> EVAL_TAC
QED

val hash_builtins_asm_opt_eval =
  EVAL ``compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
           hash_builtins_program``

Theorem hash_builtins_matches_python_asm_opt_oracle:
  compile_vyper asm_opt_finalizer (o1_policy all_capabilities)
    hash_builtins_program =
    SOME ^(evalCompilerBytecodeLib.read_asm_opt_hex_bytes "hash_builtins.hex")
Proof
  PURE_REWRITE_TAC [hash_builtins_asm_opt_eval] >> EVAL_TAC
QED

(* Rule branches that no fixture reaches, compared with the pinned Python
   function on the same list: the stack peepholes other than SWAPn SWAPn and
   SWAP1 <commutative>, the fall-through after a SWAPn SWAPn deletion, the
   ends of the list where Python raises IndexError (NONE here), and
   _merge_jumpdests' LABEL x LABEL y case. *)

Theorem asm_opt_peephole_dup1_swap2_swap1:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "SWAP1"; AsmOp "DUP2"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_dup1_swap1_pop:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"; AsmOp "STOP"; AsmOp "CALLER"] =
    SOME ([AsmOp "STOP"; AsmOp "CALLER"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_pop_pop:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"; AsmOp "STOP"] =
    SOME ([AsmOp "POP"; AsmOp "POP"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_commutative:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"; AsmOp "ADD"; AsmOp "STOP"] =
    SOME ([AsmOp "ADD"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_dup1_swap1:
  stack_peephole_opts
    [AsmOp "SWAP3"; AsmOp "SWAP3"; AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "DUP1"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_dup1_swap1:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "DUP1"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_commutative:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "MUL"; AsmOp "STOP"] =
    SOME ([AsmOp "MUL"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_lowercase_commutative:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "add"; AsmOp "STOP"] =
    SOME ([AsmOp "add"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_swap1_at_end:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"] =
    NONE
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_dup1_at_end:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "DUP1"] =
    NONE
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_no_match:
  stack_peephole_opts
    [AsmOp "CALLER"; AsmOp "SWAP1"; AsmOp "SUB"; AsmOp "STOP"] =
    SOME ([AsmOp "CALLER"; AsmOp "SWAP1"; AsmOp "SUB"; AsmOp "STOP"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_label:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "b"; AsmPushLabel "a"; AsmOp "JUMP"] =
    ([AsmLabel "a"; AsmLabel "b"; AsmPushLabel "b"; AsmOp "JUMP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_same_label:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "a"; AsmPushLabel "a"; AsmOp "JUMPI"] =
    ([AsmLabel "a"; AsmLabel "a"; AsmPushLabel "a"; AsmOp "JUMPI"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_label_unused:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"] =
    ([AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_renames_earlier_push:
  merge_jumpdests
    [AsmPushLabel "a"; AsmOp "JUMP"; AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"] =
    ([AsmPushLabel "b"; AsmOp "JUMP"; AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_jump:
  merge_jumpdests
    [AsmLabel "a"; AsmPushLabel "b"; AsmOp "JUMP"; AsmPushLabel "a"; AsmOp "JUMPI"] =
    ([AsmLabel "a"; AsmPushLabel "b"; AsmOp "JUMP"; AsmPushLabel "b"; AsmOp "JUMPI"], T)
Proof
  EVAL_TAC
QED
