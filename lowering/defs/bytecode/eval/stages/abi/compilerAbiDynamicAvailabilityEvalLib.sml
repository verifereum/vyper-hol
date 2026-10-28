(* Exact availability predicates on the shared dynamic-ABI analysis. *)
structure compilerAbiDynamicAvailabilityEvalLib = struct
open HolKernel boolLib bossLib
open evalCompilerBytecodeAbiDynamicAnalysisTheory

val abi_dynamic_ready_named_available_terms = #1
  (listSyntax.dest_list (rhs (concl abi_dynamic_available_queries_def)))
val () = if length abi_dynamic_ready_named_available_terms = 495 then ()
  else raise Fail "expected all 495 actual named availability calls"

fun abi_dynamic_take_chunk _ [] = ([],[])
  | abi_dynamic_take_chunk 0 xs = ([],xs)
  | abi_dynamic_take_chunk n (x::xs) = let
      val (front,rest) = abi_dynamic_take_chunk (n - 1) xs
    in (x::front,rest) end
(* Each conjunction is a useful, kernel-checked stage: all concrete use
   sites in this slice have an available definition.  Unlike the former
   top-level map EVAL, these computations are timed and independently
   checkpointed by holbuild. *)
fun abi_dynamic_available_slice n =
  list_mk_conj (#1 (abi_dynamic_take_chunk 40
    (List.drop (abi_dynamic_ready_named_available_terms, 40 * n))))

(* Check one use site per bounded tactic, retaining the complete slice. *)
fun abi_dynamic_available_check goal =
  (PURE_REWRITE_TAC
    ([abi_dynamic_available_cfg_def,abi_dynamic_available_dom_def,
      abi_dynamic_available_function_def] @
     CONJUNCTS abi_dynamic_available_block_evals) >> EVAL_TAC) goal
fun abi_dynamic_available_step goal =
  (conj_tac >- abi_dynamic_available_check) goal


end
