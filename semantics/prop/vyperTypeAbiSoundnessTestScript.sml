(* Regression: the merged evaluator theorems, including delayed-result
   collection and forcing, are finalised and kernel-closed. *)
Theory vyperTypeAbiSoundnessTest
Ancestors
  vyperTypeEvalSoundness vyperTypeEvalStoragePreservation vyperTypeExtCallSoundness
  vyperTypeAbiTargetSoundness

val () = let
  fun check name th = let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail (name ^ " is not kernel-closed")
    end
  fun mutual count name th =
    (check name th;
     if length (boolSyntax.strip_conj (Thm.concl th)) = count then ()
     else raise Fail (name ^ " lost evaluator predicates"))
  in
    (* The full SCC includes delayed results and the two ABI evaluators;
       the public projection retains the ten original predicates. *)
    mutual 13 "eval_scc_type_sound_results_mutual" eval_scc_type_sound_results_mutual;
    mutual 13 "eval_scc_storage_preservation_results_mutual"
      eval_scc_storage_preservation_results_mutual;
    mutual 10 "eval_scc_type_sound_mutual" eval_scc_type_sound_mutual;
    mutual 10 "eval_scc_storage_preservation_mutual" eval_scc_storage_preservation_mutual;
    check "eval_expr_read_type_sound" eval_expr_read_type_sound;
    check "target_place_pop_sound" target_place_pop_sound;
    check "abi_target_operand_pop_sound" abi_target_operand_pop_sound;
    check "eval_ext_call_result_sound" eval_ext_call_result_sound;
    check "eval_send_result_sound" eval_send_result_sound;
    print "ABI_MAIN_SOUNDNESS_KERNEL_CLOSED\n"
  end;
