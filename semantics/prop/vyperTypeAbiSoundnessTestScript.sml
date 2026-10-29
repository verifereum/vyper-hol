(* Regression: the unrestricted evaluator theorems are finalised and closed. *)
Theory vyperTypeAbiSoundnessTest
Ancestors
  vyperTypeEvalSoundness vyperTypeEvalStoragePreservation vyperTypeExtCallSoundness

val () = let
  fun check name th = let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail (name ^ " is not kernel-closed")
    end
  fun mutual name th =
    (check name th;
     if length (boolSyntax.strip_conj (Thm.concl th)) = 11 then ()
     else raise Fail (name ^ " must retain all eleven evaluator predicates"))
  in
    mutual "eval_all_type_sound_mutual" eval_all_type_sound_mutual;
    mutual "eval_all_storage_preservation_mutual" eval_all_storage_preservation_mutual;
    check "eval_ext_call_result_sound" eval_ext_call_result_sound;
    check "eval_send_result_sound" eval_send_result_sound;
    print "ABI_MAIN_SOUNDNESS_KERNEL_CLOSED\n"
  end;
