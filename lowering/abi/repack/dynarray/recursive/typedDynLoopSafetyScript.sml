(* Compatibility export: checked element strides and physical bounds are
   shared by fixed-array and dynamic-array loops. *)
Theory typedDynLoopSafety
Ancestors
  typedArrayLoopSafety

Theorem checked_dynarray_copy_element_safety = typedArrayLoopSafetyTheory.checked_array_copy_element_safety;

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked recursive array-copy safety: " ^ name)
  end) (DB.thms "typedDynLoopSafety")
