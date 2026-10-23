(* Standalone bounded selector computation checkpoint. *)
Theory nestedPlaceSelectorTest
Ancestors compileVyper selectorDispatch
Libs supportedEvalLib cv_transLib

Theorem wei_value_function_selector:
  function_selector "wei_value" [Uint 256] = [27w; 46w; 27w; 155w]
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

Theorem wei_value_compute_selector:
  compute_selector FEMPTY "wei_value" [BaseT (UintT 256)] = (456006555, "fn_wei_value", F)
Proof
  simp[compute_selector_def, wei_value_function_selector] >> EVAL_TAC
QED

(* Exercise the public checked interface as well as the direct CV probe above. *)
Theorem wei_value_checked_selector:
  function_selector "wei_value" [Uint 256] = [27w; 46w; 27w; 155w]
Proof
  CONV_TAC (LAND_CONV supportedEvalLib.function_selector_conv) >> REFL_TAC
QED

val () = List.app (fn name =>
  let val th = DB.fetch "nestedPlaceSelectorTest" name
      val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles
    then print ("Kernel-closed selector checkpoint: " ^ name ^ "\n")
    else raise Fail ("Untrusted selector checkpoint: " ^ name)
  end) ["wei_value_function_selector", "wei_value_compute_selector",
        "wei_value_checked_selector"];

(* Imported CV bridge inspection: selector encoding and its Keccak backend. *)
val () = List.app (fn (thy,name) =>
  (print (thy ^ "." ^ name ^ "\n"); print (thm_to_string (DB.fetch thy name) ^ "\n")))
  [("contractABI", "cv_function_selector_thm"),
   ("contractABI", "cv_function_selector_def"),
   ("keccak", "cv_Keccak_256_w64_thm")];
