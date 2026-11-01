(* Reload only TASK015's changed exports and focused regression objects. *)
Theory vyperDecimalMulAudit
Ancestors
  vyperValueOperation vyperTypeBuiltins vyperTypeStatePreservation vyperDecimalMulTest
  vyperAugAssignWriteSoundness

fun check_saved (thy, name) =
  let
    val th = DB.fetch thy name
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val hyps = Thm.hyp th
    val _ = print ("TASK015 TAG " ^ thy ^ "." ^ name ^ " Hyp=" ^
      Int.toString (length hyps) ^ " axioms=[" ^ String.concatWith "," axioms ^
      "] oracles=[" ^ String.concatWith "," oracles ^ "]\n")
    val _ = if null hyps andalso null axioms andalso
               List.all (fn s => s = "DISK_THM") oracles then ()
            else raise Fail ("TASK015 unclosed/admitted object: " ^ thy ^ "." ^ name)
  in
    print ("TASK015 OBJECT " ^ thy ^ "." ^ name ^
           " Hyp=0 axioms=[] admissions=[] (DISK_THM bookkeeping only)\nSTATEMENT " ^
           term_to_string (Thm.concl th) ^ "\n")
  end;

val () = List.app check_saved
  [("vyperValueOperation", "evaluate_binop_def"),
   ("vyperValueOperation", "evaluate_binop_ind"),
   ("vyperValueOperation", "cv_evaluate_binop_def"),
   ("vyperValueOperation", "cv_evaluate_binop_ind"),
   ("vyperValueOperation", "cv_evaluate_binop_thm"),
   ("vyperTypeBuiltins", "well_typed_binop_no_type_error"),
   ("vyperTypeBuiltins", "well_typed_binop_success_type"),
   ("vyperTypeBuiltins", "well_typed_builtin_app_no_type_error"),
   ("vyperTypeBuiltins", "well_typed_builtin_app_success_type"),
   ("vyperAugAssignWriteSoundness", "update_place_tail_sound"),
   ("vyperTypeStatePreservation", "well_typed_update_binop_no_type_error")];
val () = List.app (fn (name, _) => check_saved ("vyperDecimalMulTest", name))
                 (DB.thms "vyperDecimalMulTest");
