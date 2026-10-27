(* Reload only this CV repair's exports and regression objects. *)
Theory vyperExtCallCpsCVKernelCheck
Ancestors
  vyperExtCallCpsCVTest vyperExtCallCpsEquivalenceTest

fun check_saved (thy,n) = let
  val th = DB.fetch thy n
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val _ = if null (Thm.hyp th) andalso null axioms andalso
      List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail (thy ^ "." ^ n ^ ": not kernel-closed/unadmitted")
  in print ("TASK032_CV_KERNEL_CLOSED " ^ thy ^ "." ^ n ^
    " hyp=0 axioms=[] oracles=[" ^ String.concatWith "," oracles ^ "]\n") end;

val () = List.app check_saved
  [("vyperSmallStep", "cont_pre_eval_expr_cps"),
   ("vyperSmallStep", "cv_cont_def"),
   ("vyperSmallStep", "cv_cont_thm"),
   ("vyperSmallStep", "cv_eval_expr_cps_thm"),
   ("vyperSmallStep", "cv_fromtvk_thm"),
   ("vyperSmallStep", "eval_cps_eq")];

val () = List.app (fn (thy,n) => print
  ("TASK032_CV_TRANSLATION " ^ thy ^ "." ^ n ^ "\n" ^
    term_to_string (Thm.concl (DB.fetch thy n)) ^ "\n"))
  [("vyperSmallStep", "cont_pre_eval_expr_cps"),
   ("vyperSmallStep", "cv_cont_thm"),
   ("vyperExtCallCpsCVTest", "cv_cpscv_run_thm")];

val () = List.app (fn thy => List.app
  (fn (n,_) => check_saved (thy,n)) (DB.thms thy))
  ["vyperExtCallCpsCVTest", "vyperExtCallCpsEquivalenceTest"];
