structure vyperConstEvalLib :> vyperConstEvalLib = struct

open HolKernel boolLib vyperConstEvalTheory

(* EVAL computes eval_constant of a closed expression with cv_eval.
   eval_constant has no rewrites in EVAL (it is defined [nocompute]), so
   every definition that calls it, loaded before or after this library, uses
   this conversion. Frontend constants also need integer arithmetic, and
   cv_eval of byte literals needs wordsLib. *)
val eval_constant_tm =
  prim_mk_const {Thy = "vyperConstEval", Name = "eval_constant"}

fun eval_constant_conv tm =
  if null (free_vars tm) then cv_transLib.cv_eval tm
  else raise mk_HOL_ERR "vyperConstEvalLib" "eval_constant_conv" "open term"

val () = computeLib.add_convs [(eval_constant_tm, 1, eval_constant_conv)]
local open intReduce wordsLib in end

end
