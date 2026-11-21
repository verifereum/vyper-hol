structure vyperConstEvalLib :> vyperConstEvalLib = struct

open HolKernel boolLib vyperConstEvalTheory vyperPinFoldTheory vyperOriginFoldTheory

(* EVAL computes eval_constant of a closed expression with cv_eval.
   eval_constant has no rewrites in EVAL (it is defined [nocompute]), so
   every definition that calls it, loaded before or after this library, uses
   this conversion. Frontend constants also need integer arithmetic, and
   cv_eval of byte literals needs wordsLib. *)
val eval_constant_tm =
  prim_mk_const {Thy = "vyperConstEval", Name = "eval_constant"}

(* cv_compute's compiled code, by the constants of the cv term it runs on:
   the code equations cv_eqs_for collects depend only on those, and the
   compiled conversion is pure, so one compilation serves every expression
   with the same constants. A contract's constants share a handful of sets,
   and compiling is most of a cv_eval call. *)
val compiled =
  ref (Redblackmap.mkDict (Lib.list_compare Term.compare)
       : (term list, conv) Redblackmap.dict)

fun consts_of tm = let
  fun go (tm, acc) =
    if is_const tm then HOLset.add (acc, tm)
    else if is_comb tm then go (rand tm, go (rator tm, acc))
    else if is_abs tm then go (body tm, acc)
    else acc
  in HOLset.listItems (go (tm, empty_tmset)) end

fun cv_compute_conv cv_tm = let
  val key = consts_of cv_tm
  in
    case Redblackmap.peek (!compiled, key) of
      SOME conv => conv
    | NONE => let
        val conv = cv_computeLib.cv_compute (cv_transLib.cv_eqs_for cv_tm)
        in compiled := Redblackmap.insert (!compiled, key, conv); conv end
  end

fun remove_T_IMP th = MP th TRUTH handle HOL_ERR _ => th

(* cv_transLib.cv_eval's steps, with the compiled code cached. *)
fun eval_constant_conv tm =
  if not (null (free_vars tm)) then
    raise mk_HOL_ERR "vyperConstEvalLib" "eval_constant_conv" "open term"
  else let
    val th = cv_repLib.cv_rep_for [] tm
    val from_to_thm = cv_typeLib.from_to_thm_for (type_of tm)
    val conv = cv_compute_conv (cv_miscLib.cv_rep_cv_tm (concl th))
    val cv_th =
      MATCH_MP (MATCH_MP cv_repTheory.cv_rep_eval th) from_to_thm
      |> UNDISCH_ALL
      |> CONV_RULE (RAND_CONV (RAND_CONV conv))
      |> DISCH_ALL |> remove_T_IMP
    in
      cv_th |> UNDISCH_ALL |> CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
      |> DISCH_ALL |> remove_T_IMP
    end

val () = computeLib.add_convs [(eval_constant_tm, 1, eval_constant_conv)]
val pin_fold_expr_tm =
  prim_mk_const {Thy = "vyperPinFold", Name = "pin_fold_expr"}
val () = computeLib.add_convs [(pin_fold_expr_tm, 1, eval_constant_conv)]
val origin_fold_value_tm =
  prim_mk_const {Thy = "vyperOriginFold", Name = "origin_fold_value"}
val () = computeLib.add_convs [(origin_fold_value_tm, 1, eval_constant_conv)]
local open intReduce wordsLib in end

end
