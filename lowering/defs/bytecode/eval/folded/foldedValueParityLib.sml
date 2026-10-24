(* Shared bounded compiler evaluation; every pass guard remains checked.
   Oracle bytes remain data and are never installed as computation rules. *)
structure foldedValueParityLib = struct
open HolKernel Parse boolLib bossLib
open venomFnScheduleRunnerTheory

(* Reuse the theory's rules instead of taking a context snapshot per call. *)
val cached_compset = ref computeLib.bool_compset;
fun refresh_compset () = cached_compset := computeLib.the_compset ();
fun eval tm = computeLib.CBV_CONV (!cached_compset) tm;
fun restricted_eval stops = Lib.with_flag (computeLib.stoppers,
  SOME (fn c => List.exists (same_const c) stops)) eval;

fun setup () = (
  computeLib.upd_compset finite_mapLib.add_finite_map_compset;
  computeLib.upd_compset (computeLib.add_thms
    [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos,
     foldedValueParityComputeTheory.parity_uint_selector,
     foldedValueParityComputeTheory.parity_nullary_selector,
     foldedValueParityComputeTheory.parity_cube_base_bound]);
  refresh_compset ());

fun input root name = memoryStoreWitnessLib.program root name;
fun expected root name = memoryStoreWitnessLib.oracle root name;

(* Convert one exposed call. Deferred continuation lambdas are visited only
   after their input is available and beta reduction exposes their body. *)
fun locate predicate root = let
  fun seek path tm =
    if predicate tm then SOME (String.implode (rev path), tm)
    else if is_comb tm then let val (func, arg) = dest_comb tm in
      case seek (#"r" :: path) arg of
        SOME found => SOME found
      | NONE => seek (#"l" :: path) func
    end
    else NONE
in case seek [] root of
     SOME found => found
   | NONE => raise mk_HOL_ERR "foldedValueParityLib" "locate" "no matching call"
end;
fun has_term predicate tm = can (locate predicate) tm;
fun at_conv predicate conversion tm =
  PATH_CONV (#1 (locate predicate tm)) (CHANGED_CONV conversion) tm;
fun call_conv c conversion = let
  fun arity ty = case total dom_rng ty of
    NONE => 0 | SOME (_, result) => 1 + arity result
  val nargs = arity (type_of c)
  fun matches tm = same_const c (#1 (strip_comb tm)) andalso
    length (#2 (strip_comb tm)) = nargs andalso null (free_vars tm)
in at_conv matches conversion end;
fun eval_call c = CONV_TAC (call_conv c eval);

val PARITY_NORMALIZE_TAC = computeLib.RESTR_EVAL_TAC
  [``run_configured_fn_pass_fold``, ``codegen_ready``, ``finalize_codegen``,
   ``lower_vyper_deploy_unit``];
val pass_fold_head = ``run_configured_fn_pass_fold``;
fun parity_pass_call tm =
  same_const pass_fold_head (#1 (strip_comb tm)) andalso
  length (#2 (strip_comb tm)) = 7 andalso null (free_vars tm);
val parity_pass_conv =
  FIRST_CONV (map REWR_CONV (CONJUNCTS run_configured_fn_pass_fold_def)) THENC
  restricted_eval [``run_configured_fn_pass_fold``];
fun PARITY_PASS_TAC (g as (_, w)) = let
  val (path, call) = locate parity_pass_call w
  val at_end = listSyntax.is_nil (List.nth (#2 (strip_comb call), 2))
  val step = CONV_TAC (PATH_CONV path (CHANGED_CONV parity_pass_conv))
in (step >> (if at_end then PARITY_NORMALIZE_TAC else ALL_TAC)) g end;

val PARITY_OPEN_PASS_TAC = CONV_TAC (at_conv parity_pass_call
  (FIRST_CONV (map REWR_CONV (CONJUNCTS run_configured_fn_pass_fold_def)) THENC
   restricted_eval
     [``run_configured_fn_pass_fold``, ``execute_configured_fn_pass``,
      ``fn_pass_effects_hold``, ``introduces_no_invoke_edges``,
      ``ir_supply_extends``, ``ir_supply_covers_fn``, ``ir_supply_covers_unit``]));


fun audit theory = app (fn (name, th) =>
  if null (List.filter (fn oracle => oracle <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("unexpected theorem oracle: " ^ name)) (DB.thms theory);
end
