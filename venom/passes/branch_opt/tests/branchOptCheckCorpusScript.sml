(* The branch_opt checker on compiled code: each sampled parity fixture
   program is lowered to its runtime unit and run through the O1 pipeline,
   and on every function of the result branch_opt runs (both variants, with
   Python's liveness heuristic) and the checker judges the output. HOL has no
   O2 pipeline, so the pass sees post-O1 functions.

   This checks a fast sample of the fixtures: a branch (if_bool), an
   internal call whose callee has no iszero-fed jnz (internal_call), and a
   straight-line function (return_uint). branch_opt rewrites the external
   entry of each. The full set of fixtures is too slow to check on every
   build. *)
Theory branchOptCheckCorpus
Ancestors
  compileVyper evalCompiler evalCompilerSubsetAbiBuiltins
  evalCompilerSubsetAbiEvents evalCompilerSubsetAbiExternalCalls
  evalCompilerSubsetAbiExternal evalCompilerSubsetAbiInternalCalls
  evalCompilerSubsetBuiltins evalCompilerSubsetControlDeploy
  evalCompilerSubsetScalars evalCompilerSubsetState codegenReadyCompute
  branchOptDefs branchOptCheck livenessDefs irSupply alist integer_word
Libs
  wordsLib finite_mapLib
(* The runtime unit after the O1 pipeline, as compile_vyper builds it. *)
Definition bo_corpus_unit_def:
  bo_corpus_unit tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            case run_venom_pipeline (K T) (K T) (K T) rpolicy
                   o1_pipeline_spec unit of
              NONE => NONE
            | SOME out => SOME out.po_unit
End

(* Per function: did each variant rewrite it, and does the check accept the
   result. live_at is the size of the live set at a block's entry, as in
   Python's heuristic. *)
Definition bo_corpus_fn_def:
  bo_corpus_fn s0 fn =
    let lv = liveness_analyze fn in
    let live = (\l. LENGTH (live_vars_at lv l 0)) in
    let fn1 = branch_opt_function live fn in
    let fn2 = FST (branch_opt_function_supply live s0 fn) in
      (fn1.fn_blocks <> fn.fn_blocks, check_branch_opt_fn fn fn1,
       fn2.fn_blocks <> fn.fn_blocks, check_branch_opt_fn fn fn2)
End

Definition bo_corpus_def:
  bo_corpus tops =
    case bo_corpus_unit tops of
      NONE => NONE
    | SOME unit =>
        SOME (MAP (bo_corpus_fn (init_ir_supply unit))
                  unit.cu_context.ctx_functions)
End

(* ===== Running the check on the sample ===== *)

(* Loading wordsLib adds its word conversions to the compset; without them
   EVAL unfolds word arithmetic through its definitions and blows up. *)
val _ = wordsLib.WORD_ss

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
           (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
           (computeLib.add_thms [integer_wordTheory.i2w_pos])

val fixtures = ["if_bool_program", "internal_call_program", "return_uint_program"];

fun count p l = length (List.filter p l)

val totals = ref (0, 0, 0, 0, 0)

fun check_fixture name = let
  val prog = Parse.Term [QUOTE name]
  val timer = Timer.startRealTimer ()
  val th = EVAL ``bo_corpus ^prog``
  val secs = Time.toReal (Timer.checkRealTimer timer)
  val rhs_tm = rhs (concl th)
  val rows =
    if optionSyntax.is_some rhs_tm then
      map pairSyntax.strip_pair
        (fst (listSyntax.dest_list (optionSyntax.dest_some rhs_tm)))
    else if optionSyntax.is_none rhs_tm then
      raise Fail (name ^ ": no compiled unit")
    else raise Fail (name ^ ": evaluation stuck")
  fun is_t tm = aconv tm boolSyntax.T
  val n = length rows
  val rw1 = count (is_t o el 1) rows
  val ok1 = count (is_t o el 2) rows
  val rw2 = count (is_t o el 3) rows
  val ok2 = count (is_t o el 4) rows
  val (a, b, c, d, e) = !totals
  val () = totals := (a + n, b + rw1, c + ok1, d + rw2, e + ok2)
  val () = print (name ^ ": functions " ^ Int.toString n ^
    ", rewritten " ^ Int.toString rw1 ^ ", accepted " ^ Int.toString ok1 ^
    "; supply variant rewritten " ^ Int.toString rw2 ^
    ", accepted " ^ Int.toString ok2 ^ " (" ^
    Real.fmt (StringCvt.FIX (SOME 1)) secs ^ " s)\n")
  val () = if ok1 = n andalso ok2 = n then ()
           else raise Fail (name ^ ": the check rejects a function")
in save_thm (name ^ "_branch_opt_corpus", th) end;

val () = List.app (ignore o check_fixture) fixtures;

val () = let val (a, b, c, d, e) = !totals in
  print ("corpus: functions " ^ Int.toString a ^ ", rewritten " ^
    Int.toString b ^ ", accepted " ^ Int.toString c ^
    "; supply variant rewritten " ^ Int.toString d ^ ", accepted " ^
    Int.toString e ^ "\n")
end;
