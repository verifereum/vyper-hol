(*
 * Analysis Cache (minimal shared cache)
 *
 * Shared cache helpers for reusable analyses in this branch.
 *)

Theory analysisCache
Ancestors
  dfgAnalysis livenessAnalysis rangeAnalysis

Datatype:
  analysis_cache = <|
    ac_function : ir_function;
    ac_dfg : dfg_analysis option;
    ac_liveness : liveness_analysis option;
    ac_ranges : (((num # operand) # value_range) list) option
  |>
End

Definition analysis_cache_init_def:
  analysis_cache_init fn =
    <| ac_function := fn; ac_dfg := NONE; ac_liveness := NONE; ac_ranges := NONE |>
End

Definition analysis_cache_set_function_def:
  analysis_cache_set_function cache fn =
    cache with <| ac_function := fn; ac_dfg := NONE; ac_liveness := NONE; ac_ranges := NONE |>
End

Definition analysis_cache_request_dfg_def:
  analysis_cache_request_dfg cache =
    case cache.ac_dfg of
      SOME dfg => (dfg, cache)
    | NONE =>
        let dfg = dfg_build_function cache.ac_function in
          (dfg, cache with ac_dfg := SOME dfg)
End

Definition analysis_cache_request_liveness_def:
  analysis_cache_request_liveness cache =
    case cache.ac_liveness of
      SOME live => (live, cache)
    | NONE =>
        let live = liveness_analyze cache.ac_function in
          (live, cache with ac_liveness := SOME live)
End

Definition analysis_cache_request_ranges_def:
  analysis_cache_request_ranges cache =
    case cache.ac_ranges of
      SOME ranges => (ranges, cache)
    | NONE =>
        let ranges = range_analyze cache.ac_function in
          (ranges, cache with ac_ranges := SOME ranges)
End

Definition analysis_cache_invalidate_dfg_def:
  analysis_cache_invalidate_dfg cache = cache with ac_dfg := NONE
End

Definition analysis_cache_invalidate_liveness_def:
  analysis_cache_invalidate_liveness cache = cache with ac_liveness := NONE
End

Definition analysis_cache_invalidate_ranges_def:
  analysis_cache_invalidate_ranges cache = cache with ac_ranges := NONE
End

val _ = export_theory();
