(*
 * Analysis Cache (minimal shared cache)
 *
 * Shared cache helpers for reusable analyses.
 *)

Theory analysisCache
Ancestors
  dfgAnalysis

Datatype:
  analysis_cache = <|
    ac_function : ir_function;
    ac_dfg : dfg_analysis option
  |>
End

Definition analysis_cache_init_def:
  analysis_cache_init fn =
    <| ac_function := fn; ac_dfg := NONE |>
End

Definition analysis_cache_set_function_def:
  analysis_cache_set_function cache fn =
    cache with <| ac_function := fn; ac_dfg := NONE |>
End

Definition analysis_cache_request_dfg_def:
  analysis_cache_request_dfg cache =
    case cache.ac_dfg of
      SOME dfg => (dfg, cache)
    | NONE =>
        let dfg = dfg_build_function cache.ac_function in
          (dfg, cache with ac_dfg := SOME dfg)
End

Definition analysis_cache_invalidate_dfg_def:
  analysis_cache_invalidate_dfg cache = cache with ac_dfg := NONE
End

(* ===== Force Helpers ===== *)

Definition analysis_cache_force_dfg_def:
  analysis_cache_force_dfg cache =
    analysis_cache_request_dfg (analysis_cache_invalidate_dfg cache)
End

val _ = export_theory();
