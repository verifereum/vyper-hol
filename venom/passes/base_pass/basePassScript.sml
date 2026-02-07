(*
 * Base Pass Definitions
 *
 * Port of venom/passes/base_pass.py.
 *)

Theory basePass
Ancestors
  list
  venomInst
  analysisCache
  instUpdater

Type analysis_cache_map = ``:(string # analysis_cache) list``

Datatype:
  ir_pass_state = <|
    ip_function : ir_function;
    ip_cache : analysis_cache;
    ip_updater : inst_updater option
  |>
End

Datatype:
  ir_global_pass_state = <|
    ig_ctx : ir_context;
    ig_caches : analysis_cache_map
  |>
End

val _ = export_theory();
