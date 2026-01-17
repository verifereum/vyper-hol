(*
 * Venom Optimization Flags
 *
 * Port of vyper/compiler/settings.py VenomOptimizationFlags.
 *)

Theory optimizationFlags
Ancestors
  list

Datatype:
  optimization_level =
    | OPT_NONE
    | OPT_GAS
    | OPT_CODESIZE
    | OPT_O2
    | OPT_O3
    | OPT_Os
End

Definition inline_threshold_size_def:
  inline_threshold_size = 5
End

Definition inline_threshold_default_def:
  inline_threshold_default = 15
End

Definition inline_threshold_aggressive_def:
  inline_threshold_aggressive = 30
End

Definition inline_threshold_for_level_def:
  inline_threshold_for_level OPT_O3 = inline_threshold_aggressive /\
  inline_threshold_for_level OPT_CODESIZE = inline_threshold_size /\
  inline_threshold_for_level OPT_Os = inline_threshold_size /\
  inline_threshold_for_level OPT_NONE = inline_threshold_default /\
  inline_threshold_for_level _ = inline_threshold_default
End

Definition default_optimization_level_def:
  default_optimization_level = OPT_GAS
End

Datatype:
  venom_opt_flags = <|
    vof_level : optimization_level;
    vof_disable_inlining : bool;
    vof_disable_cse : bool;
    vof_disable_sccp : bool;
    vof_disable_load_elimination : bool;
    vof_disable_dead_store_elimination : bool;
    vof_disable_algebraic_optimization : bool;
    vof_disable_branch_optimization : bool;
    vof_disable_mem2var : bool;
    vof_disable_simplify_cfg : bool;
    vof_disable_remove_unused_variables : bool;
    vof_inline_threshold : num
  |>
End

Definition default_venom_opt_flags_def:
  default_venom_opt_flags =
    <| vof_level := default_optimization_level;
       vof_disable_inlining := F;
       vof_disable_cse := F;
       vof_disable_sccp := F;
       vof_disable_load_elimination := F;
       vof_disable_dead_store_elimination := F;
       vof_disable_algebraic_optimization := F;
       vof_disable_branch_optimization := F;
       vof_disable_mem2var := F;
       vof_disable_simplify_cfg := F;
       vof_disable_remove_unused_variables := F;
       vof_inline_threshold := inline_threshold_for_level default_optimization_level |>
End

val _ = export_theory();
