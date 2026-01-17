(*
 * Analysis Cache
 *
 * Port of venom/analysis/analysis.py cache behavior for analyses.
 *)

Theory analysisCache
Ancestors
  list
  cfgAnalysis dfgAnalysis reachableAnalysis dominatorsAnalysis livenessAnalysis
  basePtrAnalysis memAliasAnalysis memSSAAnalysis
  availableExpressionAnalysis
  fcgAnalysis
  addrSpace
  venomInst

Datatype:
  analysis_cache = <|
    ac_ctx : ir_context;
    ac_function : ir_function;
    ac_cfg : cfg_analysis option;
    ac_dfg : dfg_analysis option;
    ac_reachable : reachable_analysis option;
    ac_dominators : dominators_analysis option;
    ac_liveness : liveness_analysis option;
    ac_base_ptr : base_ptr_analysis option;
    ac_mem_alias_memory : mem_alias_analysis option;
    ac_mem_alias_storage : mem_alias_analysis option;
    ac_mem_alias_transient : mem_alias_analysis option;
    ac_available_expr : available_expr_analysis option;
    ac_mem_ssa_memory : mem_ssa_analysis option;
    ac_mem_ssa_storage : mem_ssa_analysis option;
    ac_mem_ssa_transient : mem_ssa_analysis option;
    ac_fcg : fcg_analysis option
  |>
End

Definition dominators_empty_def:
  dominators_empty =
    <| dominators := FEMPTY;
       immediate_dominators := FEMPTY;
       dominated := FEMPTY;
       dominator_frontiers := FEMPTY;
       cfg_post_order := FEMPTY;
       cfg_post_walk := [] |>
End

Definition analysis_cache_init_def:
  analysis_cache_init ctx fn =
    <| ac_ctx := ctx;
       ac_function := fn;
       ac_cfg := NONE;
       ac_dfg := NONE;
       ac_reachable := NONE;
       ac_dominators := NONE;
       ac_liveness := NONE;
       ac_base_ptr := NONE;
       ac_mem_alias_memory := NONE;
       ac_mem_alias_storage := NONE;
       ac_mem_alias_transient := NONE;
       ac_available_expr := NONE;
       ac_mem_ssa_memory := NONE;
       ac_mem_ssa_storage := NONE;
       ac_mem_ssa_transient := NONE;
       ac_fcg := NONE |>
End

Definition analysis_cache_set_function_def:
  analysis_cache_set_function cache fn =
    cache with ac_function := fn
End

Definition analysis_cache_request_cfg_def:
  analysis_cache_request_cfg cache =
    case cache.ac_cfg of
      SOME cfg => (cfg, cache)
    | NONE =>
        let cfg = cfg_analyze cache.ac_function in
        (cfg, cache with ac_cfg := SOME cfg)
End

Definition analysis_cache_request_dfg_def:
  analysis_cache_request_dfg cache =
    case cache.ac_dfg of
      SOME dfg => (dfg, cache)
    | NONE =>
        let dfg = dfg_analyze cache.ac_function in
        (dfg, cache with ac_dfg := SOME dfg)
End

Definition analysis_cache_request_reachable_def:
  analysis_cache_request_reachable cache =
    case cache.ac_reachable of
      SOME r => (r, cache)
    | NONE =>
        let (cfg, cache1) = analysis_cache_request_cfg cache in
        let r = reachable_analyze cache1.ac_function cfg in
        (r, cache1 with ac_reachable := SOME r)
End

Definition analysis_cache_request_dominators_def:
  analysis_cache_request_dominators cache =
    case cache.ac_dominators of
      SOME dom => (SOME dom, cache)
    | NONE =>
        let (cfg, cache1) = analysis_cache_request_cfg cache in
        case dominators_analyze cache1.ac_function cfg of
          NONE => (NONE, cache1)
        | SOME dom =>
            (SOME dom, cache1 with ac_dominators := SOME dom)
End

Definition analysis_cache_request_liveness_def:
  analysis_cache_request_liveness cache =
    case cache.ac_liveness of
      SOME live => (live, cache)
    | NONE =>
        let (cfg, cache1) = analysis_cache_request_cfg cache in
        let live = liveness_analyze cache1.ac_function cfg in
        (live, cache1 with ac_liveness := SOME live)
End

Definition analysis_cache_request_base_ptr_def:
  analysis_cache_request_base_ptr cache =
    case cache.ac_base_ptr of
      SOME bpa => (bpa, cache)
    | NONE =>
        let (cfg, cache1) = analysis_cache_request_cfg cache in
        let bpa = base_ptr_analyze cache1.ac_ctx cache1.ac_function cfg in
        (bpa, cache1 with ac_base_ptr := SOME bpa)
End

Definition analysis_cache_request_mem_alias_def:
  analysis_cache_request_mem_alias cache space =
    case space of
      MEMORY =>
        (case cache.ac_mem_alias_memory of
           SOME ma => (ma, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (bpa, cache2) = analysis_cache_request_base_ptr cache1 in
             let ma = mem_alias_analyze MEMORY cache2.ac_ctx cache2.ac_function cfg bpa in
             (ma, cache2 with ac_mem_alias_memory := SOME ma))
    | STORAGE =>
        (case cache.ac_mem_alias_storage of
           SOME ma => (ma, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (bpa, cache2) = analysis_cache_request_base_ptr cache1 in
             let ma = mem_alias_analyze STORAGE cache2.ac_ctx cache2.ac_function cfg bpa in
             (ma, cache2 with ac_mem_alias_storage := SOME ma))
    | TRANSIENT =>
        (case cache.ac_mem_alias_transient of
           SOME ma => (ma, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (bpa, cache2) = analysis_cache_request_base_ptr cache1 in
             let ma = mem_alias_analyze TRANSIENT cache2.ac_ctx cache2.ac_function cfg bpa in
             (ma, cache2 with ac_mem_alias_transient := SOME ma))
End

Definition analysis_cache_request_available_expr_def:
  analysis_cache_request_available_expr cache =
    case cache.ac_available_expr of
      SOME ae => (ae, cache)
    | NONE =>
        let (cfg, cache1) = analysis_cache_request_cfg cache in
        let (dfg, cache2) = analysis_cache_request_dfg cache1 in
        let ae = available_expr_analyze cache2.ac_function cfg dfg in
        (ae, cache2 with ac_available_expr := SOME ae)
End

Definition analysis_cache_request_mem_ssa_def:
  analysis_cache_request_mem_ssa cache space =
    case space of
      MEMORY =>
        (case cache.ac_mem_ssa_memory of
           SOME ms => (ms, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (dom_opt, cache2) = analysis_cache_request_dominators cache1 in
             let (bpa, cache3) = analysis_cache_request_base_ptr cache2 in
             case dom_opt of
               NONE => (mem_ssa_analyze MEMORY cache3.ac_ctx cache3.ac_function cfg
                         dominators_empty bpa, cache3)
             | SOME dom =>
                 let ms = mem_ssa_analyze MEMORY cache3.ac_ctx cache3.ac_function cfg dom bpa in
                 (ms, cache3 with ac_mem_ssa_memory := SOME ms))
    | STORAGE =>
        (case cache.ac_mem_ssa_storage of
           SOME ms => (ms, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (dom_opt, cache2) = analysis_cache_request_dominators cache1 in
             let (bpa, cache3) = analysis_cache_request_base_ptr cache2 in
             case dom_opt of
               NONE => (mem_ssa_analyze STORAGE cache3.ac_ctx cache3.ac_function cfg
                         dominators_empty bpa, cache3)
             | SOME dom =>
                 let ms = mem_ssa_analyze STORAGE cache3.ac_ctx cache3.ac_function cfg dom bpa in
                 (ms, cache3 with ac_mem_ssa_storage := SOME ms))
    | TRANSIENT =>
        (case cache.ac_mem_ssa_transient of
           SOME ms => (ms, cache)
         | NONE =>
             let (cfg, cache1) = analysis_cache_request_cfg cache in
             let (dom_opt, cache2) = analysis_cache_request_dominators cache1 in
             let (bpa, cache3) = analysis_cache_request_base_ptr cache2 in
             case dom_opt of
               NONE => (mem_ssa_analyze TRANSIENT cache3.ac_ctx cache3.ac_function cfg
                         dominators_empty bpa, cache3)
             | SOME dom =>
                 let ms = mem_ssa_analyze TRANSIENT cache3.ac_ctx cache3.ac_function cfg dom bpa in
                 (ms, cache3 with ac_mem_ssa_transient := SOME ms))
End

Definition analysis_cache_request_fcg_def:
  analysis_cache_request_fcg cache =
    case cache.ac_fcg of
      SOME fcg => (fcg, cache)
    | NONE =>
        let fcg = fcg_analyze cache.ac_ctx in
        (fcg, cache with ac_fcg := SOME fcg)
End

(* ===== Invalidate Helpers ===== *)

Definition analysis_cache_invalidate_cfg_def:
  analysis_cache_invalidate_cfg cache = cache with ac_cfg := NONE
End

Definition analysis_cache_invalidate_dfg_def:
  analysis_cache_invalidate_dfg cache = cache with ac_dfg := NONE
End

Definition analysis_cache_invalidate_reachable_def:
  analysis_cache_invalidate_reachable cache = cache with ac_reachable := NONE
End

Definition analysis_cache_invalidate_dominators_def:
  analysis_cache_invalidate_dominators cache = cache with ac_dominators := NONE
End

Definition analysis_cache_invalidate_liveness_def:
  analysis_cache_invalidate_liveness cache = cache with ac_liveness := NONE
End

Definition analysis_cache_invalidate_base_ptr_def:
  analysis_cache_invalidate_base_ptr cache = cache with ac_base_ptr := NONE
End

Definition analysis_cache_invalidate_available_expr_def:
  analysis_cache_invalidate_available_expr cache = cache with ac_available_expr := NONE
End

Definition analysis_cache_invalidate_mem_alias_def:
  analysis_cache_invalidate_mem_alias cache space =
    case space of
      MEMORY => cache with ac_mem_alias_memory := NONE
    | STORAGE => cache with ac_mem_alias_storage := NONE
    | TRANSIENT => cache with ac_mem_alias_transient := NONE
End

Definition analysis_cache_invalidate_mem_ssa_def:
  analysis_cache_invalidate_mem_ssa cache space =
    case space of
      MEMORY => cache with ac_mem_ssa_memory := NONE
    | STORAGE => cache with ac_mem_ssa_storage := NONE
    | TRANSIENT => cache with ac_mem_ssa_transient := NONE
End

Definition analysis_cache_invalidate_fcg_def:
  analysis_cache_invalidate_fcg cache = cache with ac_fcg := NONE
End

(* ===== Force Helpers ===== *)

Definition analysis_cache_force_dfg_def:
  analysis_cache_force_dfg cache =
    analysis_cache_request_dfg (analysis_cache_invalidate_dfg cache)
End

Definition analysis_cache_force_available_expr_def:
  analysis_cache_force_available_expr cache =
    analysis_cache_request_available_expr (analysis_cache_invalidate_available_expr cache)
End

Definition analysis_cache_force_fcg_def:
  analysis_cache_force_fcg cache =
    analysis_cache_request_fcg (analysis_cache_invalidate_fcg cache)
End

val _ = export_theory();
