(* Binding-free equations for separately checked dominator computations. *)
Theory dominatorCompute
Ancestors
  dominatorDefs venomInst cfgDefs dfAnalyzeDefs dfHelperDefs latticeDefs list option
Libs
  proofAuditLib

Theorem dom_fixpoint_compute:
  dom_fixpoint func =
    df_analyze Forward (fn_labels func) list_intersect dom_transfer_inst
      dom_edge_transfer ()
      (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label func)) func
Proof
  simp[dom_fixpoint_def]
QED

Theorem dom_analyze_compute:
  dom_analyze cfg func =
    <| da_dominators := dom_sets_of func (dom_fixpoint func);
       da_idom := compute_idom cfg.cfg_dfs_post (fn_entry_label func)
         (dom_sets_of func (dom_fixpoint func)) (fn_labels func);
       da_dominated := compute_dominated
         (compute_idom cfg.cfg_dfs_post (fn_entry_label func)
           (dom_sets_of func (dom_fixpoint func)) (fn_labels func))
         (fn_labels func);
       da_frontier := compute_df cfg
         (compute_idom cfg.cfg_dfs_post (fn_entry_label func)
           (dom_sets_of func (dom_fixpoint func)) (fn_labels func))
         cfg.cfg_dfs_post (LENGTH (fn_labels func)) |>
Proof
  simp[dom_analyze_def]
QED

val () = proofAuditLib.check_theory "dominatorCompute";
