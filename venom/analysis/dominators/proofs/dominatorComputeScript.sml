(* Binding-free equations for separately checked dominator computations. *)
Theory dominatorCompute
Ancestors
  dominatorDefs venomInst cfgDefs dfAnalyzeDefs dfHelperDefs latticeDefs list option

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

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("dominator equation has oracle dependencies: " ^ name)
  end) (DB.thms "dominatorCompute");
