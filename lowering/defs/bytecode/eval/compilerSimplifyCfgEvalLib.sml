(* Original and checked executable CFG clauses, one recursive call at a time.
   Configuration only installs metadata; all reductions run in checked pass steps. *)
structure compilerSimplifyCfgEvalLib = struct
  open HolKernel boolLib

  fun specifications () =
    [("simplifyCfgDefs","simplify_cfg_fn_with_labels",1,"simplify_cfg_fn_with_labels_def"),
     ("simplifyCfgDefs","simplify_cfg_iter_with_labels",2,"simplify_cfg_iter_with_labels_def"),
     ("simplifyCfgDefs","simplify_cfg_round_with_labels",1,"simplify_cfg_round_with_labels_def"),
     ("simplifyCfgDefs","remove_unreachable_blocks",1,"remove_unreachable_blocks_def"),
     ("simplifyCfgDefs","fix_all_phis",1,"fix_all_phis_def"),
     ("simplifyCfgDefs","collapse_dfs",4,"collapse_dfs_def"),
     ("simplifyCfgDefs","collapse_dfs_succs",4,"collapse_dfs_def"),
     ("simplifyCfgDefs","try_bypass",4,"try_bypass_def"),
     ("cfgTransform","subst_block_labels_fn",2,"subst_block_labels_fn_def")]

  fun clauses theory name = Conv.FIRST_CONV
    (map Conv.REWR_CONV (CONJUNCTS (SPEC_ALL (DB.fetch theory name))))

  fun iteration current =
    clauses "simplifyCfgDefs" "simplify_cfg_iter_with_labels_def" current
    handle HOL_ERR _ => let
      (* Expose the same numeral's SUC form; the model bound is unchanged. *)
      val fuel = Conv.RATOR_CONV (Conv.RAND_CONV numLib.num_CONV) current
    in TRANS fuel
      (clauses "simplifyCfgDefs" "simplify_cfg_iter_with_labels_def"
        (rhs (concl fuel)))
    end

  fun configure () = let
    val descriptions = specifications ()
    val entries = map (fn (theory,name,arity,_) =>
      (prim_mk_const {Thy=theory,Name=name},arity)) descriptions
    val heads = map #1 entries
    val unfolds = map (fn (theory,name,_,definition) =>
      (prim_mk_const {Thy=theory,Name=name},
       if name = "simplify_cfg_iter_with_labels" then iteration
       else if name = "remove_unreachable_blocks" then
         clauses "simplifyCfgCompute" "remove_unreachable_blocks_compute"
       else clauses theory definition)) descriptions
    val cfg = prim_mk_const {Thy="cfgDefs",Name="cfg_analyze"}
    val captures = map (fn operator => (operator,heads @ [cfg])) heads
    val () = compilerPassEvalLib.extend_phases entries unfolds captures
  in app compilerPassEvalLib.install_indexed_head entries end
end
