Theory concretizeAnalysisMetadataSchedule
Ancestors
  o1PassContract venomPassSchedule venomPassDispatcher venomInst
  concretizeMemLocDefs list

Theorem concretize_observation_suffix:
  DROP 3 o1_fn_passes =
    [CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
Proof
  simp[o1_fn_passes_def]
QED

Theorem fn_steps_name:
  !passes fn fn'. fn_steps rpolicy passes fn fn' ==> fn'.fn_name = fn.fn_name
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >>
  gvs[fn_pass_step_def] >> metis_tac[]
QED

Theorem concretize_context_rebuilds_metadata:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME out ==>
  ?layout. out = apply_context_concretize_layout ctx layout fn
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

(* Conditional transport states exactly what the suffix theorem must supply.
   It does not infer summary equality from the name-only runner checks. *)
Theorem walk_view_mems_used:
  walk_view rpolicy later C' fn observed /\
  (!g h. fn_steps rpolicy later g h ==> h.fn_mems_used = g.fn_mems_used) /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name C'.ctx_functions = SOME g' ==>
  ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
      g.fn_name = g'.fn_name /\ g.fn_mems_used = g'.fn_mems_used
Proof
  rw[walk_view_def] >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `g` >> metis_tac[fn_steps_name]
QED

(* Source audit for the remaining unconditional suffix interface:
   - fn_pass_step checks fn_name, but fn_static_layout_eq checks only fn_eom.
     Neither contract field mentions fn_mems_used; executable preservation
     proofs are required, not consequence of the runner's metadata checks.
   - fmp_lower_function delegates to fmp_lower_function_with_info; its success
     branches return fn unchanged or fmp_checked_seal. fmp_seal updates only
     fn_blocks and fn_fmp_signature.
   - make_ssa_current_fn returns fn unchanged or updates only fn_blocks.
   - simplify_cfg_fn_with_labels iterates simplify_cfg_round_with_labels;
     need preservation through remove_unreachable_blocks, fix_all_phis,
     collapse_dfs and subst_block_labels_fn, then its iterator.
   - sue_expand_function_supply updates only fn_blocks.
   - dft_fn updates only fn_blocks.
   - cfg_norm_function_supply iterates find_and_split_supply; its modifying
     primitive insert_split_supply updates only fn_blocks.
   Required exported interfaces (in new proof theories, executable defs frozen):
     fmp_lower_function ctx s fn = SOME (out,s') ==> out.fn_mems_used = fn.fn_mems_used
     make_ssa_current_fn s fn = (out,s') ==> out.fn_mems_used = fn.fn_mems_used
     simplify_cfg_fn_with_labels fn = (out,lm) ==> out.fn_mems_used = fn.fn_mems_used
     sue_expand_function_supply s fn = (out,s') ==> out.fn_mems_used = fn.fn_mems_used
     (dft_fn fn).fn_mems_used = fn.fn_mems_used
     cfg_norm_function_supply s fn = (out,s') ==> out.fn_mems_used = fn.fn_mems_used
   Then dispatcher case projections and list induction give the unconditional
   fn_steps suffix equality needed by walk_view_mems_used. Existing *_metadata
   theorems establish other field equalities, not this field.

   Source/output pairing is LIST_REL in ctx_pass_stage_def. A consumer needs a
   lookup-pair elimination: given distinct source function names and lookup of
   a source fn, obtain the corresponding output fn, observed unit and step,
   and lookup that same name in C'. Name preservation in fn_pass_step provides
   the mapped-name equality; walk_view_mems_used then transports output summary
   ownership to the actually observed callee. No equality of whole functions
   is justified or needed. These obligations remain separate from source
   ownership and from the proof that actual summaries have source owners.
*)
