Theory fnPlanLineageReplayInterfaceProbe
Ancestors
  fnPlanLineageSetup fnPlanLineageSuffix fnPlanLineageNativeTargets
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst
  dfgDefs cfgDefs livenessDefs finite_map

(* Local arbitrary-state experiments, not a lineage counterexample. *)
Definition shadow_probe_fn_def:
  shadow_probe_fn = mk_raw_function "shadow"
    [<|bb_label := "J"; bb_instructions := []|>]
End

Definition shadow_probe_live_def:
  shadow_probe_live = (init_df_state [] []) with
    ds_inst := FEMPTY |+ (("J",0), ["x"])
End

Definition shadow_probe_state_def:
  shadow_probe_state stk spills =
    (init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := stk; ps_spilled := spills|>
End

Definition shadow_probe_add_def:
  shadow_probe_add ps =
    generate_regular_inst_plan shadow_probe_live
      (dfg_build_function shadow_probe_fn) (cfg_analyze shadow_probe_fn)
      shadow_probe_fn (mk_inst 0 ADD [Var "x"; Lit 1w] ["y"])
      ["x";"y"] F T "P" ps
End

Theorem shadow_probe_suffix_replay:
  FST (shadow_probe_add (shadow_probe_state [Var "x"] FEMPTY)) =
    FST (shadow_probe_add (shadow_probe_state [Var "x";Var "x"] FEMPTY)) /\
  (SND (shadow_probe_add (shadow_probe_state [Var "x";Var "x"] FEMPTY))).ps_stack =
    Var "x" :: (SND (shadow_probe_add (shadow_probe_state [Var "x"] FEMPTY))).ps_stack /\
  (SND (shadow_probe_add (shadow_probe_state [Var "x";Var "x"] FEMPTY))).ps_alloc =
    (SND (shadow_probe_add (shadow_probe_state [Var "x"] FEMPTY))).ps_alloc
Proof
  EVAL_TAC >> simp[]
QED

Theorem shadow_probe_spill_replay:
  FST (shadow_probe_add (shadow_probe_state [] (FEMPTY |+ (Var "x",0)))) =
    FST (shadow_probe_add (shadow_probe_state [Var "x"] (FEMPTY |+ (Var "x",0)))) /\
  (SND (shadow_probe_add (shadow_probe_state [Var "x"] (FEMPTY |+ (Var "x",0))))).ps_stack =
    Var "x" :: (SND (shadow_probe_add (shadow_probe_state [] (FEMPTY |+ (Var "x",0))))).ps_stack
Proof
  EVAL_TAC >> simp[]
QED

Definition shadow_probe_jmp_def:
  shadow_probe_jmp ps =
    generate_inst_plan shadow_probe_live
      (dfg_build_function shadow_probe_fn) (cfg_analyze shadow_probe_fn)
      shadow_probe_fn (mk_inst 1 JMP [Label "J"] []) ["x"] F F "P" ps
End

Theorem shadow_probe_jmp_restore_success:
  IS_SOME (shadow_probe_jmp (shadow_probe_state [] (FEMPTY |+ (Var "x",0)))) /\
  IS_SOME (shadow_probe_jmp (shadow_probe_state [Var "x"] (FEMPTY |+ (Var "x",0)))) /\
  FST (THE (shadow_probe_jmp (shadow_probe_state [] (FEMPTY |+ (Var "x",0))))) =
    FST (THE (shadow_probe_jmp (shadow_probe_state [Var "x"] (FEMPTY |+ (Var "x",0))))) /\
  MEM (SORestore 0)
    (FST (THE (shadow_probe_jmp (shadow_probe_state [Var "x"] (FEMPTY |+ (Var "x",0))))))
Proof
  EVAL_TAC >> simp[]
QED

Theorem shadow_probe_jmp_suffix_success:
  IS_SOME (shadow_probe_jmp (shadow_probe_state [Var "x"] FEMPTY)) /\
  IS_SOME (shadow_probe_jmp (shadow_probe_state [Var "x";Var "x"] FEMPTY)) /\
  FST (THE (shadow_probe_jmp (shadow_probe_state [Var "x"] FEMPTY))) =
    FST (THE (shadow_probe_jmp (shadow_probe_state [Var "x";Var "x"] FEMPTY)))
Proof
  EVAL_TAC >> simp[]
QED

(* A missing suffix hit matters: the same metadata and a common spill map
   alone cannot shield optimistic_swap's query of LAST next_liveness. *)
Theorem shadow_probe_missing_hit_observable:
  FST (optimistic_swap_plan (dfg_build_function shadow_probe_fn)
    (mk_inst 0 ADD [] ["y"]) ["x"] F
    (shadow_probe_state [Var "y"] FEMPTY)) = [] /\
  FST (optimistic_swap_plan (dfg_build_function shadow_probe_fn)
    (mk_inst 0 ADD [] ["y"]) ["x"] F
    (shadow_probe_state [Var "x";Var "y"] FEMPTY)) = [SOSwap 1]
Proof
  EVAL_TAC >> simp[]
QED

(* REPLAY INTERFACE AUDIT (local probe, not a universal invariant proof)

   Operation / observation                 Sufficient shielding boundary
   emit_one_input, restore_spilled_plan     Same spill map restores FIRST,
     stackPlanGen:23, stackPlanOps:57        even if prefix already contains x.
                                            Otherwise a suffix lookup hit;
                                            or absence in BOTH prefixes.
   reorder_plan / commutative cost choice    Same selected depths and enough
     Setup.lineage_regular_prepare_*        common core; <=16 input arity
                                            gives its existing consumption
                                            bound. Prefix absence unnecessary
                                            for an actual suffix hit.
   stack_pop consumed operands              At least operand-count common
                                            cells after preparation: mere
                                            name membership is insufficient.
   popmany dead outputs                     Each queried output must still
     Setup.native_regular_singleton_*       hit the core at its turn (singleton
                                            fresh output hits top). Multi-output
                                            sequence needs its own hit proof.
   optimistic_swap_plan (Gen:108)            LAST nl hits common post-pop core,
                                            or absent in BOTH prefixes. This is
                                            the explicit nl-absence use in
                                            native_regular_bottom_frame, not a
                                            general resource uniqueness need.
   release_dead_spills                       Same spilled/alloc metadata and nl;
                                            stack contents not inspected.
   generate_emit_ops                        Same metadata, common arguments;
                                            existing slots/frame boundary.
   JMP restore/reorder (Gen:282)             Shared spill map restores targets
                                            before lookup; remaining targets
                                            need common-core hits and reorder
                                            footprint bounds. join_reached must
                                            still succeed on BOTH states; do
                                            not infer this from unit counts.
   PHI                                      Alternative lookup hit in common
                                            suffix (Suffix phi-hit lemma), plus
                                            selected operand and dup/poke
                                            footprint within that suffix.

   Candidate paired-state relation at an instruction boundary:
     exists base p q. left = base[stack := p ++ base.stack] /\
                       right = base[stack := q ++ base.stack] /\
       for every imminent lookup query, either its first observation hits
       base.stack, or both prefixes miss it, or the native operation performs
       a shared-map restoration before that observation;
       every destructive footprint fits within the evolving common core.
   For PHI the query is a predicate/alternative set rather than one name.
   This is deliberately a stage-indexed observational relation, NOT an
   assertion that all nl names are physically unique or absent from prefixes.

   Earliest unresolved producers/preservation obligations:
   - actual lineage/DFS entry states must admit shared metadata/base and
     common-core demand support; successful JMP gives a suffix but not shared
     alloc/spill metadata by itself;
   - after each native prepare/output/pop stage, show LAST nl is in core when
     present in either prefix (or prove both prefixes miss). The missing-hit
     theorem above is an explicit obstruction to omitting this premise;
   - repeated definitions and PHI must preserve these stage-wise observations;
     input/output freshness alone is not a proof of delayed spill reset;
   - multi-output pops, deep swap/dup spill footprints and JMP reorder must
     preserve core capacity and metadata agreement, including successful guard;
   - initialization, cleanup and native prefix composition must produce the
     relation, not merely assume it at each instruction.
   The checked suffix/spill ADD and JMP instances show that unary absence is
   stronger than needed locally. They do NOT prove any global producer or
   falsify lineage_state_block_plan. Shared spills shield immediate restores,
   not arbitrary later optimistic queries after those spills have been freed.
*)
