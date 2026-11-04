Theory algebraicOptRangeProofs
Ancestors
  rangeAnalysisDefs rangeAnalysisProofs algebraicOptDefs venomExecSemantics unitShapeDefs

(* Coincident JNZ targets select the true-edge refinement.  This is a
   computation boundary only, not a reachable-state soundness assertion. *)
Theorem ao_range_coincident_targets:
  lookup_block pred bbs = SOME bb /\
  ~NULL bb.bb_instructions /\
  LAST bb.bb_instructions = term /\
  term.inst_opcode = JNZ /\
  term.inst_operands = [cond; Label dst; Label dst] ==>
  range_branch_refine dfg bbs pred dst rs =
    range_apply_condition dfg ASSIGN_CHAIN_FUEL cond T rs
Proof
  strip_tac >> simp[range_branch_refine_def]
QED

Theorem ao_range_coincident_edge:
  lookup_block pred bbs = SOME bb /\
  ~NULL bb.bb_instructions /\
  LAST bb.bb_instructions = term /\
  term.inst_opcode = JNZ /\
  term.inst_operands = [cond; Label dst; Label dst] ==>
  range_edge_transfer_opt (dfg,bbs) pred dst (SOME rs) =
    SOME (range_apply_condition dfg ASSIGN_CHAIN_FUEL cond T rs)
Proof
  strip_tac >> simp[range_edge_transfer_opt_def] >>
  drule_all ao_range_coincident_targets >> simp[]
QED

Definition ao_range_edge_probe_def:
  ao_range_edge_probe = mk_raw_function "edge_probe"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 GT [Var "input"; Lit 5w] ["cond"];
        mk_inst 1 JNZ [Var "cond"; Label "dst"; Label "dst"] []] |>;
     <| bb_label := "dst"; bb_instructions :=
       [mk_inst 2 GT [Var "input"; Lit 5w] ["result"];
        mk_inst 3 STOP [] []] |>]
End


Theorem ao_range_probe_cfg:
  cfg_analyze ao_range_edge_probe =
    <| cfg_succs := FEMPTY |+ ("entry",[]) |+ ("dst",[])
                          |+ ("entry",["dst"]) |+ ("dst",[]);
       cfg_preds := FEMPTY |+ ("entry",[]) |+ ("dst",[])
                          |+ ("dst",["entry"]);
       cfg_reachable := FEMPTY |+ ("entry",T) |+ ("dst",T);
       cfg_dfs_post := ["dst";"entry"];
       cfg_dfs_pre := ["entry";"dst"] |>
Proof
  EVAL_TAC
QED

Theorem ao_range_probe_dfg:
  dfg_build_function ao_range_edge_probe =
    <| dfg_uses := FEMPTY
         |+ ("input",[mk_inst 2 GT [Var "input"; Lit 5w] ["result"]])
         |+ ("cond",[mk_inst 1 JNZ [Var "cond"; Label "dst"; Label "dst"] []])
         |+ ("input",[mk_inst 0 GT [Var "input"; Lit 5w] ["cond"];
                       mk_inst 2 GT [Var "input"; Lit 5w] ["result"]]);
       dfg_defs := FEMPTY
         |+ ("result",mk_inst 2 GT [Var "input"; Lit 5w] ["result"])
         |+ ("cond",mk_inst 0 GT [Var "input"; Lit 5w] ["cond"]);
       dfg_ids := FEMPTY
         |+ (3,mk_inst 3 STOP [] [])
         |+ (2,mk_inst 2 GT [Var "input"; Lit 5w] ["result"])
         |+ (1,mk_inst 1 JNZ [Var "cond"; Label "dst"; Label "dst"] [])
         |+ (0,mk_inst 0 GT [Var "input"; Lit 5w] ["cond"]) |>
Proof
  EVAL_TAC
QED

Definition ao_range_probe_process_def:
  ao_range_probe_process =
    df_process_block_widen Forward NONE range_join_opt range_widen_opt
      WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
      (dfg_build_function ao_range_edge_probe, ao_range_edge_probe.fn_blocks)
      (SOME ("entry",SOME FEMPTY)) (cfg_analyze ao_range_edge_probe)
      ao_range_edge_probe.fn_blocks
End

Definition ao_range_probe_initial_def:
  ao_range_probe_initial =
    <| dws_inst := FEMPTY;
       dws_boundary := FEMPTY |+ ("entry",NONE) |+ ("dst",NONE)
                             |+ ("entry",SOME FEMPTY);
       dws_entry := FEMPTY; dws_visits := FEMPTY |>
End

Definition ao_range_probe_first_def:
  ao_range_probe_first = ao_range_probe_initial with <|
      dws_boundary := ao_range_probe_initial.dws_boundary |+ ("entry",SOME FEMPTY);
      dws_entry := FEMPTY |+ ("entry",SOME FEMPTY);
      dws_visits := FEMPTY |+ ("entry",1) |>
End

Theorem ao_range_probe_process_entry:
  ao_range_probe_process "entry" ao_range_probe_initial = ao_range_probe_first
Proof
  rewrite_tac[ao_range_probe_first_def] >>
  rewrite_tac[ao_range_probe_process_def,ao_range_probe_cfg,ao_range_probe_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY]
QED

Definition ao_range_probe_boundary_def:
  ao_range_probe_boundary = <|
    dws_inst := FEMPTY;
    dws_boundary := FEMPTY |+ ("entry",NONE) |+ ("dst",NONE)
      |+ ("entry",SOME FEMPTY)
      |+ ("dst",SOME (FEMPTY |+ ("result",VR_Range 0 1)));
    dws_entry := FEMPTY |+ ("entry",SOME FEMPTY) |+ ("dst",SOME FEMPTY);
    dws_visits := FEMPTY |+ ("entry",1) |+ ("dst",1) |>
End

Theorem ao_range_probe_process_dst:
  ao_range_probe_process "dst" ao_range_probe_first = ao_range_probe_boundary
Proof
  rewrite_tac[ao_range_probe_process_def,ao_range_probe_cfg,ao_range_probe_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC >>
  simp[finite_mapTheory.DRESTRICT_FUPDATE,finite_mapTheory.DRESTRICT_FEMPTY,
       pred_setTheory.IN_GSPEC,valueRangeDefsTheory.vr_is_top_def]
QED

Theorem ao_range_probe_process_dst_stable:
  ao_range_probe_process "dst" ao_range_probe_boundary = ao_range_probe_boundary
Proof
  rewrite_tac[ao_range_probe_process_def,ao_range_probe_cfg,ao_range_probe_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC >>
  simp[finite_mapTheory.DRESTRICT_FUPDATE,finite_mapTheory.DRESTRICT_FEMPTY,
       pred_setTheory.IN_GSPEC,valueRangeDefsTheory.vr_is_top_def] >>
  qmatch_goalsub_abbrev_tac `FUN_FMAP f {key}` >>
  `FUN_FMAP f {key} = FEMPTY |+ (key,f key)` by
    (simp[finite_mapTheory.fmap_eq_flookup,finite_mapTheory.FLOOKUP_FUN_FMAP] >>
     gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FLOOKUP_EMPTY] >>
     IF_CASES_TAC >> simp[]) >>
  simp[] >>
  simp[Abbr `f`,Abbr `key`,valueRangeDefsTheory.vr_union_def,
       finite_mapTheory.DRESTRICT_FUPDATE,finite_mapTheory.DRESTRICT_FEMPTY,
       valueRangeDefsTheory.vr_is_top_def,
       finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FLOOKUP_EMPTY]
QED

Definition ao_range_probe_changed_def:
  ao_range_probe_changed lbl old new =
    (df_widen_boundary NONE new lbl <> df_widen_boundary NONE old lbl \/
     df_widen_entry NONE new lbl <> df_widen_entry NONE old lbl)
End

Theorem ao_range_probe_worklist_entry:
  wl_step ao_range_probe_changed ao_range_probe_process
    (cfg_succs_of (cfg_analyze ao_range_edge_probe))
    (["entry";"dst"],ao_range_probe_initial) =
    (["dst";"dst"],ao_range_probe_first)
Proof
  simp[worklistDefsTheory.wl_step_def,ao_range_probe_process_entry] >>
  rewrite_tac[ao_range_probe_cfg] >> EVAL_TAC
QED

Theorem ao_range_probe_worklist_dst:
  wl_step ao_range_probe_changed ao_range_probe_process
    (cfg_succs_of (cfg_analyze ao_range_edge_probe))
    (["dst";"dst"],ao_range_probe_first) =
    (["dst"],ao_range_probe_boundary)
Proof
  simp[worklistDefsTheory.wl_step_def,ao_range_probe_process_dst] >>
  rewrite_tac[ao_range_probe_cfg] >> EVAL_TAC
QED

Theorem ao_range_probe_worklist_stable:
  wl_step ao_range_probe_changed ao_range_probe_process
    (cfg_succs_of (cfg_analyze ao_range_edge_probe))
    (["dst"],ao_range_probe_boundary) = ([],ao_range_probe_boundary)
Proof
  simp[worklistDefsTheory.wl_step_def,ao_range_probe_process_dst_stable,
       ao_range_probe_changed_def]
QED

Theorem ao_range_probe_worklist:
  wl_iterate ao_range_probe_changed ao_range_probe_process
    (cfg_succs_of (cfg_analyze ao_range_edge_probe))
    ["entry";"dst"] ao_range_probe_initial = ([],ao_range_probe_boundary)
Proof
  rewrite_tac[worklistDefsTheory.wl_iterate_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[ao_range_probe_worklist_entry] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[ao_range_probe_worklist_dst] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[ao_range_probe_worklist_stable] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[]
QED

Theorem ao_range_probe_fold_entry:
  df_fold_block Forward
    (range_transfer_opt (dfg_build_function ao_range_edge_probe,
                         ao_range_edge_probe.fn_blocks)) "entry"
    [mk_inst 0 GT [Var "input";Lit 5w] ["cond"];
     mk_inst 1 JNZ [Var "cond";Label "dst";Label "dst"] []]
    (SOME FEMPTY) =
    (SOME (FEMPTY |+ ("cond",VR_Range 0 1)),
     FEMPTY |+ (("entry",0),SOME FEMPTY)
       |+ (("entry",1),SOME (FEMPTY |+ ("cond",VR_Range 0 1)))
       |+ (("entry",2),SOME (FEMPTY |+ ("cond",VR_Range 0 1))))
Proof
  rewrite_tac[ao_range_probe_dfg] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_range_probe_fold_dst:
  df_fold_block Forward
    (range_transfer_opt (dfg_build_function ao_range_edge_probe,
                         ao_range_edge_probe.fn_blocks)) "dst"
    [mk_inst 2 GT [Var "input";Lit 5w] ["result"];mk_inst 3 STOP [] []]
    (SOME FEMPTY) =
    (SOME (FEMPTY |+ ("result",VR_Range 0 1)),
     FEMPTY |+ (("dst",0),SOME FEMPTY)
       |+ (("dst",1),SOME (FEMPTY |+ ("result",VR_Range 0 1)))
       |+ (("dst",2),SOME (FEMPTY |+ ("result",VR_Range 0 1))))
Proof
  rewrite_tac[ao_range_probe_dfg] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_range_probe_edge:
  range_edge_transfer_opt
    (dfg_build_function ao_range_edge_probe,ao_range_edge_probe.fn_blocks)
    "entry" "dst" (SOME FEMPTY) = SOME FEMPTY
Proof
  rewrite_tac[ao_range_probe_dfg] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_range_probe_population_inputs:
  cfg_preds_of (cfg_analyze ao_range_edge_probe) "entry" = [] /\
  cfg_preds_of (cfg_analyze ao_range_edge_probe) "dst" = ["entry"] /\
  lookup_block "entry" ao_range_edge_probe.fn_blocks =
    SOME <| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 GT [Var "input";Lit 5w] ["cond"];
       mk_inst 1 JNZ [Var "cond";Label "dst";Label "dst"] []] |> /\
  lookup_block "dst" ao_range_edge_probe.fn_blocks =
    SOME <| bb_label := "dst"; bb_instructions :=
      [mk_inst 2 GT [Var "input";Lit 5w] ["result"];mk_inst 3 STOP [] []] |> /\
  df_widen_boundary NONE ao_range_probe_boundary "entry" = SOME FEMPTY /\
  df_widen_visits ao_range_probe_boundary "entry" = 1 /\
  df_widen_visits ao_range_probe_boundary "dst" = 1 /\
  1 < WIDEN_THRESHOLD
Proof
  rewrite_tac[ao_range_probe_cfg] >> EVAL_TAC
QED

Definition ao_range_probe_result_def:
  ao_range_probe_result = ao_range_probe_boundary with dws_inst :=
    FUNION
      (FEMPTY |+ (("dst",0),SOME FEMPTY)
        |+ (("dst",1),SOME (FEMPTY |+ ("result",VR_Range 0 1)))
        |+ (("dst",2),SOME (FEMPTY |+ ("result",VR_Range 0 1))))
      (FUNION
        (FEMPTY |+ (("entry",0),SOME FEMPTY)
          |+ (("entry",1),SOME (FEMPTY |+ ("cond",VR_Range 0 1)))
          |+ (("entry",2),SOME (FEMPTY |+ ("cond",VR_Range 0 1))))
        ao_range_probe_boundary.dws_inst)
End

Theorem ao_range_probe_population:
  df_populate_widen_inst Forward NONE range_join_opt range_widen_opt
    WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
    (dfg_build_function ao_range_edge_probe,ao_range_edge_probe.fn_blocks)
    (SOME ("entry",SOME FEMPTY)) (cfg_analyze ao_range_edge_probe)
    ao_range_edge_probe.fn_blocks ["entry";"dst"] ao_range_probe_boundary = ao_range_probe_result
Proof
  rewrite_tac[dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def] >>
  simp[ao_range_probe_population_inputs,ao_range_probe_edge,
       range_join_opt_def,range_normalize_def,finite_mapTheory.DRESTRICT_FEMPTY,
       ao_range_probe_fold_entry,ao_range_probe_fold_dst] >>
  simp[ao_range_probe_result_def]
QED

Theorem ao_range_probe_setup:
  fn_entry_label ao_range_edge_probe = SOME "entry" /\
  MAP (\bb. bb.bb_label) ao_range_edge_probe.fn_blocks = ["entry";"dst"] /\
  (cfg_analyze ao_range_edge_probe).cfg_dfs_pre = ["entry";"dst"] /\
  (init_df_widen_state NONE ["entry";"dst"] with
    dws_boundary := (init_df_widen_state NONE ["entry";"dst"]).dws_boundary
       |+ ("entry",SOME FEMPTY)) = ao_range_probe_initial
Proof
  rewrite_tac[ao_range_probe_cfg] >> EVAL_TAC
QED

Theorem ao_range_probe_analysis:
  range_analyze ao_range_edge_probe = ao_range_probe_result
Proof
  rewrite_tac[range_analyze_def,dfAnalyzeWidenDefsTheory.df_analyze_widen_def] >>
  simp[ao_range_probe_setup] >>
  rewrite_tac[GSYM ao_range_probe_process_def,
              GSYM ao_range_probe_changed_def] >>
  `(\lbl (old : range_state option df_widen_state) new.
      df_widen_boundary NONE new lbl = df_widen_boundary NONE old lbl ==>
      df_widen_entry NONE new lbl <> df_widen_entry NONE old lbl) =
    ao_range_probe_changed` by
    simp[FUN_EQ_THM,ao_range_probe_changed_def] >>
  asm_rewrite_tac[ao_range_probe_worklist] >>
  simp[ao_range_probe_population]
QED

Theorem ao_range_probe_input_query:
  range_get_range (range_analyze ao_range_edge_probe) "dst" 0 (Var "input") = VR_Top
Proof
  rewrite_tac[ao_range_probe_analysis] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION,finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY,range_unwrap_def]
QED

Theorem ao_range_probe_comparator:
  ao_opt_cmp_range (range_analyze ao_range_edge_probe) "dst" 0
    (mk_inst 2 GT [Var "input";Lit 5w] ["result"]) T F = NONE
Proof
  simp[ao_opt_cmp_range_def,venomInstTheory.mk_inst_def,
       ao_range_probe_input_query] >>
  simp[ao_range_valid_for_cmp_def,valueRangeDefsTheory.vr_is_top_def,
       passSharedDefsTheory.is_lit_op_def]
QED

Definition ao_range_backedge_probe_def:
  ao_range_backedge_probe = mk_raw_function "backedge_probe"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 7w] ["x"];mk_inst 1 JMP [Label "tail"] []] |>;
     <| bb_label := "tail"; bb_instructions :=
       [mk_inst 2 JMP [Label "entry"] []] |>]
End

Theorem ao_range_backedge_wf:
  wf_function ao_range_backedge_probe /\
  wf_ssa ao_range_backedge_probe /\
  fn_inst_wf ao_range_backedge_probe /\
  EVERY label_positions_ok (fn_insts ao_range_backedge_probe)
Proof
  rpt conj_tac
  >- EVAL_TAC
  >- (simp[venomWfTheory.wf_ssa_def,venomWfTheory.ssa_form_def,
           venomWfTheory.def_dominates_uses_def,ao_range_backedge_probe_def,
           venomInstTheory.mk_raw_function_def,venomInstTheory.mk_inst_def,
           venomInstTheory.fn_insts_def] >>
      rpt strip_tac >> gvs[listTheory.MEM] >> EVAL_TAC)
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem ao_range_backedge_cfg:
  cfg_analyze ao_range_backedge_probe =
    <| cfg_succs := FEMPTY |+ ("entry",[]) |+ ("tail",[])
                          |+ ("entry",["tail"]) |+ ("tail",["entry"]);
       cfg_preds := FEMPTY |+ ("entry",[]) |+ ("tail",[])
                          |+ ("tail",["entry"]) |+ ("entry",["tail"]);
       cfg_reachable := FEMPTY |+ ("entry",T) |+ ("tail",T);
       cfg_dfs_post := ["tail";"entry"];
       cfg_dfs_pre := ["entry";"tail"] |>
Proof
  EVAL_TAC
QED

Theorem ao_range_backedge_dfg:
  dfg_build_function ao_range_backedge_probe =
    <| dfg_uses := FEMPTY;
       dfg_defs := FEMPTY |+ ("x",mk_inst 0 ASSIGN [Lit 7w] ["x"]);
       dfg_ids := FEMPTY |+ (2,mk_inst 2 JMP [Label "entry"] [])
         |+ (1,mk_inst 1 JMP [Label "tail"] [])
         |+ (0,mk_inst 0 ASSIGN [Lit 7w] ["x"]) |>
Proof
  EVAL_TAC
QED

Definition ao_range_backedge_process_def:
  ao_range_backedge_process =
    df_process_block_widen Forward NONE range_join_opt range_widen_opt
      WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
      (dfg_build_function ao_range_backedge_probe,ao_range_backedge_probe.fn_blocks)
      (SOME ("entry",SOME FEMPTY)) (cfg_analyze ao_range_backedge_probe)
      ao_range_backedge_probe.fn_blocks
End

Definition ao_range_backedge_initial_def:
  ao_range_backedge_initial =
    <| dws_inst := FEMPTY;
       dws_boundary := FEMPTY |+ ("entry",NONE) |+ ("tail",NONE)
                             |+ ("entry",SOME FEMPTY);
       dws_entry := FEMPTY; dws_visits := FEMPTY |>
End

Theorem ao_range_backedge_first:
  ao_range_backedge_process "entry" ao_range_backedge_initial = ao_range_backedge_initial
Proof
  rewrite_tac[ao_range_backedge_process_def,ao_range_backedge_cfg,ao_range_backedge_dfg] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY]
QED

Definition ao_range_backedge_boundary_def:
  ao_range_backedge_boundary = ao_range_backedge_initial with <|
    dws_boundary := ao_range_backedge_initial.dws_boundary |+ ("tail",SOME FEMPTY);
    dws_entry := FEMPTY |+ ("tail",SOME FEMPTY);
    dws_visits := FEMPTY |+ ("tail",1) |>
End

Theorem ao_range_backedge_tail:
  ao_range_backedge_process "tail" ao_range_backedge_initial = ao_range_backedge_boundary
Proof
  rewrite_tac[ao_range_backedge_process_def,ao_range_backedge_cfg,ao_range_backedge_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY]
QED

Definition ao_range_backedge_final_def:
  ao_range_backedge_final = <|
    dws_inst := FEMPTY;
    dws_boundary := FEMPTY |+ ("entry",NONE) |+ ("tail",NONE)
      |+ ("entry",SOME FEMPTY) |+ ("tail",SOME FEMPTY);
    dws_entry := FEMPTY |+ ("tail",SOME FEMPTY) |+ ("entry",SOME FEMPTY);
    dws_visits := FEMPTY |+ ("tail",1) |+ ("entry",1) |>
End

Theorem ao_range_backedge_reentry:
  ao_range_backedge_process "entry" ao_range_backedge_boundary = ao_range_backedge_final
Proof
  rewrite_tac[ao_range_backedge_process_def,ao_range_backedge_cfg,ao_range_backedge_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY] >>
  simp[finite_mapTheory.fmap_eq_flookup,finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY] >> gen_tac >>
  Cases_on `x = "entry"` >> simp[]
QED

Theorem ao_range_backedge_tail_stable:
  ao_range_backedge_process "tail" ao_range_backedge_final = ao_range_backedge_final
Proof
  rewrite_tac[ao_range_backedge_process_def,ao_range_backedge_cfg,ao_range_backedge_dfg] >>
  EVAL_TAC >> simp[finite_mapTheory.FUN_FMAP_EMPTY,finite_mapTheory.DRESTRICT_FEMPTY]
QED

Theorem ao_range_backedge_steps:
  wl_step ao_range_probe_changed ao_range_backedge_process
    (cfg_succs_of (cfg_analyze ao_range_backedge_probe))
    (["entry";"tail"],ao_range_backedge_initial) = (["tail"],ao_range_backedge_initial) /\
  wl_step ao_range_probe_changed ao_range_backedge_process
    (cfg_succs_of (cfg_analyze ao_range_backedge_probe))
    (["tail"],ao_range_backedge_initial) = (["entry"],ao_range_backedge_boundary) /\
  wl_step ao_range_probe_changed ao_range_backedge_process
    (cfg_succs_of (cfg_analyze ao_range_backedge_probe))
    (["entry"],ao_range_backedge_boundary) = (["tail"],ao_range_backedge_final) /\
  wl_step ao_range_probe_changed ao_range_backedge_process
    (cfg_succs_of (cfg_analyze ao_range_backedge_probe))
    (["tail"],ao_range_backedge_final) = ([],ao_range_backedge_final)
Proof
  simp[worklistDefsTheory.wl_step_def,ao_range_backedge_first,ao_range_backedge_tail,
       ao_range_backedge_reentry,ao_range_backedge_tail_stable,ao_range_probe_changed_def] >>
  rewrite_tac[ao_range_backedge_cfg] >> EVAL_TAC
QED

Theorem ao_range_backedge_worklist:
  wl_iterate ao_range_probe_changed ao_range_backedge_process
    (cfg_succs_of (cfg_analyze ao_range_backedge_probe))
    ["entry";"tail"] ao_range_backedge_initial = ([],ao_range_backedge_final)
Proof
  rewrite_tac[worklistDefsTheory.wl_iterate_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[ao_range_backedge_steps] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[ao_range_backedge_steps] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[ao_range_backedge_steps] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[ao_range_backedge_steps] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[]
QED

Theorem ao_range_backedge_folds:
  df_fold_block Forward
    (range_transfer_opt (dfg_build_function ao_range_backedge_probe,
                         ao_range_backedge_probe.fn_blocks)) "entry"
    [mk_inst 0 ASSIGN [Lit 7w] ["x"];mk_inst 1 JMP [Label "tail"] []]
    (SOME FEMPTY) =
    (SOME (FEMPTY |+ ("x",VR_Range 7 7)),
     FEMPTY |+ (("entry",0),SOME FEMPTY)
       |+ (("entry",1),SOME (FEMPTY |+ ("x",VR_Range 7 7)))
       |+ (("entry",2),SOME (FEMPTY |+ ("x",VR_Range 7 7)))) /\
  df_fold_block Forward
    (range_transfer_opt (dfg_build_function ao_range_backedge_probe,
                         ao_range_backedge_probe.fn_blocks)) "tail"
    [mk_inst 2 JMP [Label "entry"] []] (SOME FEMPTY) =
    (SOME FEMPTY,FEMPTY |+ (("tail",0),SOME FEMPTY) |+ (("tail",1),SOME FEMPTY))
Proof
  rewrite_tac[ao_range_backedge_dfg] >> EVAL_TAC >>
  simp[wordsTheory.word_msb_def,wordsTheory.dimword_def,
       wordsTheory.word_L_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Definition ao_range_backedge_result_def:
  ao_range_backedge_result = ao_range_backedge_final with dws_inst :=
    FUNION (FEMPTY |+ (("tail",0),SOME FEMPTY) |+ (("tail",1),SOME FEMPTY))
      (FUNION (FEMPTY |+ (("entry",0),SOME FEMPTY)
        |+ (("entry",1),SOME (FEMPTY |+ ("x",VR_Range 7 7)))
        |+ (("entry",2),SOME (FEMPTY |+ ("x",VR_Range 7 7)))) FEMPTY)
End

Theorem ao_range_backedge_population_inputs:
  cfg_preds_of (cfg_analyze ao_range_backedge_probe) "entry" = ["tail"] /\
  cfg_preds_of (cfg_analyze ao_range_backedge_probe) "tail" = ["entry"] /\
  range_edge_transfer_opt
    (dfg_build_function ao_range_backedge_probe,ao_range_backedge_probe.fn_blocks)
    "entry" "tail" (SOME FEMPTY) = SOME FEMPTY /\
  range_edge_transfer_opt
    (dfg_build_function ao_range_backedge_probe,ao_range_backedge_probe.fn_blocks)
    "tail" "entry" (SOME FEMPTY) = SOME FEMPTY /\
  df_widen_boundary NONE ao_range_backedge_final "entry" = SOME FEMPTY /\
  df_widen_boundary NONE ao_range_backedge_final "tail" = SOME FEMPTY /\
  df_widen_visits ao_range_backedge_final "entry" = 1 /\
  df_widen_visits ao_range_backedge_final "tail" = 1 /\
  1 < WIDEN_THRESHOLD
Proof
  rewrite_tac[ao_range_backedge_cfg,ao_range_backedge_dfg] >> EVAL_TAC
QED

Theorem ao_range_backedge_population:
  df_populate_widen_inst Forward NONE range_join_opt range_widen_opt
    WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
    (dfg_build_function ao_range_backedge_probe,ao_range_backedge_probe.fn_blocks)
    (SOME ("entry",SOME FEMPTY)) (cfg_analyze ao_range_backedge_probe)
    ao_range_backedge_probe.fn_blocks ["entry";"tail"] ao_range_backedge_final =
    ao_range_backedge_result
Proof
  `lookup_block "entry" ao_range_backedge_probe.fn_blocks =
    SOME <| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 ASSIGN [Lit 7w] ["x"];mk_inst 1 JMP [Label "tail"] []] |>` by EVAL_TAC >>
  `lookup_block "tail" ao_range_backedge_probe.fn_blocks =
    SOME <| bb_label := "tail"; bb_instructions :=
      [mk_inst 2 JMP [Label "entry"] []] |>` by EVAL_TAC >>
  rewrite_tac[dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def] >>
  simp[ao_range_backedge_population_inputs,range_join_opt_def,range_normalize_def,
       finite_mapTheory.DRESTRICT_FEMPTY,ao_range_backedge_folds] >>
  simp[ao_range_backedge_result_def,ao_range_backedge_final_def]
QED

Theorem ao_range_backedge_setup:
  fn_entry_label ao_range_backedge_probe = SOME "entry" /\
  MAP (\bb. bb.bb_label) ao_range_backedge_probe.fn_blocks = ["entry";"tail"] /\
  (cfg_analyze ao_range_backedge_probe).cfg_dfs_pre = ["entry";"tail"] /\
  (init_df_widen_state NONE ["entry";"tail"] with
    dws_boundary := (init_df_widen_state NONE ["entry";"tail"]).dws_boundary
      |+ ("entry",SOME FEMPTY)) = ao_range_backedge_initial
Proof
  rewrite_tac[ao_range_backedge_cfg] >> EVAL_TAC
QED

Theorem ao_range_backedge_analysis:
  range_analyze ao_range_backedge_probe = ao_range_backedge_result
Proof
  rewrite_tac[range_analyze_def,dfAnalyzeWidenDefsTheory.df_analyze_widen_def] >>
  simp[ao_range_backedge_setup] >>
  rewrite_tac[GSYM ao_range_backedge_process_def,GSYM ao_range_probe_changed_def] >>
  `(\lbl (old : range_state option df_widen_state) new.
      df_widen_boundary NONE new lbl = df_widen_boundary NONE old lbl ==>
      df_widen_entry NONE new lbl <> df_widen_entry NONE old lbl) =
    ao_range_probe_changed` by simp[FUN_EQ_THM,ao_range_probe_changed_def] >>
  asm_rewrite_tac[ao_range_backedge_worklist] >>
  simp[ao_range_backedge_population]
QED

Theorem ao_range_backedge_initial_cache:
  range_at_inst (range_analyze ao_range_backedge_probe) "entry" 0 = FEMPTY
Proof
  rewrite_tac[ao_range_backedge_analysis] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION,finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY,range_unwrap_def]
QED

(* The entry-backedge fixture has no constrained initial cache keys.
   Thus both arbitrary values (including x = 8) and absent outputs are
   sound here; this fixture does not distinguish those interfaces. *)
Theorem ao_range_backedge_initial_sound:
  !env. in_range_state
    (range_at_inst (range_analyze ao_range_backedge_probe) "entry" 0) env
Proof
  simp[ao_range_backedge_initial_cache,rangeEvalDefsTheory.in_range_state_def,
       finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem ao_range_join_sound[local]:
  !a b s. range_sound a s /\ range_sound b s ==>
    range_sound (range_join_opt a b) s
Proof
  Cases >> Cases >> simp[range_join_opt_def,range_sound_bottom] >>
  metis_tac[range_join_opt_some_sound_left,range_join_opt_some_sound_right,
            range_join_opt_def]
QED

Theorem ao_range_fold_join_sound:
  !xs acc s. range_sound acc s /\ EVERY (\x. range_sound x s) xs ==>
    range_sound (FOLDL range_join_opt acc xs) s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> irule ao_range_join_sound >> simp[]
QED

Theorem ao_range_widen_sound:
  !old new s. range_sound new s ==> range_sound (range_widen_opt old new) s
Proof
  Cases >> Cases >> simp[range_widen_opt_def,range_sound_bottom,range_sound_fempty] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[range_sound_fempty]
QED

Theorem ao_range_computed_entry_sound:
  !edges seed (lbl:string) joined old (visits:num) threshold s.
    EVERY (\x. range_sound x s) edges /\
    (case seed of NONE => T | SOME (l,v) => l = lbl ==> range_sound v s) /\
    joined = (case edges of
      [] => (case seed of NONE => NONE | SOME (l,v) => if lbl = l then v else NONE)
    | _ => FOLDL range_join_opt NONE edges) ==>
    range_sound (if visits >= threshold then range_widen_opt old joined else joined) s
Proof
  rpt gen_tac >> strip_tac >>
  `range_sound joined s` by
    (Cases_on `edges`
     >- (Cases_on `seed` >> gvs[range_sound_bottom] >>
         PairCases_on `x` >> gvs[] >> IF_CASES_TAC >> gvs[range_sound_bottom])
     >> gvs[] >> irule ao_range_fold_join_sound >>
        simp[] >> irule ao_range_join_sound >> simp[range_sound_bottom]) >>
  IF_CASES_TAC >> simp[ao_range_widen_sound]
QED

Theorem ao_range_process_entry_sound:
  !transfer edge_transfer ctx cfg bbs threshold seed lbl st s q.
    (!p. range_sound (df_widen_entry NONE st p) s) /\
    EVERY (\nbr. range_sound
      (edge_transfer ctx nbr lbl (df_widen_boundary NONE st nbr)) s)
      (cfg_preds_of cfg lbl) /\
    (case seed of NONE => T | SOME (l,v) => l = lbl ==> range_sound v s) ==>
    range_sound (df_widen_entry NONE
      (df_process_block_widen Forward NONE range_join_opt range_widen_opt
        threshold transfer edge_transfer ctx seed cfg bbs lbl st) q) s
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `EVERY _ neighbors` >>
  qabbrev_tac `edges = MAP (\nbr.
    edge_transfer ctx nbr lbl (df_widen_boundary NONE st nbr)) neighbors` >>
  qabbrev_tac `joined = (case edges of
      [] => (case seed of NONE => NONE | SOME (l,v) => if lbl = l then v else NONE)
    | _ => FOLDL range_join_opt NONE edges)` >>
  qabbrev_tac `entry = if df_widen_visits st lbl >= threshold then
    range_widen_opt (df_widen_entry NONE st lbl) joined else joined` >>
  `range_sound entry s` by
    (simp[Abbr `entry`] >> irule ao_range_computed_entry_sound >>
     qexistsl_tac [`edges`,`lbl`,`seed`] >>
     simp[Abbr `joined`,Abbr `edges`,listTheory.EVERY_MAP]) >>
  rewrite_tac[Once dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  fs[markerTheory.Abbrev_def] >>
  qpat_x_assum `neighbors = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `edges = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `joined = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `entry = _` (fn th => rewrite_tac[GSYM th]) >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >- simp[] >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_entry_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `q = lbl` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_entry_def]
QED

(* External-input diagnostic: no instruction defines the branch operand. *)
Definition ao_range_external_probe_def:
  ao_range_external_probe = mk_raw_function "external_probe"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 JMP [Label "tail"] []] |>;
     <| bb_label := "tail"; bb_instructions :=
       [mk_inst 1 JNZ [Var "external";Label "done";Label "entry"] []] |>;
     <| bb_label := "done"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Theorem ao_range_external_wf:
  wf_function ao_range_external_probe /\
  fn_inst_wf ao_range_external_probe /\
  EVERY label_positions_ok (fn_insts ao_range_external_probe)
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem ao_range_external_edge:
  range_edge_transfer_opt
    (dfg_build_function ao_range_external_probe,ao_range_external_probe.fn_blocks)
    "tail" "entry" (SOME FEMPTY) = SOME FEMPTY
Proof
  EVAL_TAC
QED

Theorem ao_range_external_not_ssa:
  ~wf_ssa ao_range_external_probe
Proof
  simp[venomWfTheory.wf_ssa_def,venomWfTheory.def_dominates_uses_def,
       ao_range_external_probe_def,venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def,venomWfTheory.def_available_at_def] >>
  EVAL_TAC >> simp[listTheory.MEM] >>
  qexistsl [`<| bb_label := "tail"; bb_instructions :=
    [mk_inst 1 JNZ [Var "external";Label "done";Label "entry"] []] |>`,
    `mk_inst 1 JNZ [Var "external";Label "done";Label "entry"] []`] >>
  simp[venomInstTheory.mk_inst_def] >>
  rpt gen_tac >> spose_not_then strip_assume_tac >>
  Cases_on `def_bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 JMP [Label "tail"] []] |>` >>
  gvs[listTheory.MEM,venomInstTheory.mk_inst_def]
QED
