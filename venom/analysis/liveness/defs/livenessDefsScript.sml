(*
 * Liveness Analysis — Definitions
 *
 * Upstream: vyperlang/vyper@d21ee3ba9 (positional phi substitution)
 *
 * Backward liveness analysis with Python-ordered block recomputation.
 *
 * TOP-LEVEL:
 *   liveness_analyze      — run full liveness analysis on a function
 *   liveness_analyze_fuel — bounded liveness analysis for evaluator use
 *   live_vars_at          — query live variables before instruction idx
 *   input_vars_from       — live vars entering target from source (PHI-aware)
 *
 * Soundness statement helpers:
 *   cfg_exec_path         — valid execution path through CFG
 *   var_used_at           — variable read at position
 *   var_defined_at        — variable written at position
 *   used_before_defined   — used before redefined along path
 *   fn_all_vars           — all variable names in a function
 *)

Theory livenessDefs
Ancestors
  list finite_map pred_set
  venomInst cfgDefs dfAnalyzeDefs dfHelperDefs worklistDefs

(* ==========================================================================
   Transfer function: (live \ defs) ∪ uses
   ========================================================================== *)

Definition live_update_def:
  live_update defs uses live =
    let live' = FILTER (λv. ¬MEM v defs) live in
    live' ++ FILTER (λv. ¬MEM v live') uses
End

Definition ordered_inst_uses_def:
  ordered_inst_uses inst =
    operand_vars (python_stack_operands inst.inst_opcode inst.inst_operands)
End

Theorem MEM_ordered_inst_uses[simp]:
  MEM v (ordered_inst_uses inst) <=> MEM v (inst_uses inst)
Proof
  rw[ordered_inst_uses_def, inst_uses_def, python_stack_operands_def] >>
  simp[]
QED
Definition liveness_transfer_def:
  liveness_transfer (bbs : basic_block list) (inst : instruction)
                    (live : string list) =
    live_update (inst_defs inst) (ordered_inst_uses inst) live
End

(* ==========================================================================
   PHI-aware edge transfer
   ========================================================================== *)

(* Collect PHI instructions from the start of a block *)
Definition collect_phis_def:
  collect_phis [] = [] ∧
  collect_phis (inst :: rest) =
    if inst.inst_opcode = PHI then inst :: collect_phis rest
    else []
End

(* Pinned Python maps every incoming PHI operand to the PHI's positional
   index, then selects the operand associated with the traversed source edge. *)
Definition build_phi_maps_def:
  build_phi_maps src_label phis =
    let indexed = MAPi (λi phi. (i, phi)) phis in
    FOLDL (λ(op_map, matching) (i, phi).
      let pairs = phi_pairs phi.inst_operands in
      let op_map' = FOLDL (λm (l,v). m |+ (v, i)) op_map pairs in
      let src_var = FIND (λ(l,v). l = src_label) pairs in
      let matching' = case src_var of
                        SOME (_, v) => matching |+ (i, v)
                      | NONE => matching in
      (op_map', matching'))
    (FEMPTY : (string, num) fmap, FEMPTY : (num, string) fmap) indexed
End

Definition input_vars_from_def:
  input_vars_from src_label target_instrs base_liveness =
    let phis = collect_phis target_instrs in
    if NULL phis then base_liveness
    else
      let (op_map, matching) = build_phi_maps src_label phis in
      let (result, placed) = FOLDL (λ(acc, placed) v.
        case FLOOKUP op_map v of
          SOME phi_idx =>
            if MEM phi_idx placed then (acc, placed)
            else
              (case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx :: placed)
               | NONE => (acc, placed))
        | NONE => (acc ++ [v], placed))
        ([], [] : num list) base_liveness in
      result
End

Definition liveness_edge_transfer_def:
  liveness_edge_transfer (bbs : basic_block list) succ_lbl cur_lbl
                         (live : string list) =
    case lookup_block succ_lbl bbs of
      NONE => live
    | SOME succ_bb =>
        input_vars_from cur_lbl succ_bb.bb_instructions live
End

(* ==========================================================================
   Block recomputation and staged Python-ordered drivers
   ========================================================================== *)

(* Python OrderedSet equality ignores order. *)
Definition same_vars_def:
  same_vars (xs : string list) ys <=>
    EVERY (λv. MEM v ys) xs ∧ EVERY (λv. MEM v xs) ys
End

Theorem same_vars_set:
  same_vars xs ys <=> set xs = set ys
Proof
  simp[same_vars_def, EVERY_MEM, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Definition liveness_block_def:
  liveness_block bbs cfg lbl (st : string list df_state) =
    let out = FOLDL list_union []
          (MAP (λs. liveness_edge_transfer bbs s lbl (df_at [] st s 0))
               (cfg_succs_of cfg lbl)) in
    let instrs = (case lookup_block lbl bbs of
                    NONE => [] | SOME bb => bb.bb_instructions) in
    let (entry, inst_map) =
          df_fold_block Backward (liveness_transfer bbs) lbl instrs out in
    st with <| ds_inst := FUNION inst_map st.ds_inst;
               ds_boundary := st.ds_boundary |+ (lbl, entry) |>
End

Definition liveness_changed_def:
  liveness_changed bbs lbl (old : string list df_state) new <=>
    let n = (case lookup_block lbl bbs of
               NONE => 0 | SOME bb => LENGTH bb.bb_instructions) in
    ¬(same_vars (df_at [] new lbl n) (df_at [] old lbl n) ∧
      same_vars (df_at [] new lbl 0) (df_at [] old lbl 0))
End

(* Staged implementation: the public driver switches together with its
   iteration proofs and consumers, after the preparation theories integrate. *)
Definition liveness_recompute_def:
  liveness_recompute fn =
    let cfg = cfg_analyze fn in
    SND (wl_iterate (liveness_changed fn.fn_blocks)
           (liveness_block fn.fn_blocks cfg) (cfg_preds_of cfg)
           cfg.cfg_dfs_post
           (init_df_state [] (MAP (λbb. bb.bb_label) fn.fn_blocks)))
End

Definition liveness_recompute_fuel_def:
  liveness_recompute_fuel fuel fn =
    let cfg = cfg_analyze fn in
    SND (wl_iterate_fuel fuel (liveness_changed fn.fn_blocks)
           (liveness_block fn.fn_blocks cfg) (cfg_preds_of cfg)
           cfg.cfg_dfs_post
           (init_df_state [] (MAP (λbb. bb.bb_label) fn.fn_blocks)))
End

(* Public drivers recompute and overwrite each block, without a final refold. *)
Definition liveness_analyze_def:
  liveness_analyze fn = liveness_recompute fn
End

Definition liveness_analyze_fuel_def:
  liveness_analyze_fuel fuel fn = liveness_recompute_fuel fuel fn
End

(* ==========================================================================
   Query API
   ========================================================================== *)

(* Live variables before instruction idx in block lbl.
   idx = LENGTH instrs gives the exit liveness (live-out). *)
Definition live_vars_at_def:
  live_vars_at st lbl idx = df_at [] st lbl idx
End

(* ==========================================================================
   Variable universe (for boundedness statement)
   ========================================================================== *)

Definition fn_all_vars_def:
  fn_all_vars bbs =
    FLAT (MAP (λbb.
      FLAT (MAP (λinst. inst_uses inst ++ inst_defs inst)
                bb.bb_instructions))
      bbs)
End

(* ==========================================================================
   Execution path and use/def at a point (for soundness statement)
   ========================================================================== *)

Definition cfg_exec_path_def:
  cfg_exec_path cfg ([] : (string # num) list) = T ∧
  cfg_exec_path cfg [(lbl, idx)] = T ∧
  cfg_exec_path cfg ((lbl1, idx1) :: (lbl2, idx2) :: rest) =
    (((lbl1 = lbl2 ∧ idx2 = idx1 + 1) ∨
      (MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0)) ∧
     cfg_exec_path cfg ((lbl2, idx2) :: rest))
End

Definition var_used_at_def:
  var_used_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      MEM v (inst_uses inst))
End

Definition var_defined_at_def:
  var_defined_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      inst.inst_opcode ≠ PHI ∧
      MEM v (inst_defs inst))
End

Definition used_before_defined_def:
  used_before_defined bbs v positions =
    (∃k. k < LENGTH positions ∧
         var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
         ∀j. j < k ==>
             ¬var_defined_at bbs (FST (EL j positions))
                                 (SND (EL j positions)) v)
End

(* FMP lowering emits hidden parameters as ordinary def/use instructions. *)
Theorem fmp_hidden_param_defs_uses:
  (inst_uses (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) = [] /\
   inst_defs (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) = [v]) /\
  (inst_uses (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) = [] /\
   inst_defs (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) = [v])
Proof
  simp[mk_inst_def, inst_uses_def, inst_defs_def, operand_vars_def,
       operand_var_def]
QED

Theorem fmp_hidden_param_liveness_transfer:
  (liveness_transfer bbs
     (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) live =
   FILTER (\x. x <> v) live) /\
  (liveness_transfer bbs
     (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) live =
   FILTER (\x. x <> v) live)
Proof
  simp[liveness_transfer_def, live_update_def, ordered_inst_uses_def,
       python_stack_operands_def, ir_specific_operand_order_def, mk_inst_def,
       inst_uses_def, inst_defs_def, operand_vars_def, operand_var_def]
QED

Theorem fmp_lowered_generated_defs_uses:
  (inst_uses (mk_inst id INITIAL_FMP [] [v]) = [] /\
   inst_defs (mk_inst id INITIAL_FMP [] [v]) = [v]) /\
  (inst_uses (mk_inst id' BUMP [Var fmp; Lit (n2w k)] [out]) = [fmp] /\
   inst_defs (mk_inst id' BUMP [Var fmp; Lit (n2w k)] [out]) = [out])
Proof
  simp[mk_inst_def, inst_uses_def, inst_defs_def, operand_vars_def,
       operand_var_def]
QED

(* Computational interface probes: overwrite, empty blocks and set scheduling. *)
Theorem liveness_recompute_probe[local]:
  let cfg = <| cfg_succs := FEMPTY |+ ("b", ["s"]);
               cfg_preds := FEMPTY; cfg_reachable := FEMPTY;
               cfg_dfs_post := []; cfg_dfs_pre := [] |> in
  let bbs = [<| bb_label := "b";
                bb_instructions := [mk_inst 0 ADD [Var "x"; Var "y"] ["z"]] |>] in
  let old = <| ds_inst := FEMPTY |+ (("b",0),["stale"])
                               |+ (("b",1),["stale"])
                               |+ (("s",0),["z";"w"]);
               ds_boundary := FEMPTY |+ ("b",["stale"]) |> in
  let new = liveness_block bbs cfg "b" old in
  df_at [] new "b" 1 = ["z";"w"] /\
  df_at [] new "b" 0 = ["w";"y";"x"] /\
  df_boundary [] new "b" = ["w";"y";"x"] /\
  df_at [] new "s" 0 = ["z";"w"] /\
  liveness_changed bbs "b" old new
Proof
  EVAL_TAC
QED

Theorem liveness_empty_order_probe[local]:
  let cfg = <| cfg_succs := FEMPTY |+ ("b", ["s"]);
               cfg_preds := FEMPTY |+ ("b", ["p"]);
               cfg_reachable := FEMPTY;
               cfg_dfs_post := []; cfg_dfs_pre := [] |> in
  let bbs = [<| bb_label := "b"; bb_instructions := [] |>] in
  let old = <| ds_inst := FEMPTY |+ (("b",0),["x";"y"])
                               |+ (("s",0),["y";"x"]);
               ds_boundary := FEMPTY |+ ("b",["x";"y"]) |> in
  let new = liveness_block bbs cfg "b" old in
  df_at [] new "b" 0 = ["y";"x"] /\
  df_boundary [] new "b" = ["y";"x"] /\
  ~liveness_changed bbs "b" old new /\
  FST (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
               (cfg_preds_of cfg) (["b"],old)) = []
Proof
  EVAL_TAC
QED

Theorem liveness_cycle_probe[local]:
  let fn = mk_raw_function "cycle"
    [<| bb_label := "b";
        bb_instructions := [mk_inst 0 ADD [Var "x"; Var "y"] ["z"];
                            mk_inst 1 JMP [Label "b"] []] |>] in
  let st = liveness_recompute_fuel 4 fn in
  df_at [] st "b" 0 = ["y";"x"] /\
  df_at [] st "b" 2 = ["y";"x"] /\
  df_boundary [] st "b" = ["y";"x"]
Proof
  EVAL_TAC
QED

Theorem liveness_acyclic_probe[local]:
  let fn = mk_raw_function "acyclic"
    [<| bb_label := "b";
        bb_instructions := [mk_inst 0 JMP [Label "s"] []] |>;
     <| bb_label := "s";
        bb_instructions := [mk_inst 1 SINK [Var "x"] []] |>] in
  let st = liveness_recompute_fuel 4 fn in
  df_at [] st "b" 0 = ["x"] /\
  df_at [] st "b" 1 = ["x"] /\
  df_at [] st "s" 0 = ["x"] /\
  df_boundary [] st "b" = ["x"] /\
  df_at [] (liveness_recompute_fuel 0 fn) "s" 0 = []
Proof
  EVAL_TAC
QED
