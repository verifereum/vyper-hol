(*
 * MakeSSA pass — definitions.
 *
 * Converts a function into SSA form over the canonical CFG, dominator and
 * liveness analyses, with fresh names drawn from the IR supply:
 *   1. compute_defs: the blocks that define each variable
 *   2. PHI insertion at dominance frontiers, pruned by liveness
 *   3. renaming along the dominator tree
 *   4. degenerate-PHI cleanup
 *
 * Upstream: vyperlang/vyper venom/passes/make_ssa.py
 *)

Theory makeSsaDefs
Ancestors
  cfgTransform venomWf cfgDefs dominatorDefs livenessDefs irSupply
  list rich_list alist

(* ===== Dominator Tree ===== *)

Datatype:
  dom_tree = DNode string (dom_tree list)
End

(* Tree/list induction for clients reasoning about a tree and its forest. *)
Theorem dom_tree_list_induction:
  ∀P Q.
    (∀s children. Q children ⇒ P (DNode s children)) ∧
    Q [] ∧ (∀dtree children. P dtree ∧ Q children ⇒ Q (dtree::children)) ⇒
    (∀tree. P tree) ∧ (∀children. Q children)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops (TypeBase.induction_of ``:dom_tree``)) >>
  metis_tac[]
QED

(* All labels in a dominator tree. *)
Definition dom_tree_labels_def:
  dom_tree_labels (DNode lbl children) =
    lbl :: FLAT (MAP dom_tree_labels children)
End


(* ===== Definition Points ===== *)

(* All variables assigned in a block. *)
Definition block_assignments_def:
  block_assignments bb =
    nub (FLAT (MAP (λinst. inst.inst_outputs) bb.bb_instructions))
End

(* Update an assoc list entry in place: if key exists, update its value
   without changing its position. If not, append it at the end. *)
Definition alist_update_or_append_def:
  alist_update_or_append key f default [] = [(key, default)] ∧
  alist_update_or_append key f default ((k,v)::rest) =
    if k = key then (k, f v) :: rest
    else (k,v) :: alist_update_or_append key f default rest
End

(* Compute definition points: for each variable, the block labels where it
   is assigned. Returns assoc list: (var, [block_label]).
   Mirrors Python make_ssa._compute_defs: blocks in the given (dominator
   post-) order, variables in first-seen order (dict insertion order). Each
   variable's labels are in reverse block order, because
   insert_phis_for_var takes the head where Python's worklist pops the last.
   The fold runs over the raw outputs rather than block_assignments, whose
   nub keeps the last occurrence of a repeated variable. A variable assigned
   twice in a block gets that block's label twice; the repeat is a no-op in
   insert_phis_for_var, since all its frontiers are then in has_phi. *)
Definition compute_defs_acc_def:
  compute_defs_acc acc [] = acc ∧
  compute_defs_acc acc (bb::bbs) =
    compute_defs_acc
      (FOLDL (λacc var.
         alist_update_or_append var (CONS bb.bb_label) [bb.bb_label] acc)
       acc (FLAT (MAP (λinst. inst.inst_outputs) bb.bb_instructions)))
      bbs
End

Definition compute_defs_def:
  compute_defs bbs = compute_defs_acc [] bbs
End

(* Order-insensitive facts about compute_defs: its keys, distinctness of
   keys, and that every defining block is recorded. *)

Theorem alist_update_or_append_keys:
  ∀al k f d v.
    MEM v (MAP FST (alist_update_or_append k f d al)) ⇔
    v = k ∨ MEM v (MAP FST al)
Proof
  Induct >> simp[alist_update_or_append_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  rw[alist_update_or_append_def] >> metis_tac[]
QED

Theorem alist_update_or_append_alookup:
  ∀al k f d k'.
    ALOOKUP (alist_update_or_append k f d al) k' =
    if k' = k then SOME (case ALOOKUP al k of SOME v => f v | NONE => d)
    else ALOOKUP al k'
Proof
  Induct >- rw[alist_update_or_append_def] >>
  Cases >> rw[alist_update_or_append_def] >> gvs[]
QED

Theorem alist_update_or_append_all_distinct:
  ∀al k f d.
    ALL_DISTINCT (MAP FST al) ⇒
    ALL_DISTINCT (MAP FST (alist_update_or_append k f d al))
Proof
  Induct >- rw[alist_update_or_append_def] >>
  Cases >> rw[alist_update_or_append_def, alist_update_or_append_keys] >>
  gvs[]
QED

Triviality foldl_update_keys:
  ∀vars acc f d v.
    MEM v (MAP FST (FOLDL (λacc var. alist_update_or_append var f d acc)
                     acc vars)) ⇔
    MEM v (MAP FST acc) ∨ MEM v vars
Proof
  Induct >> simp[alist_update_or_append_keys] >> metis_tac[]
QED

Triviality foldl_update_all_distinct:
  ∀vars acc f d.
    ALL_DISTINCT (MAP FST acc) ⇒
    ALL_DISTINCT (MAP FST
      (FOLDL (λacc var. alist_update_or_append var f d acc) acc vars))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[alist_update_or_append_all_distinct]
QED

Triviality foldl_update_preserves:
  ∀vars acc lbl var dbs.
    ALOOKUP acc var = SOME dbs ⇒
    ∃dbs'.
      ALOOKUP (FOLDL (λacc v. alist_update_or_append v (CONS lbl) [lbl] acc)
                 acc vars) var = SOME dbs' ∧
      ∀x. MEM x dbs ⇒ MEM x dbs'
Proof
  Induct >- (simp[] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  `∃d1. ALOOKUP (alist_update_or_append h (CONS lbl) [lbl] acc) var =
          SOME d1 ∧ ∀x. MEM x dbs ⇒ MEM x d1`
    by (rw[alist_update_or_append_alookup] >> gvs[]) >>
  first_x_assum (drule_then (qspec_then `lbl` strip_assume_tac)) >>
  metis_tac[]
QED

Triviality foldl_update_records:
  ∀vars acc lbl var.
    MEM var vars ⇒
    ∃dbs.
      ALOOKUP (FOLDL (λacc v. alist_update_or_append v (CONS lbl) [lbl] acc)
                 acc vars) var = SOME dbs ∧
      MEM lbl dbs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac
  >- (`∃d1. ALOOKUP (alist_update_or_append h (CONS lbl) [lbl] acc) var =
             SOME d1 ∧ MEM lbl d1`
        by (gvs[alist_update_or_append_alookup] >> CASE_TAC >> simp[]) >>
      drule_then (qspecl_then [`vars`, `lbl`] strip_assume_tac)
        foldl_update_preserves >>
      metis_tac[])
  >> first_x_assum irule >> simp[]
QED

Theorem compute_defs_acc_keys:
  ∀bbs acc v.
    MEM v (MAP FST (compute_defs_acc acc bbs)) ⇔
    MEM v (MAP FST acc) ∨ MEM v (FLAT (MAP block_assignments bbs))
Proof
  Induct >>
  simp[compute_defs_acc_def, foldl_update_keys, block_assignments_def,
       MEM_nub] >>
  metis_tac[]
QED

Theorem compute_defs_acc_all_distinct:
  ∀bbs acc.
    ALL_DISTINCT (MAP FST acc) ⇒
    ALL_DISTINCT (MAP FST (compute_defs_acc acc bbs))
Proof
  Induct >> simp[compute_defs_acc_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[foldl_update_all_distinct]
QED

Triviality compute_defs_acc_preserves:
  ∀bbs acc var dbs.
    ALOOKUP acc var = SOME dbs ⇒
    ∃dbs'. ALOOKUP (compute_defs_acc acc bbs) var = SOME dbs' ∧
           ∀x. MEM x dbs ⇒ MEM x dbs'
Proof
  Induct >- (simp[compute_defs_acc_def] >> metis_tac[]) >>
  rpt strip_tac >> simp[compute_defs_acc_def] >>
  drule_then (qspecl_then [`FLAT (MAP (λinst. inst.inst_outputs)
                                      h.bb_instructions)`, `h.bb_label`]
    strip_assume_tac) foldl_update_preserves >>
  first_x_assum drule >> metis_tac[]
QED

Theorem compute_defs_acc_complete:
  ∀bbs acc bb var.
    MEM bb bbs ∧ MEM var (block_assignments bb) ⇒
    ∃dbs. ALOOKUP (compute_defs_acc acc bbs) var = SOME dbs ∧
          MEM bb.bb_label dbs
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[compute_defs_acc_def] >>
  Cases_on `MEM bb bbs` >- (first_x_assum irule >> simp[]) >>
  `bb = h` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  gvs[block_assignments_def, MEM_nub] >>
  drule_then (qspecl_then [`acc`, `h.bb_label`] strip_assume_tac)
    foldl_update_records >>
  drule compute_defs_acc_preserves >> metis_tac[]
QED

Theorem compute_defs_keys:
  ∀bbs v.
    MEM v (MAP FST (compute_defs bbs)) ⇔
    MEM v (FLAT (MAP block_assignments bbs))
Proof
  simp[compute_defs_def, compute_defs_acc_keys]
QED

Theorem compute_defs_all_distinct:
  ∀bbs. ALL_DISTINCT (MAP FST (compute_defs bbs))
Proof
  simp[compute_defs_def, compute_defs_acc_all_distinct]
QED

Theorem compute_defs_complete:
  ∀bbs bb var.
    MEM bb bbs ∧ MEM var (block_assignments bb) ⇒
    ∃dbs. ALOOKUP (compute_defs bbs) var = SOME dbs ∧ MEM bb.bb_label dbs
Proof
  simp[compute_defs_def, compute_defs_acc_complete]
QED

Theorem compute_defs_every_key:
  ∀P bbs.
    (∀bb. MEM bb bbs ⇒ EVERY P (block_assignments bb)) ⇒
    EVERY (λp. P (FST p)) (compute_defs bbs)
Proof
  rw[EVERY_MEM, pairTheory.FORALL_PROD] >>
  `MEM p_1 (MAP FST (compute_defs bbs))`
    by (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  gvs[compute_defs_keys, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

(* Regression (#561, a14-02): keys in first-seen order across blocks and
   within a block, as Python's dict; labels in reverse block order. The
   previous FOLDR version gave [x; z; y] with x's labels [b1; b2]. *)
Theorem compute_defs_first_seen_order:
  compute_defs
    [<| bb_label := "b1";
        bb_instructions := [mk_inst 0 ASSIGN [] ["x"];
                            mk_inst 1 ASSIGN [] ["y"]] |>;
     <| bb_label := "b2";
        bb_instructions := [mk_inst 2 ASSIGN [] ["z"];
                            mk_inst 3 ASSIGN [] ["x"]] |>] =
  [("x", ["b2"; "b1"]); ("y", ["b1"]); ("z", ["b2"])]
Proof
  EVAL_TAC
QED

(* A variable reassigned in its block keeps its first position, as in
   Python; nub would keep the last and give [y; x]. *)
Theorem compute_defs_first_seen_in_block:
  compute_defs
    [<| bb_label := "b1";
        bb_instructions := [mk_inst 0 ASSIGN [] ["x"];
                            mk_inst 1 ASSIGN [] ["y"];
                            mk_inst 2 ASSIGN [] ["x"]] |>] =
  [("x", ["b1"; "b1"]); ("y", ["b1"])]
Proof
  EVAL_TAC
QED

(* ===== PHI Node Insertion ===== *)

(* Build a PHI instruction for a variable at a block.
   PHI operands: [Label pred1, Var x, Label pred2, Var x, ...]
   where preds are the predecessors of the block. *)
Definition build_phi_inst_def:
  build_phi_inst var pred_labels =
    <| inst_id := 0;  (* placeholder — renumbered later *)
       inst_opcode := PHI;
       inst_operands :=
         FLAT (MAP (λl. [Label l; Var var]) pred_labels);
       inst_outputs := [var]
    |>
End

(* Insert a PHI instruction at the start of a block. *)
Definition insert_phi_at_block_def:
  insert_phi_at_block phi_inst bb =
    bb with bb_instructions := phi_inst :: bb.bb_instructions
End

(* A finite association-list view of a query function, in function-label
   order.  This is the only conversion used by the current-analysis bridge. *)
Definition current_query_map_def:
  current_query_map labels query = MAP (\l. (l, query l)) labels
End

Definition current_pred_map_def:
  current_pred_map fn =
    current_query_map (fn_labels fn) (cfg_preds_of (cfg_analyze fn))
End

Definition current_succ_map_def:
  current_succ_map fn =
    current_query_map (fn_labels fn) (cfg_succs_of (cfg_analyze fn))
End

Definition current_frontier_map_def:
  current_frontier_map fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      current_query_map (fn_labels fn) (frontier_of dom)
End

Definition current_live_in_def:
  current_live_in fn =
    let live = liveness_analyze fn in
      current_query_map (fn_labels fn) (df_boundary [] live)
End

(* Build the dominator tree from the canonical dominated-children query.
   Fuel makes this executable independently of analysis correctness. *)
Definition current_dom_tree_aux_def:
  (current_dom_tree_aux dom 0 lbl = DNode lbl []) /\
  (current_dom_tree_aux dom (SUC fuel) lbl =
     DNode lbl
       (MAP (current_dom_tree_aux dom fuel) (dominated_of dom lbl)))
End

Definition current_dom_tree_def:
  current_dom_tree fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      case fn_entry_label fn of
        NONE => DNode "" []
      | SOME entry => current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry
End

(* Structural postorder of the dominator tree (children left-to-right, then
   the node), rather than the CFG DFS postorder. *)
Definition dom_tree_postorder_def:
  dom_tree_postorder (DNode lbl children) =
    FLAT (MAP dom_tree_postorder children) ++ [lbl]
End

Definition current_dom_postorder_def:
  current_dom_postorder fn = dom_tree_postorder (current_dom_tree fn)
End

(* ===== Supply-aware PHI insertion ===== *)

(* The ID is supplied explicitly by fresh_inst_id at the unique insertion
   point; this constructor contains no placeholder or arithmetic ID. *)
Definition build_phi_inst_supply_def:
  build_phi_inst_supply id var pred_labels =
    <| inst_id := id;
       inst_opcode := PHI;
       inst_operands := FLAT (MAP (\l. [Label l; Var var]) pred_labels);
       inst_outputs := [var] |>
End

Definition process_frontiers_supply_def:
  process_frontiers_supply s var pred_map live_in bbs rest has_phi [] =
    (bbs, rest, has_phi, s) /\
  process_frontiers_supply s var pred_map live_in bbs rest has_phi (f::fs) =
    if MEM f has_phi then
      process_frontiers_supply s var pred_map live_in bbs rest has_phi fs
    else
      let is_live = case ALOOKUP live_in f of
                      SOME vars => MEM var vars
                    | NONE => F in
      if ~is_live then
        process_frontiers_supply s var pred_map live_in bbs rest
                                 (f::has_phi) fs
      else
        let preds = case ALOOKUP pred_map f of SOME ps => ps | NONE => [] in
        let (id,s') = fresh_inst_id s in
        let phi = build_phi_inst_supply id var preds in
        let bbs' = MAP (\bb.
          if bb.bb_label = f then insert_phi_at_block phi bb else bb) bbs in
          process_frontiers_supply s' var pred_map live_in bbs'
                                   (f::rest) (f::has_phi) fs
End

Theorem process_frontiers_supply_labels:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >>
  rw[MAP_MAP_o, insert_phi_at_block_def] >>
  irule MAP_CONG >> rw[]
QED

Triviality filter_add_mem_decrease_supply:
  !U (h:'a) hp.
    MEM h U /\ ~MEM h hp /\ ALL_DISTINCT U ==>
    LENGTH (FILTER (\x. ~MEM x (h::hp)) U) + 1 <=
    LENGTH (FILTER (\x. ~MEM x hp) U)
Proof
  Induct >> simp[ALL_DISTINCT] >> rpt strip_tac >> gvs[]
  >- (
    `LENGTH (FILTER (\x. x <> h /\ ~MEM x hp) U) <=
     LENGTH (FILTER (\x. ~MEM x hp) U)` suffices_by DECIDE_TAC >>
    irule LENGTH_FILTER_LEQ_MONO >> simp[])
  >- (
    Cases_on `MEM h hp`
    >- (`~(h <> h' /\ ~MEM h hp)` by simp[] >>
        `~(~MEM h hp)` by simp[] >>
        simp[] >> first_x_assum drule_all >> simp[])
    >- (`h <> h'` by metis_tac[MEM] >>
        simp[LENGTH] >> first_x_assum drule_all >> DECIDE_TAC))
QED

Triviality filter_weaken_exclusion_supply:
  !(U:'a list) hp1 hp2.
    (!x. MEM x hp1 ==> MEM x hp2) ==>
    LENGTH (FILTER (\x. ~MEM x hp2) U) <=
    LENGTH (FILTER (\x. ~MEM x hp1) U)
Proof
  Induct >> rw[FILTER] >> gvs[] >> res_tac >> DECIDE_TAC
QED

Triviality process_frontiers_supply_measure:
  !fs s var pm li bbs rest hp bbs' rest' hp' s' U.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    (!f. MEM f fs ==> MEM f U) ==>
    ALL_DISTINCT U ==>
    LENGTH (FILTER (\x. ~MEM x hp') U) + LENGTH rest' <=
    LENGTH (FILTER (\x. ~MEM x hp) U) + LENGTH rest
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (
    rpt strip_tac >>
    `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
    asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
    simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (
    rpt strip_tac >>
    `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
    asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `LENGTH (FILTER (\x. ~MEM x (h::hp)) U) <=
     LENGTH (FILTER (\x. ~MEM x hp) U)` by
      (irule filter_weaken_exclusion_supply >> simp[]) >>
    DECIDE_TAC)
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
  asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MEM h U` by metis_tac[] >>
  `LENGTH (FILTER (\x. ~MEM x (h::hp)) U) + 1 <=
   LENGTH (FILTER (\x. ~MEM x hp) U)` by
    (irule filter_add_mem_decrease_supply >> simp[]) >>
  gvs[LENGTH] >> DECIDE_TAC
QED


Definition frontier_work_needed_def:
  frontier_work_needed dom_frontiers has_phi d =
    case ALOOKUP dom_frontiers d of
      NONE => F
    | SOME fs => EXISTS (\f. ~MEM f has_phi) fs
End

Definition insert_phis_for_var_supply_def:
  insert_phis_for_var_supply s var dom_frontiers pred_map live_in bbs [] has_phi =
    (bbs,s) /\
  insert_phis_for_var_supply s var dom_frontiers pred_map live_in bbs
                             (d::rest) has_phi =
    let frontiers = case ALOOKUP dom_frontiers d of
                      SOME fs => fs | NONE => [] in
    let (bbs',rest',has_phi',s') =
      process_frontiers_supply s var pred_map live_in bbs rest has_phi
                               frontiers in
    let work = FILTER (frontier_work_needed dom_frontiers has_phi') rest' in
      insert_phis_for_var_supply s' var dom_frontiers pred_map live_in
                                 bbs' work has_phi'
Termination
  WF_REL_TAC `measure (\(s,var,df,pm,li,bbs,wl,hp).
    LENGTH (FILTER (\x. ~MEM x hp)
      (nub (MAP (\bb. bb.bb_label) bbs ++ FLAT (MAP SND df)))) +
    LENGTH wl)` >>
  rpt strip_tac >>
  rename1 `(bbs',rest',has_phi',next_supply) =
    process_frontiers_supply s var pred_map live_in bbs rest has_phi _` >>
  qabbrev_tac `fs = case ALOOKUP dom_frontiers d of
                      NONE => [] | SOME x => x` >>
  qabbrev_tac `U = nub (MAP (\bb. bb.bb_label) bbs ++
                         FLAT (MAP SND dom_frontiers))` >>
  qabbrev_tac `result = process_frontiers_supply s var pred_map live_in
                          bbs rest has_phi fs` >>
  `result = (bbs',rest',has_phi',next_supply)` by
    simp[Abbr `result`, Abbr `fs`] >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  `process_frontiers_supply s var pred_map live_in bbs rest has_phi fs =
   (bbs',rest',has_phi',next_supply)` by gvs[markerTheory.Abbrev_def] >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs` by
    (irule process_frontiers_supply_labels >> metis_tac[]) >>
  `nub (MAP (\bb. bb.bb_label) bbs' ++ FLAT (MAP SND dom_frontiers)) = U` by
    simp[Abbr `U`] >>
  gvs[] >>
  `!f. MEM f fs ==> MEM f U` by (
    unabbrev_all_tac >> rpt strip_tac >>
    Cases_on `ALOOKUP dom_frontiers d` >> gvs[] >>
    simp[MEM_nub, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
    disj2_tac >> qexists_tac `x` >> simp[] >>
    qexists_tac `(d,x)` >> simp[] >> metis_tac[ALOOKUP_MEM]) >>
  `ALL_DISTINCT U` by simp[Abbr `U`, all_distinct_nub] >>
  `LENGTH (FILTER (\x. ~MEM x has_phi') U) + LENGTH rest' <=
   LENGTH (FILTER (\x. ~MEM x has_phi) U) + LENGTH rest` by
    metis_tac[process_frontiers_supply_measure] >>
  `LENGTH (FILTER (frontier_work_needed dom_frontiers has_phi') rest') <=
   LENGTH rest'` by simp[rich_listTheory.LENGTH_FILTER_LEQ] >>
  DECIDE_TAC
End

Definition add_phi_nodes_supply_def:
  (add_phi_nodes_supply s dom_frontiers pred_map live_in bbs [] = (bbs,s)) /\
  (add_phi_nodes_supply s dom_frontiers pred_map live_in bbs
                        ((var,def_blocks)::defs) =
    let (bbs',s') = insert_phis_for_var_supply s var dom_frontiers pred_map
                                                live_in bbs def_blocks [] in
      add_phi_nodes_supply s' dom_frontiers pred_map live_in bbs' defs)
End

(* ===== Supply-aware concrete-name renaming ===== *)

Definition init_current_rename_state_def:
  init_current_rename_state defs =
    let vars = MAP FST defs in
      (MAP (\v. (v,0n)) vars, MAP (\v. (v,[v])) vars)
End

Definition latest_current_name_def:
  latest_current_name
    (counters : (string # num) list, stacks : (string # string list) list) var =
    case ALOOKUP stacks var of SOME (name::_) => name | _ => var
End

(* Counter zero is the original spelling and consumes no supply.  Every later
   definition gets its concrete spelling directly from fresh_ir_var. *)
Definition push_current_name_def:
  push_current_name s
    (counters : (string # num) list, stacks : (string # string list) list) var =
    let n = case ALOOKUP counters var of SOME k => k | NONE => 0n in
    let counters' = (var,n+1)::FILTER (\(v,_). v <> var) counters in
    if n = 0 then
      let stacks' = (var,var::case ALOOKUP stacks var of
                                SOME ns => ns | NONE => []) ::
                    FILTER (\(v,_). v <> var) stacks in
        ((counters',stacks'),s,var)
    else
      let (name,s') = fresh_ir_var s in
      let stacks' = (var,name::case ALOOKUP stacks var of
                                  SOME ns => ns | NONE => []) ::
                    FILTER (\(v,_). v <> var) stacks in
        ((counters',stacks'),s',name)
End

Definition rename_current_operands_def:
  (rename_current_operands rs [] = []) /\
  (rename_current_operands rs (Var v::ops) =
    Var (latest_current_name rs v)::rename_current_operands rs ops) /\
  (rename_current_operands rs (op::ops) =
    op::rename_current_operands rs ops)
End

Definition rename_current_outputs_def:
  (rename_current_outputs s rs [] = (rs,s,[]:string list)) /\
  (rename_current_outputs s rs (v::vs) =
    let (rs',s',name) = push_current_name s rs v in
    let (rs'',s'',rest) = rename_current_outputs s' rs' vs in
      (rs'',s'',name::rest))
End

Definition rename_current_inst_def:
  rename_current_inst s rs inst =
    if inst.inst_opcode = PHI then
      let (rs',s',outs') = rename_current_outputs s rs inst.inst_outputs in
        (rs',s',inst with inst_outputs := outs')
    else
      let ops' = rename_current_operands rs inst.inst_operands in
      let (rs',s',outs') = rename_current_outputs s rs inst.inst_outputs in
        (rs',s',inst with <| inst_operands := ops'; inst_outputs := outs' |>)
End

Definition rename_current_block_insts_def:
  (rename_current_block_insts s rs [] = (rs,s,[])) /\
  (rename_current_block_insts s rs (inst::rest) =
    let (rs',s',inst') = rename_current_inst s rs inst in
    let (rs'',s'',rest') = rename_current_block_insts s' rs' rest in
      (rs'',s'',inst'::rest'))
End

Definition update_current_phi_for_pred_def:
  (update_current_phi_for_pred rs current_label [] = []) /\
  (update_current_phi_for_pred rs current_label [x] = [x]) /\
  (update_current_phi_for_pred rs current_label (Label l::Var v::rest) =
    (if l = current_label
     then Label l::Var (latest_current_name rs v)::
          update_current_phi_for_pred rs current_label rest
     else Label l::Var v::update_current_phi_for_pred rs current_label rest)) /\
  (update_current_phi_for_pred rs current_label (x::y::rest) =
    x::y::update_current_phi_for_pred rs current_label rest)
End

Definition update_current_succ_phis_def:
  update_current_succ_phis rs current_label bbs succs =
    FOLDL (\bs lbl.
      case lookup_block lbl bs of
        NONE => bs
      | SOME bb =>
          let bb' = bb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else inst with inst_operands :=
                          update_current_phi_for_pred rs current_label
                                                      inst.inst_operands)
                bb.bb_instructions in
            replace_block lbl bb' bs) bbs succs
End

Definition rename_current_blocks_def:
  (rename_current_blocks s rs bbs succ_map (DNode lbl children) =
    case lookup_block lbl bbs of
      NONE => (FST rs,s,bbs)
    | SOME bb =>
        let (rs1,s1,insts') =
          rename_current_block_insts s rs bb.bb_instructions in
        let bb' = bb with bb_instructions := insts' in
        let bbs1 = replace_block lbl bb' bbs in
        let succs = case ALOOKUP succ_map lbl of SOME ss => ss | NONE => [] in
        let bbs2 = update_current_succ_phis rs1 lbl bbs1 succs in
          rename_current_children s1 (FST rs1) (SND rs1) bbs2 succ_map
                                  children) /\
  (rename_current_children s ctrs stacks bbs succ_map [] = (ctrs,s,bbs)) /\
  (rename_current_children s ctrs stacks bbs succ_map (child::rest) =
    let (ctrs',s',bbs') =
      rename_current_blocks s (ctrs,stacks) bbs succ_map child in
      rename_current_children s' ctrs' stacks bbs' succ_map rest)
End

(* Python's liveness_in_vars deliberately skips leading PHIs.  MakeSSA uses
   the liveness immediately before the first ordinary instruction when
   deciding whether another PHI is needed on a repeated SSA run. *)
(* Build the finite liveness map directly from blocks.  In particular, the
   common first-SSA case with no leading PHI reduces immediately to the old
   index-zero query without repeatedly looking the block up in the function. *)
Definition current_live_in_after_phis_def:
  current_live_in_after_phis live [] = [] /\
  current_live_in_after_phis live (bb::bbs) =
    (bb.bb_label,
     case bb.bb_instructions of
       [] => ([] : string list)
     | inst::rest =>
         if inst.inst_opcode = PHI then
           live_vars_at live bb.bb_label
             (LENGTH (collect_phis bb.bb_instructions))
         else live_vars_at live bb.bb_label 0) ::
    current_live_in_after_phis live bbs
End

Definition blocks_have_leading_phi_def:
  blocks_have_leading_phi [] = F /\
  blocks_have_leading_phi (bb::bbs) =
    (case bb.bb_instructions of
       [] => blocks_have_leading_phi bbs
     | inst::_ => inst.inst_opcode = PHI \/ blocks_have_leading_phi bbs)
End

Definition select_current_live_in_def:
  select_current_live_in F live fn =
    current_query_map (fn_labels fn) (df_boundary [] live) /\
  select_current_live_in T live fn =
    current_live_in_after_phis live fn.fn_blocks
End

(* Mirror Python's degenerate-PHI cleanup while preserving definitions and
   instruction IDs: when the non-self inputs are all equal the PHI collapses
   to an ASSIGN (no inputs: a NOP); otherwise it is kept as it is. *)
Definition current_phi_output_def:
  current_phi_output [out] = SOME out /\
  current_phi_output _ = NONE
End

Definition remove_current_phi_self_def:
  remove_current_phi_self out [] = [] /\
  remove_current_phi_self out [x] = [x] /\
  remove_current_phi_self out (Label l::Var v::rest) =
    (if v = out then remove_current_phi_self out rest
     else Label l::Var v::remove_current_phi_self out rest) /\
  remove_current_phi_self out (x::y::rest) =
    x::y::remove_current_phi_self out rest
End

Definition current_phi_values_def:
  current_phi_values [] = SOME ([] : string list) /\
  current_phi_values (Label l::Var v::rest) =
    (case current_phi_values rest of
       NONE => NONE
     | SOME vs => SOME (v::vs)) /\
  current_phi_values _ = NONE
End

Definition simplify_current_phi_raw_def:
  simplify_current_phi_raw inst =
    if inst.inst_opcode <> PHI then inst
    else case current_phi_output inst.inst_outputs of
      NONE => inst
    | SOME out =>
        let cleaned = remove_current_phi_self out inst.inst_operands in
        case current_phi_values cleaned of
          NONE => inst
        | SOME [] =>
            inst with <| inst_opcode := NOP; inst_operands := [];
                         inst_outputs := [] |>
        | SOME (v::vs) =>
            if EVERY (\w. w = v) vs then
              inst with <| inst_opcode := ASSIGN;
                           inst_operands := [Var v] |>
            (* A PHI that stays a PHI keeps its self edges: eval_one_phi
               needs an operand for every incoming edge. *)
            else inst
End

Definition keep_current_phi_vars_def:
  keep_current_phi_vars original candidate =
    if EVERY (\v. MEM v (inst_ir_vars original))
             (inst_ir_vars candidate)
    then candidate
    else original
End

Definition simplify_current_phi_def:
  simplify_current_phi inst =
    keep_current_phi_vars inst (simplify_current_phi_raw inst)
End

Definition simplify_current_phi_prefix_parts_def:
  simplify_current_phi_prefix_parts [] = ([],[]) /\
  simplify_current_phi_prefix_parts (inst::rest) =
    if inst.inst_opcode <> PHI then ([],inst::rest)
    else
      let inst' = simplify_current_phi inst in
      let (phis,ordinary) = simplify_current_phi_prefix_parts rest in
        if inst'.inst_opcode = PHI then (inst'::phis,ordinary)
        else (phis,inst'::ordinary)
End

Definition reassign_current_inst_ids_def:
  reassign_current_inst_ids [] insts = insts /\
  reassign_current_inst_ids ids [] = [] /\
  reassign_current_inst_ids (id::ids) (inst::insts) =
    (inst with inst_id := id)::reassign_current_inst_ids ids insts
End

Definition simplify_current_phi_prefix_def:
  simplify_current_phi_prefix insts =
    let (phis,ordinary) = simplify_current_phi_prefix_parts insts in
      reassign_current_inst_ids (MAP (\inst. inst.inst_id) insts)
        (phis ++ ordinary)
End

Definition simplify_current_phi_block_def:
  simplify_current_phi_block bb =
    case bb.bb_instructions of
      [] => bb
    | inst::rest =>
        if inst.inst_opcode = PHI then
          bb with bb_instructions :=
            simplify_current_phi_prefix bb.bb_instructions
        else bb
End

Definition simplify_current_phis_def:
  simplify_current_phis bbs =
    if blocks_have_leading_phi bbs then
      MAP simplify_current_phi_block bbs
    else bbs
End

Definition simplify_current_phis_if_def:
  simplify_current_phis_if enabled bbs =
    if enabled then simplify_current_phis bbs else bbs
End

Theorem simplify_current_phi_raw_id[simp]:
  (simplify_current_phi_raw inst).inst_id = inst.inst_id
Proof
  Cases_on `inst.inst_opcode <> PHI` >> simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  rename1 `current_phi_output inst.inst_outputs = SOME out` >>
  Cases_on `current_phi_values (remove_current_phi_self out inst.inst_operands)` >>
  simp[] >> rename1 `current_phi_values _ = SOME values` >>
  Cases_on `values` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem simplify_current_phi_id[simp]:
  (simplify_current_phi inst).inst_id = inst.inst_id
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  CASE_TAC >> simp[]
QED

Theorem simplify_current_phi_vars:
  MEM v (inst_ir_vars (simplify_current_phi inst)) ==>
  MEM v (inst_ir_vars inst)
Proof
  Cases_on `EVERY (\v. MEM v (inst_ir_vars inst))
                  (inst_ir_vars (simplify_current_phi_raw inst))`
  >- (simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
      fs[listTheory.EVERY_MEM]) >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def]
QED

Theorem simplify_current_phi_prefix_parts_length:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
    LENGTH phis + LENGTH ordinary = LENGTH insts
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >>
  pairarg_tac >> gvs[] >> CASE_TAC >> strip_tac >> gvs[]
QED

Theorem reassign_current_inst_ids_ids:
  !ids insts.
    LENGTH ids = LENGTH insts ==>
    MAP (\inst. inst.inst_id) (reassign_current_inst_ids ids insts) = ids
Proof
  Induct >> Cases_on `insts` >>
  simp[reassign_current_inst_ids_def]
QED

Theorem MAP_simplify_current_phi_prefix_ids[simp]:
  MAP (\inst. inst.inst_id) (simplify_current_phi_prefix insts) =
  MAP (\inst. inst.inst_id) insts
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule reassign_current_inst_ids_ids >>
  drule simplify_current_phi_prefix_parts_length >> simp[]
QED

Theorem simplify_current_phi_block_label[simp]:
  (simplify_current_phi_block bb).bb_label = bb.bb_label
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem MAP_simplify_current_phis_labels[simp]:
  MAP (\bb. bb.bb_label) (simplify_current_phis bbs) =
  MAP (\bb. bb.bb_label) bbs
Proof
  Cases_on `blocks_have_leading_phi bbs` >>
  simp[simplify_current_phis_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[]
QED

Theorem simplify_current_phi_block_ids[simp]:
  block_ir_inst_ids (simplify_current_phi_block bb) =
  block_ir_inst_ids bb
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >>
  gvs[block_ir_inst_ids_def]
QED

Theorem MAP_simplify_current_phis_inst_ids[simp]:
  MAP block_ir_inst_ids (simplify_current_phis bbs) =
  MAP block_ir_inst_ids bbs
Proof
  Cases_on `blocks_have_leading_phi bbs` >>
  simp[simplify_current_phis_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[]
QED

Theorem MAP_simplify_current_phis_if_labels[simp]:
  MAP (\bb. bb.bb_label) (simplify_current_phis_if enabled bbs) =
  MAP (\bb. bb.bb_label) bbs
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def]
QED

Theorem MAP_simplify_current_phis_if_inst_ids[simp]:
  MAP block_ir_inst_ids (simplify_current_phis_if enabled bbs) =
  MAP block_ir_inst_ids bbs
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def]
QED

Theorem reassign_current_inst_ids_vars:
  !ids insts.
    LENGTH ids = LENGTH insts ==>
    MAP inst_ir_vars (reassign_current_inst_ids ids insts) =
    MAP inst_ir_vars insts
Proof
  Induct >> Cases_on `insts` >>
  simp[reassign_current_inst_ids_def, inst_ir_vars_def,
       venomInstTheory.inst_uses_def]
QED

Theorem simplify_current_phi_prefix_parts_vars:
  !insts phis ordinary v.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    MEM v (FLAT (MAP inst_ir_vars (phis ++ ordinary))) ==>
    MEM v (FLAT (MAP inst_ir_vars insts))
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >>
  pairarg_tac >> gvs[] >> CASE_TAC >> strip_tac >> gvs[] >>
  metis_tac[simplify_current_phi_vars]
QED

Theorem simplify_current_phi_prefix_vars:
  MEM v (FLAT (MAP inst_ir_vars (simplify_current_phi_prefix insts))) ==>
  MEM v (FLAT (MAP inst_ir_vars insts))
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  `LENGTH (MAP (\inst. inst.inst_id) insts) =
   LENGTH (phis ++ ordinary)` by
    (drule simplify_current_phi_prefix_parts_length >> simp[]) >>
  drule_all reassign_current_inst_ids_vars >> strip_tac >> gvs[] >>
  strip_tac >>
  mp_tac (Q.SPECL [`insts`,`phis`,`ordinary`,`v`]
    simplify_current_phi_prefix_parts_vars) >> simp[]
QED

Theorem simplify_current_phi_block_vars:
  MEM v (block_ir_vars (simplify_current_phi_block bb)) ==>
  MEM v (block_ir_vars bb)
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >>
  gvs[block_ir_vars_def] >> strip_tac >>
  drule simplify_current_phi_prefix_vars >> simp[]
QED

Theorem simplify_current_phis_vars_subset:
  MEM v (FLAT (MAP block_ir_vars (simplify_current_phis bbs))) ==>
  MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  Cases_on `blocks_have_leading_phi bbs` >>
  gvs[simplify_current_phis_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[simplify_current_phi_block_vars]
QED

Theorem simplify_current_phis_if_vars_subset:
  MEM v (FLAT (MAP block_ir_vars (simplify_current_phis_if enabled bbs))) ==>
  MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  Cases_on `enabled` >> gvs[simplify_current_phis_if_def] >>
  metis_tac[simplify_current_phis_vars_subset]
QED

(* This boundary intentionally binds every analysis from this very fn. *)
Definition make_ssa_current_fn_def:
  make_ssa_current_fn s fn =
    case fn_entry_label fn of
      NONE => (fn,s)
    | SOME entry =>
        let cfg = cfg_analyze fn in
        let dom = dom_analyze cfg fn in
        let live = liveness_analyze fn in
        let had_phis = blocks_have_leading_phi fn.fn_blocks in
        let pred_map = current_query_map (fn_labels fn) (cfg_preds_of cfg) in
        let succ_map = current_query_map (fn_labels fn) (cfg_succs_of cfg) in
        let frontiers = current_query_map (fn_labels fn) (frontier_of dom) in
        let live_in = select_current_live_in had_phis live fn in
        let dtree = current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry in
        let postorder = dom_tree_postorder dtree in
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl fn.fn_blocks) postorder)) in
        let defs = compute_defs ordered_bbs in
        let (bbs1,s1) = add_phi_nodes_supply s frontiers pred_map live_in
                                             fn.fn_blocks defs in
        let rs0 = init_current_rename_state defs in
        let (_,s2,bbs2) = rename_current_blocks s1 rs0 bbs1 succ_map dtree in
        let bbs3 = simplify_current_phis_if had_phis bbs2 in
          (fn with fn_blocks := bbs3,s2)
End

Definition make_ssa_functions_supply_def:
  (make_ssa_functions_supply s [] = ([],s)) /\
  (make_ssa_functions_supply s (fn::fns) =
    let (fn',s') = make_ssa_current_fn s fn in
    let (fns',s'') = make_ssa_functions_supply s' fns in
      (fn'::fns',s''))
End

Definition make_ssa_ctx_supply_def:
  make_ssa_ctx_supply s ctx =
    let (fns,s') = make_ssa_functions_supply s ctx.ctx_functions in
      (ctx with ctx_functions := fns,s')
End

Definition make_ssa_unit_supply_def:
  make_ssa_unit_supply s unit =
    let (ctx,s') = make_ssa_ctx_supply s unit.cu_context in
      (unit with cu_context := ctx,s')
End

Definition make_ssa_configured_with_supply_def:
  make_ssa_configured_with_supply unit =
    make_ssa_unit_supply (init_ir_supply unit) unit
End

Definition make_ssa_configured_def:
  make_ssa_configured unit = FST (make_ssa_configured_with_supply unit)
End

Theorem make_ssa_configured_with_supply_eq:
  make_ssa_configured_with_supply unit =
    make_ssa_unit_supply (init_ir_supply unit) unit
Proof
  simp[make_ssa_configured_with_supply_def]
QED

Theorem make_ssa_configured_eq:
  make_ssa_configured unit = FST (make_ssa_configured_with_supply unit)
Proof
  simp[make_ssa_configured_def]
QED

Theorem make_ssa_current_fn_current_analysis_eq:
  make_ssa_current_fn s fn =
    case fn_entry_label fn of
      NONE => (fn,s)
    | SOME entry =>
        let cfg = cfg_analyze fn in
        let dom = dom_analyze cfg fn in
        let live = liveness_analyze fn in
        let had_phis = blocks_have_leading_phi fn.fn_blocks in
        let pred_map = current_query_map (fn_labels fn) (cfg_preds_of cfg) in
        let succ_map = current_query_map (fn_labels fn) (cfg_succs_of cfg) in
        let frontiers = current_query_map (fn_labels fn) (frontier_of dom) in
        let live_in = select_current_live_in had_phis live fn in
        let dtree = current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry in
        let postorder = dom_tree_postorder dtree in
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl fn.fn_blocks) postorder)) in
        let defs = compute_defs ordered_bbs in
        let (bbs1,s1) = add_phi_nodes_supply s frontiers pred_map live_in
                                             fn.fn_blocks defs in
        let rs0 = init_current_rename_state defs in
        let (_,s2,bbs2) = rename_current_blocks s1 rs0 bbs1 succ_map dtree in
        let bbs3 = simplify_current_phis_if had_phis bbs2 in
          (fn with fn_blocks := bbs3,s2)
Proof
  simp[make_ssa_current_fn_def]
QED

Theorem ALOOKUP_current_query_map:
  !labels query l.
    MEM l labels ==>
    ALOOKUP (current_query_map labels query) l = SOME (query l)
Proof
  Induct >> gvs[current_query_map_def] >> metis_tac[]
QED

Theorem ALOOKUP_current_pred_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_pred_map fn) l =
    SOME (cfg_preds_of (cfg_analyze fn) l)
Proof
  simp[current_pred_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_succ_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_succ_map fn) l =
    SOME (cfg_succs_of (cfg_analyze fn) l)
Proof
  simp[current_succ_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_frontier_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_frontier_map fn) l =
    SOME (frontier_of (dom_analyze (cfg_analyze fn) fn) l)
Proof
  simp[current_frontier_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_live_in:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_live_in fn) l =
    SOME (df_boundary [] (liveness_analyze fn) l)
Proof
  simp[current_live_in_def, ALOOKUP_current_query_map]
QED

Theorem current_dom_tree_eq:
  current_dom_tree fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      case fn_entry_label fn of
        NONE => DNode "" []
      | SOME entry => current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry
Proof
  simp[current_dom_tree_def]
QED

Theorem current_dom_postorder_eq:
  current_dom_postorder fn = dom_tree_postorder (current_dom_tree fn)
Proof
  simp[current_dom_postorder_def]
QED
