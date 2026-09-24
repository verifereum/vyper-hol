(*
 * Current-analysis, supply-safe MakeSSA adapter — definitions.
 *
 * This theory starts with the canonical analysis bridge.  The configured
 * MakeSSA implementation is kept separate from the legacy semantic model in
 * makeSsaDefs.
 *)

Theory makeSsaCurrentDefs
Ancestors
  makeSsaDefs cfgDefs dominatorDefs livenessDefs irSupply
  list alist

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
  qabbrev_tac `fs = case ALOOKUP dom_frontiers d of
                      NONE => [] | SOME x => x` >>
  qabbrev_tac `U = nub (MAP (\bb. bb.bb_label) bbs ++
                         FLAT (MAP SND dom_frontiers))` >>
  qabbrev_tac `result = process_frontiers_supply s var pred_map live_in
                          bbs rest has_phi fs` >>
  `result = (bbs',rest',has_phi',s')` by
    simp[Abbr `result`, Abbr `fs`] >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  `process_frontiers_supply s var pred_map live_in bbs rest has_phi fs =
   (bbs',rest',has_phi',s')` by gvs[markerTheory.Abbrev_def] >>
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
   instruction IDs: self edges are discarded and equal inputs collapse. *)
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
            else inst with inst_operands := cleaned
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
  simp[simplify_current_phi_raw_def] >> rpt CASE_TAC >> gvs[]
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
  rename [`simplify_current_phi_prefix_parts insts = (phis,ordinary)`] >>
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
