(*
 * Make SSA Pass — Definitions
 *
 * Converts a function into Static Single Assignment (SSA) form:
 *   1. Compute definition points: which blocks define each variable
 *   2. Insert PHI nodes at dominance frontiers (pruned by liveness)
 *   3. Rename variables with version suffixes (x → x:1, x:2, ...)
 *      using dominator tree walk
 *   4. Remove degenerate PHIs (single value → ASSIGN, all same → ASSIGN)
 *
 * TOP-LEVEL:
 *   compute_defs          — definition points for each variable
 *   place_phi             — insert a PHI for a variable at a block
 *   add_phi_nodes         — insert PHIs at dominance frontiers
 *   version_var           — create versioned variable name (e.g., "x:3")
 *   rename_block          — rename variables in a block (SSA renaming)
 *   rename_fn             — rename all variables in a function
 *   remove_degenerate_phis — simplify trivial PHIs to ASSIGNs
 *   make_ssa_fn           — full SSA construction pass
 *   make_ssa_ctx          — transform all functions in context
 *
 * Source: vyper/venom/passes/make_ssa.py
 *)

Theory makeSsaDefs
Ancestors
  cfgTransform venomWf dominatorDefs

(* ===== Definition Points ===== *)

(* All variables assigned in a block. *)
Definition block_assignments_def:
  block_assignments bb =
    nub (FLAT (MAP (λinst. inst.inst_outputs) bb.bb_instructions))
End

(* Compute definition points: for each variable, the set of block labels
   where it is assigned. Returns assoc list: (var, [block_label]). *)
Definition compute_defs_def:
  compute_defs [] = [] ∧
  compute_defs (bb::bbs) =
    let vars = block_assignments bb in
    let rest = compute_defs bbs in
    FOLDL (λacc var.
      case ALOOKUP acc var of
        SOME lbls => (var, bb.bb_label :: lbls) ::
                     FILTER (λ(v,_). v ≠ var) acc
      | NONE => (var, [bb.bb_label]) :: acc)
    rest vars
End

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

(* Add PHI nodes for all variables at their dominance frontiers.
   Implements the standard SSA PHI insertion algorithm:
   - For each variable v with definitions in blocks D,
   - For each block d in D, for each block f in DF(d),
   - Insert PHI for v at f (if not already done and v is live-in at f).

   dom_frontiers: block_label → [block_label] (dominance frontier map)
   pred_map: block_label → [block_label] (predecessor labels)
   live_in: block_label → string set (liveness at block entry)

   Returns updated block list with PHIs inserted. *)

(* Process one variable: insert PHIs at all required frontier blocks.
   worklist: blocks whose frontiers may need PHIs.
   has_phi: blocks that already have a PHI for this variable.
   Returns updated block list. *)
Definition insert_phis_for_var_def:
  insert_phis_for_var 0 var dom_frontiers pred_map live_in bbs worklist has_phi
    = bbs ∧
  insert_phis_for_var (SUC fuel) var dom_frontiers pred_map live_in bbs [] has_phi
    = bbs ∧
  insert_phis_for_var (SUC fuel) var dom_frontiers pred_map live_in bbs
    (d::rest) has_phi =
    let frontiers = case ALOOKUP dom_frontiers d of
                      SOME fs => fs | NONE => [] in
    let (bbs', rest', has_phi') = FOLDL
      (λ(bbs_acc, wl_acc, hp_acc) f.
        if MEM f hp_acc then (bbs_acc, wl_acc, hp_acc)
        else
          (* Check if var is live-in at f *)
          let is_live = case ALOOKUP live_in f of
                          SOME vars => MEM var vars
                        | NONE => F in
          if ¬is_live then (bbs_acc, wl_acc, f :: hp_acc)
          else
            let preds = case ALOOKUP pred_map f of
                          SOME ps => ps | NONE => [] in
            let phi = build_phi_inst var preds in
            let bbs_new = MAP (λbb.
              if bb.bb_label = f
              then insert_phi_at_block phi bb
              else bb) bbs_acc in
            (bbs_new, f :: wl_acc, f :: hp_acc))
      (bbs, rest, has_phi) frontiers in
    insert_phis_for_var fuel var dom_frontiers pred_map live_in bbs' rest' has_phi'
End

(* Insert PHIs for all variables. *)
Definition add_phi_nodes_def:
  add_phi_nodes dom_frontiers pred_map live_in bbs defs =
    FOLDL (λbbs_acc (var, def_blocks).
      let fuel = LENGTH bbs * LENGTH bbs in
      insert_phis_for_var fuel var dom_frontiers pred_map live_in
        bbs_acc def_blocks [])
    bbs defs
End

(* ===== Variable Renaming ===== *)

(* Create versioned variable name: "x" with version 3 → "x:3".
   Version 0 keeps the original name (no suffix). *)
Definition version_var_def:
  version_var base (n:num) =
    if n = 0 then base
    else STRCAT base (STRCAT ":" (toString n))
End

(* Rename state: tracks the current version counter and name stack
   for each variable. Represented as assoc lists.
   counters: var → next version number
   stacks: var → [current_version, ...] (head = latest) *)
(* Rename state: counters (var → next version) and stacks (var → version stack).
   All version numbers are natural numbers. *)

(* Initial rename state from definition points.
   Returns (counters, stacks) where each var starts at counter 0, stack [0]. *)
Definition init_rename_state_def:
  init_rename_state defs =
    let vars = MAP FST defs in
    (MAP (λv. (v, 0n)) vars,
     MAP (λv. (v, [0n])) vars)
End

(* Get latest version of a variable. *)
Definition latest_version_def:
  latest_version (counters : (string # num) list,
                  stacks : (string # num list) list) var =
    case ALOOKUP stacks var of
      SOME (ver :: _) => version_var var ver
    | _ => var
End

(* Push a new version for a variable. *)
Definition push_version_def:
  push_version (counters : (string # num) list,
                stacks : (string # num list) list) var =
    let ver = case ALOOKUP counters var of SOME n => n | NONE => 0n in
    let counters' = (var, ver + 1n) ::
                    FILTER (λ(v,_). v ≠ var) counters in
    let stacks' =
      case ALOOKUP stacks var of
        SOME stack => (var, ver :: stack) ::
                      FILTER (λ(v,_). v ≠ var) stacks
      | NONE => (var, [ver]) :: stacks in
    ((counters', stacks'), ver)
End

(* Pop a version from a variable's stack. *)
Definition pop_version_def:
  pop_version (counters : (string # num) list,
               stacks : (string # num list) list) var =
    case ALOOKUP stacks var of
      SOME (_ :: rest) =>
        (counters, (var, rest) :: FILTER (λ(v,_). v ≠ var) stacks)
    | _ => (counters, stacks)
End

(* Rename operands in a non-PHI instruction. *)
Definition rename_operands_def:
  rename_operands rs [] = [] ∧
  rename_operands rs (Var v :: ops) =
    Var (latest_version rs v) :: rename_operands rs ops ∧
  rename_operands rs (op :: ops) =
    op :: rename_operands rs ops
End

(* Rename output variables: push new versions. *)
Definition rename_outputs_def:
  rename_outputs rs [] = (rs, [] : string list) ∧
  rename_outputs rs (v::vs) =
    let (rs', ver : num) = push_version rs v in
    let new_name = version_var v ver in
    let (rs'', rest) = rename_outputs rs' vs in
    (rs'', new_name :: rest)
End

(* Rename a single instruction.
   For non-PHI: rename input operands, then push new versions for outputs.
   For PHI: only push new versions for outputs (operands renamed separately). *)
Definition rename_inst_def:
  rename_inst rs inst =
    if inst.inst_opcode = PHI then
      let (rs', outs') = rename_outputs rs inst.inst_outputs in
      (rs', inst with inst_outputs := outs')
    else
      let ops' = rename_operands rs inst.inst_operands in
      let (rs', outs') = rename_outputs rs inst.inst_outputs in
      (rs', inst with <| inst_operands := ops'; inst_outputs := outs' |>)
End

(* Rename all instructions in a block. Thread rename state. *)
Definition rename_block_insts_def:
  rename_block_insts rs [] = (rs, []) ∧
  rename_block_insts rs (inst::rest) =
    let (rs', inst') = rename_inst rs inst in
    let (rs'', rest') = rename_block_insts rs' rest in
    (rs'', inst' :: rest')
End

(* Update PHI operands for a predecessor: rename vars matching the label. *)
Definition update_phi_for_pred_def:
  update_phi_for_pred rs current_label [] = [] ∧
  update_phi_for_pred rs current_label [x] = [x] ∧
  update_phi_for_pred rs current_label (Label l :: Var v :: rest) =
    (if l = current_label
     then Label l :: Var (latest_version rs v) ::
          update_phi_for_pred rs current_label rest
     else Label l :: Var v ::
          update_phi_for_pred rs current_label rest) ∧
  update_phi_for_pred rs current_label (x :: y :: rest) =
    x :: y :: update_phi_for_pred rs current_label rest
End

(* ===== Dominator Tree Walk ===== *)

(* Update successor PHIs for a given block label and rename state. *)
Definition update_succ_phis_def:
  update_succ_phis rs current_label bbs succs =
    FOLDL (λbs s.
      case lookup_block s bs of
        NONE => bs
      | SOME sbb =>
          let sbb' = sbb with bb_instructions :=
            MAP (λinst.
              if inst.inst_opcode ≠ PHI then inst
              else inst with inst_operands :=
                update_phi_for_pred rs current_label inst.inst_operands)
            sbb.bb_instructions in
          replace_block s sbb' bs)
    bbs succs
End

(* Rename variables in dominator tree order.
   Processes a single subtree rooted at lbl.
   Returns (final_counters, updated_blocks):
   - Counters are threaded through siblings so each gets unique versions
   - Each child sees the parent's stacks (not sibling's pushed versions)
   This matches Python's _rename_vars where var_name_counters is a shared
   class attribute (monotonically increasing) while var_name_stacks uses
   push/pop (children see parent's stack, not sibling's). *)
Definition rename_blocks_def:
  rename_blocks 0 rs bbs dom_children succ_map lbl = (FST rs, bbs) ∧
  rename_blocks (SUC fuel) rs bbs dom_children succ_map lbl =
    case lookup_block lbl bbs of
      NONE => (FST rs, bbs)
    | SOME bb =>
        (* Pre-action: rename instructions, push versions for outputs *)
        let (rs1, insts') = rename_block_insts rs bb.bb_instructions in
        let bb' = bb with bb_instructions := insts' in
        let bbs1 = replace_block lbl bb' bbs in
        (* Update successor PHIs with current rename state *)
        let succs = case ALOOKUP succ_map lbl of
                      SOME ss => ss | NONE => [] in
        let bbs2 = update_succ_phis rs1 lbl bbs1 succs in
        (* Recurse on dominated children.
           Thread counters through siblings (so each gets unique versions).
           Each child gets parent's stacks (not sibling's pushed versions).
           This matches Python where var_name_counters increases monotonically
           across all branches, but var_name_stacks is push/popped per subtree. *)
        let children = case ALOOKUP dom_children lbl of
                         SOME cs => cs | NONE => [] in
        let parent_stacks = SND rs1 in
        FOLDL (λ(ctrs, bs) c.
          rename_blocks fuel (ctrs, parent_stacks) bs dom_children succ_map c)
          (FST rs1, bbs2) children
End

(* ===== Degenerate PHI Removal ===== *)

(* Remove degenerate PHIs:
   - Self-referential operands (phi output = operand value) are removed
   - 0 remaining operands → remove instruction (NOP)
   - 1 remaining operand → convert to ASSIGN
   - All same value → convert to ASSIGN *)
Definition simplify_phi_def:
  simplify_phi inst =
    if inst.inst_opcode ≠ PHI then inst
    else
      let out = case inst.inst_outputs of [v] => SOME v | _ => NONE in
      let pairs = phi_pairs inst.inst_operands in
      (* Remove self-referential pairs *)
      let pairs' = case out of
                     NONE => pairs
                   | SOME v => FILTER (λ(l,var). var ≠ v) pairs in
      case pairs' of
        [] => inst with <| inst_opcode := NOP;
                          inst_operands := [];
                          inst_outputs := [] |>
      | [(l, v)] => inst with <| inst_opcode := ASSIGN;
                                 inst_operands := [Var v] |>
      | _ =>
          (* Check if all values are the same *)
          let vals = MAP SND pairs' in
          (case vals of
             [] => inst  (* shouldn't happen *)
           | (v :: vs) =>
               if EVERY (λx. x = v) vs then
                 inst with <| inst_opcode := ASSIGN;
                              inst_operands := [Var v] |>
               else
                 inst with inst_operands :=
                   FLAT (MAP (λ(l,v). [Label l; Var v]) pairs'))
End

(* Apply degenerate PHI removal to all blocks. *)
Definition remove_degenerate_phis_def:
  remove_degenerate_phis bbs =
    MAP (λbb. bb with bb_instructions :=
      FILTER (λi. i.inst_opcode ≠ NOP)
        (MAP simplify_phi bb.bb_instructions))
    bbs
End

(* ===== Ensure Well-Formed ===== *)

(* Instruction sort key: PHI/PARAM → 0, regular → 1, terminator → 2.
   Matches Python's ensure_well_formed. *)
Definition inst_sort_key_def:
  inst_sort_key inst =
    if inst.inst_opcode = PHI then 0n
    else if is_terminator inst.inst_opcode then 2n
    else 1n
End

(* Sort instructions so PHIs are at the start and terminators at the end.
   Uses insertion sort (stable) to match Python's list.sort(key=...). *)
Definition insert_by_key_def:
  insert_by_key inst [] = [inst] ∧
  insert_by_key inst (h::t) =
    if inst_sort_key inst ≤ inst_sort_key h
    then inst :: h :: t
    else h :: insert_by_key inst t
End

Definition stable_sort_insts_def:
  stable_sort_insts [] = [] ∧
  stable_sort_insts (inst::rest) =
    insert_by_key inst (stable_sort_insts rest)
End

Definition ensure_well_formed_def:
  ensure_well_formed bbs =
    MAP (λbb. bb with bb_instructions :=
      stable_sort_insts bb.bb_instructions) bbs
End

(* ===== Full Pass ===== *)

(* Full make_ssa pass on a function.
   Requires pre-computed: CFG, dominator tree, liveness.
   Parameters encode these analyses as maps.
   dom_post_order: block labels in dominator tree post-order
     (determines variable/PHI insertion order to match Python). *)
Definition make_ssa_fn_def:
  make_ssa_fn dom_frontiers dom_children dom_post_order
              pred_map succ_map live_in func =
    case fn_entry_label func of
      NONE => func
    | SOME entry =>
        (* Iterate blocks in dom_post_order for compute_defs *)
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (λlbl. lookup_block lbl func.fn_blocks) dom_post_order)) in
        let defs = compute_defs ordered_bbs in
        (* 1. Insert PHI nodes *)
        let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                     func.fn_blocks defs in
        (* 2. Rename variables *)
        let rs0 = init_rename_state defs in
        let fuel = LENGTH bbs1 * LENGTH bbs1 in
        let (_, bbs2) = rename_blocks fuel rs0 bbs1 dom_children succ_map entry in
        (* 3. Remove degenerate PHIs *)
        let bbs3 = remove_degenerate_phis bbs2 in
        (* 4. Ensure PHIs are at top of blocks *)
        let bbs4 = ensure_well_formed bbs3 in
        func with fn_blocks := bbs4
End

(* Transform all functions in context.
   Note: in practice, the caller provides pre-computed analyses.
   This definition takes analysis maps as parameters. *)
Definition make_ssa_ctx_def:
  make_ssa_ctx dom_frontiers_fn dom_children_fn dom_post_order_fn
               pred_map_fn succ_map_fn live_in_fn ctx =
    ctx with ctx_functions := MAP (λfunc.
      make_ssa_fn (dom_frontiers_fn func) (dom_children_fn func)
                  (dom_post_order_fn func)
                  (pred_map_fn func) (succ_map_fn func)
                  (live_in_fn func) func)
    ctx.ctx_functions
End
