(*
 * DFT Pass
 *
 * Port of venom/passes/dft.py.
 *)

Theory dft
Ancestors
  list pred_set sorting
  orderedSet
  irOps cfgAnalysis dfgAnalysis livenessAnalysis stackOrderAnalysis
  venomSem

Type dep_map = ``:(num # num list) list``
Type effect_map = ``:(effect # num) list``
Type effect_list_map = ``:(effect # num list) list``
Type order_map = ``:(string # string list) list``

Definition dep_lookup_def:
  dep_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition dep_update_def:
  dep_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition dep_add_def:
  dep_add m k v = dep_update m k (ordset_add v (dep_lookup m k))
End

Definition effect_lookup_def:
  effect_lookup m k = ALOOKUP m k
End

Definition effect_update_def:
  effect_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition effect_list_lookup_def:
  effect_list_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition effect_list_update_def:
  effect_list_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition order_lookup_def:
  order_lookup m k = ALOOKUP m k
End

Definition order_update_def:
  order_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition inst_id_in_block_def:
  inst_id_in_block iid bb =
    MEM iid (MAP (λinst. inst.inst_id) bb.bb_instructions)
End

Definition dfg_producing_in_block_def:
  dfg_producing_in_block dfg bb v =
    case dfg_get_producing dfg v of
      NONE => NONE
    | SOME iid => if inst_id_in_block iid bb then SOME iid else NONE
End

Definition dft_operand_data_deps_def:
  dft_operand_data_deps dfg bb ops =
    FOLDL
      (λacc op.
         case op of
           Var v =>
             (case dfg_producing_in_block dfg bb v of
                NONE => acc
              | SOME iid => ordset_add iid acc)
         | _ => acc)
      [] ops
End

Definition dft_order_deps_def:
  dft_order_deps dfg bb order =
    FOLDL
      (λacc v.
         case dfg_producing_in_block dfg bb v of
           NONE => acc
         | SOME iid => ordset_add iid acc)
      [] order
End

Definition list_find_index_aux_def:
  list_find_index_aux x [] (idx:num) = NONE /\
  list_find_index_aux x (y::ys) idx =
    if x = y then SOME idx else list_find_index_aux x ys (idx + 1)
End

Definition list_find_index_def:
  list_find_index x xs = list_find_index_aux x xs (0:num)
End

Definition min_list_def:
  min_list [] = 0 /\
  min_list (x::xs) = FOLDL MIN x xs
End

Definition collect_operand_dep_indices_def:
  collect_operand_dep_indices dfg child [] (idx:num) = [] /\
  collect_operand_dep_indices dfg child (op::ops) idx =
    let rest = collect_operand_dep_indices dfg child ops (idx + 1) in
    case op of
      Var v =>
        if dfg_get_producing dfg v = SOME child then idx :: rest else rest
    | _ => rest
End

Definition collect_operand_positions_def:
  collect_operand_positions ops outs =
    FOLDL
      (λacc out.
         case list_find_index (Var out) ops of
           NONE => acc
         | SOME idx => acc ++ [idx])
      [] outs
End

Definition collect_order_positions_def:
  collect_order_positions order outs =
    FOLDL
      (λacc out.
         case list_find_index out order of
           NONE => acc
         | SOME idx => acc ++ [idx])
      [] outs
End

Definition dft_child_cost_def:
  dft_child_cost dfg order inst dda eda data_offspring child =
    let deps = dep_lookup dda inst.inst_id in
    let effs = dep_lookup eda inst.inst_id in
    let is_effect_only = (~MEM child deps /\ MEM child effs) in
    let has_data = ~(dep_lookup data_offspring child = []) in
    if is_effect_only \/ inst_flippable inst then
      if has_data then 0 else 1
    else
      let operand_idxs = collect_operand_dep_indices dfg child inst.inst_operands 0 in
      if operand_idxs <> [] then 2 + min_list operand_idxs + LENGTH order
      else
        let output_positions = collect_operand_positions inst.inst_operands inst.inst_outputs in
        if output_positions <> [] then 2 + min_list output_positions + LENGTH order
        else
          let order_positions = collect_order_positions order inst.inst_outputs in
          if order_positions <> [] then 2 + min_list order_positions
          else 2 + LENGTH order
End

Definition dft_sort_children_def:
  dft_sort_children dfg order inst dda eda data_offspring children =
    QSORT
      (λa b. dft_child_cost dfg order inst dda eda data_offspring a <
             dft_child_cost dfg order inst dda eda data_offspring b)
      children
End

Definition dft_handle_write_effects_def:
  dft_handle_write_effects inst_id write_eff eda last_write all_read =
    FOLDL
      (λacc eff.
         let (ed, lw, ar) = acc in
         let ed1 =
           FOLDL (λacc2 iid. dep_add acc2 inst_id iid)
             ed (effect_list_lookup ar eff) in
         let ed2 =
           if eff = Eff_MSIZE then ed1
           else
             (case effect_lookup lw eff of
                NONE => ed1
              | SOME iid => dep_add ed1 inst_id iid) in
         let lw1 = effect_update lw eff inst_id in
         let ar1 = effect_list_update ar eff [] in
         (ed2, lw1, ar1))
      (eda, last_write, all_read) write_eff
End

Definition dft_handle_read_effects_def:
  dft_handle_read_effects inst_id read_eff eda last_write all_read =
    FOLDL
      (λacc eff.
         let (ed, lw, ar) = acc in
         let ed1 =
           case effect_lookup lw eff of
             NONE => ed
           | SOME iid => if iid = inst_id then ed else dep_add ed inst_id iid in
         let ar1 =
           effect_list_update ar eff (ordset_add inst_id (effect_list_lookup ar eff)) in
         (ed1, lw, ar1))
      (eda, last_write, all_read) read_eff
End

Definition dft_build_dep_graphs_def:
  dft_build_dep_graphs fn dfg order bb =
    let insts = bb_non_phi_instructions bb in
    let (dda, eda, _, _) =
      FOLDL
        (λacc inst.
           let (dd, ed, lw, ar) = acc in
           let deps = dft_operand_data_deps dfg bb inst.inst_operands in
           let deps' =
             if inst_is_bb_terminator inst then
               ordset_union deps (dft_order_deps dfg bb order)
             else deps in
           let dd1 = dep_update dd inst.inst_id deps' in
           let ed1 = dep_update ed inst.inst_id (dep_lookup ed inst.inst_id) in
           let we = SET_TO_LIST (write_effects inst.inst_opcode) in
           let re = SET_TO_LIST (read_effects inst.inst_opcode) in
           let (ed2, lw2, ar2) = dft_handle_write_effects inst.inst_id we ed1 lw ar in
           let (ed3, lw3, ar3) = dft_handle_read_effects inst.inst_id re ed2 lw2 ar2 in
           (dd1, ed3, lw3, ar3))
        ([], [], [], []) insts in
    (dda, eda)
End

Definition dft_data_offspring_aux_def:
  dft_data_offspring_aux 0 dda acc iid = (acc, dep_lookup acc iid) /\
  dft_data_offspring_aux (SUC fuel) dda acc iid =
    case ALOOKUP acc iid of
      SOME deps => (acc, deps)
    | NONE =>
        let direct = dep_lookup dda iid in
        let (acc1, all_deps) =
          FOLDL
            (λstate did.
               let (m, deps) = state in
               let (m', deps') = dft_data_offspring_aux fuel dda m did in
               (m', ordset_union deps deps'))
            (acc, direct) direct in
        let acc2 = dep_update acc1 iid all_deps in
        (acc2, all_deps)
End

Definition dft_build_data_offspring_def:
  dft_build_data_offspring dda inst_ids =
    let fuel = LENGTH inst_ids + 1 in
    FOLDL
      (λacc iid. FST (dft_data_offspring_aux fuel dda acc iid))
      [] inst_ids
End

Definition dft_inst_map_def:
  dft_inst_map insts = MAP (λinst. (inst.inst_id, inst)) insts
End

Definition dft_process_instruction_r_def:
  dft_process_instruction_r 0 inst_map dfg order dda eda data_offspring visited acc inst_id =
    (visited, acc) /\
  dft_process_instruction_r (SUC fuel) inst_map dfg order dda eda data_offspring visited acc inst_id =
    if MEM inst_id visited then (visited, acc) else
    case ALOOKUP inst_map inst_id of
      NONE => (visited, acc)
    | SOME inst =>
        let visited1 = ordset_add inst_id visited in
        if inst_is_pseudo inst then (visited1, acc)
        else
          let children = ordset_union (dep_lookup dda inst_id) (dep_lookup eda inst_id) in
          let orig_children = children in
          let sorted = dft_sort_children dfg order inst dda eda data_offspring children in
          let inst' =
            if inst_flippable inst /\ sorted <> orig_children then inst_flip inst else inst in
          let (visited2, acc2) =
            FOLDL
              (λstate cid.
                 let (vis, accs) = state in
                 dft_process_instruction_r fuel inst_map dfg order dda eda data_offspring vis accs cid)
              (visited1, acc) sorted in
          (visited2, acc2 ++ [inst'])
End

Definition dft_process_block_def:
  dft_process_block fn dfg order bb =
    let (dda, eda) = dft_build_dep_graphs fn dfg order bb in
    let insts = bb.bb_instructions in
    let inst_ids = MAP (λinst. inst.inst_id) insts in
    let data_offspring = dft_build_data_offspring dda inst_ids in
    let inst_map = dft_inst_map insts in
    let pseudo = bb_pseudo_instructions bb in
    let non_phi = bb_non_phi_instructions bb in
    let non_phi_ids = MAP (λinst. inst.inst_id) non_phi in
    let to_remove =
      FOLDL
        (λacc iid. ordset_union acc (ordset_union (dep_lookup dda iid) (dep_lookup eda iid)))
        [] non_phi_ids in
    let entry = ordset_diff non_phi_ids to_remove in
    let fuel = LENGTH insts + 1 in
    let (_, insts') =
      FOLDL
        (λstate iid.
           let (vis, acc) = state in
           dft_process_instruction_r fuel inst_map dfg order dda eda data_offspring vis acc iid)
        ([], pseudo) entry in
    bb with bb_instructions := insts'
End

Definition update_block_def:
  update_block lbl new_bb [] = [] /\
  update_block lbl new_bb (bb::bbs) =
    if bb.bb_label = lbl then new_bb :: bbs
    else bb :: update_block lbl new_bb bbs
End

Definition dft_iter_def:
  dft_iter 0 fn cfg dfg live from_to last_order worklist = fn /\
  dft_iter (SUC fuel) fn cfg dfg live from_to last_order worklist =
    case worklist of
      [] => fn
    | lbl::rest =>
        (case lookup_block lbl fn.fn_blocks of
           NONE => dft_iter fuel fn cfg dfg live from_to last_order rest
         | SOME bb =>
             let (from_to', order) = stack_order_get_stack fn cfg live from_to bb in
             (case order_lookup last_order lbl of
                SOME prev =>
                  if prev = order then fn
                  else
                    let last_order' = order_update last_order lbl order in
                    let order_rev = REVERSE order in
                    let bb' = dft_process_block fn dfg order_rev bb in
                    let fn' = fn with fn_blocks := update_block lbl bb' fn.fn_blocks in
                    let preds = fmap_lookup_ordset cfg.cfg_in lbl in
                    dft_iter fuel fn' cfg dfg live from_to' last_order' (rest ++ preds)
              | NONE =>
                  let last_order' = order_update last_order lbl order in
                  let order_rev = REVERSE order in
                  let bb' = dft_process_block fn dfg order_rev bb in
                  let fn' = fn with fn_blocks := update_block lbl bb' fn.fn_blocks in
                  let preds = fmap_lookup_ordset cfg.cfg_in lbl in
                  dft_iter fuel fn' cfg dfg live from_to' last_order' (rest ++ preds)))
End

Definition dft_function_def:
  dft_function fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let live = liveness_analyze fn cfg in
    let worklist = cfg.dfs_post in
    let fuel = (LENGTH fn.fn_blocks + 1) * (LENGTH fn.fn_blocks + 1) in
    dft_iter fuel fn cfg dfg live [] [] worklist
End

Definition dft_context_def:
  dft_context ctx =
    ctx with ctx_functions := MAP dft_function ctx.ctx_functions
End

val _ = export_theory();
