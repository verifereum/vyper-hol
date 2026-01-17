(*
 * Remove Unused Variables Pass
 *
 * Port of venom/passes/remove_unused_variables.py.
 *)

Theory removeUnusedVars
Ancestors
  list pred_set
  orderedSet
  irOps dfgAnalysis reachableAnalysis
  venomSem

Definition alist_lookup_def:
  alist_lookup k [] = NONE /\
  alist_lookup k ((k',v)::rest) =
    if k = k' then SOME v else alist_lookup k rest
End

Definition alist_update_def:
  alist_update k v m =
    (k, v) :: FILTER (λ(k',_). k' <> k) m
End

Definition fmap_to_alist_def:
  fmap_to_alist m =
    MAP (λk. (k, THE (FLOOKUP m k))) (SET_TO_LIST (FDOM m))
End

Definition list_max_def:
  list_max [] = NONE /\
  list_max (x::xs) =
    case list_max xs of
      NONE => SOME x
    | SOME m => SOME (MAX x m)
End

Definition index_insts_def:
  index_insts (idx:num) [] = [] /\
  index_insts idx (inst::rest) =
    (inst.inst_id, idx) :: index_insts (idx + 1) rest
End

Definition msize_indices_aux_def:
  msize_indices_aux (idx:num) [] = [] /\
  msize_indices_aux idx (inst::rest) =
    if inst.inst_opcode = MSIZE then
      idx :: msize_indices_aux (idx + 1) rest
    else msize_indices_aux (idx + 1) rest
End

Definition build_inst_block_map_def:
  build_inst_block_map fn =
    FOLDL
      (λacc bb.
         FOLDL
           (λacc2 inst. (inst.inst_id, bb.bb_label) :: acc2)
           acc bb.bb_instructions)
      [] fn.fn_blocks
End

Definition build_inst_order_map_def:
  build_inst_order_map fn =
    FOLDL
      (λacc bb. acc ++ index_insts (0:num) bb.bb_instructions)
      [] fn.fn_blocks
End

Definition build_msize_map_def:
  build_msize_map fn =
    FOLDL
      (λacc bb.
         alist_update bb.bb_label (msize_indices_aux (0:num) bb.bb_instructions) acc)
      [] fn.fn_blocks
End

Definition has_msize_def:
  has_msize msize_map lbl =
    case alist_lookup lbl msize_map of
      NONE => F
    | SOME xs => xs <> []
End

Definition get_last_msize_def:
  get_last_msize msize_map lbl =
    case alist_lookup lbl msize_map of
      NONE => NONE
    | SOME xs => list_max xs
End

Definition msize_fence_def:
  msize_fence fn reachable_map msize_map inst_order inst_id =
    case alist_lookup inst_id inst_order of
      NONE => F
    | SOME idx =>
        case alist_lookup inst_id (build_inst_block_map fn) of
          NONE => F
        | SOME lbl =>
            let reach = fmap_lookup_ordset reachable_map lbl in
            let has_reach_msize =
              EXISTS (λbbl. has_msize msize_map bbl) reach in
            if has_reach_msize then T
            else if ~has_msize msize_map lbl then F
            else
              case get_last_msize msize_map lbl of
                NONE => F
              | SOME last_idx => idx < last_idx
End

Definition outputs_have_uses_def:
  outputs_have_uses dfg outs =
    EXISTS (λv. dfg_get_uses dfg v <> []) outs
End

Definition uniq_vars_def:
  uniq_vars vars = ordset_addmany [] vars
End

Definition remove_use_list_def:
  remove_use_list dfg inst_id [] = dfg /\
  remove_use_list dfg inst_id (v::vs) =
    remove_use_list (dfg_remove_use dfg v inst_id) inst_id vs
End

Definition add_worklist_uses_def:
  add_worklist_uses dfg vars work =
    FOLDL (λacc v. ordset_union acc (dfg_get_uses dfg v)) work vars
End

Definition remove_unused_process_inst_def:
  remove_unused_process_inst fn reachable_map msize_map inst_order blocked work dfg inst_id =
    case lookup_inst_in_function inst_id fn of
      NONE => (fn, dfg, work, msize_map, blocked)
    | SOME inst =>
        if inst.inst_outputs = [] then (fn, dfg, work, msize_map, blocked)
        else if inst_is_volatile inst \/ inst_is_bb_terminator inst then
          (fn, dfg, work, msize_map, blocked)
        else if Eff_MSIZE IN write_effects inst.inst_opcode /\
                msize_fence fn reachable_map msize_map inst_order inst_id then
          (fn, dfg, work, msize_map, ordset_add inst_id blocked)
        else if outputs_have_uses dfg inst.inst_outputs then
          (fn, dfg, work, msize_map, blocked)
        else
          let vars = uniq_vars (inst_input_vars inst) in
          let dfg1 = remove_use_list dfg inst_id vars in
          let work1 = add_worklist_uses dfg1 vars work in
          let (msize_map', work2, blocked') =
            if inst.inst_opcode = MSIZE then
              case alist_lookup inst_id (build_inst_block_map fn) of
                NONE => (msize_map, work1, blocked)
              | SOME lbl =>
                  let xs = case alist_lookup lbl msize_map of NONE => [] | SOME ys => ys in
                  let idx = case alist_lookup inst_id inst_order of NONE => 0 | SOME i => i in
                  let xs' = ordset_remove idx xs in
                  let msize_map' = alist_update lbl xs' msize_map in
                  (msize_map', ordset_union work1 blocked, [])
            else (msize_map, work1, blocked) in
          let inst' = inst_make_nop inst in
          let fn' = update_inst_in_function inst_id inst' fn in
          (fn', dfg1, work2, msize_map', blocked')
End

Definition remove_unused_iter_def:
  remove_unused_iter 0 fn reachable_map msize_map inst_order blocked dfg work = (fn, dfg, msize_map) /\
  remove_unused_iter (SUC fuel) fn reachable_map msize_map inst_order blocked dfg work =
    case work of
      [] => (fn, dfg, msize_map)
    | inst_id::rest =>
        let (fn', dfg', work', msize_map', blocked') =
          remove_unused_process_inst fn reachable_map msize_map inst_order blocked rest dfg inst_id in
        remove_unused_iter fuel fn' reachable_map msize_map' inst_order blocked' dfg' work'
End

Definition clear_nops_block_def:
  clear_nops_block bb =
    bb with bb_instructions := FILTER (λinst. inst.inst_opcode <> NOP) bb.bb_instructions
End

Definition remove_unused_function_def:
  remove_unused_function fn cfg =
    let dfg = dfg_analyze fn in
    let reach = reachable_analyze fn cfg in
    let msize_map = build_msize_map fn in
    let inst_order = build_inst_order_map fn in
    let outputs = fmap_to_alist dfg.dfg_outputs in
    let work0 = MAP SND outputs in
    let fuel = (LENGTH (fn_instructions_list fn) + 1) * (LENGTH (fn_instructions_list fn) + 1) in
    let (fn', _, _) =
      remove_unused_iter fuel fn reach.reachable msize_map inst_order [] dfg work0 in
    fn' with fn_blocks := MAP clear_nops_block fn'.fn_blocks
End

Definition remove_unused_context_def:
  remove_unused_context ctx =
    let cfgs = MAP cfg_analyze ctx.ctx_functions in
    ctx with ctx_functions :=
      MAP2 (λfn cfg. remove_unused_function fn cfg) ctx.ctx_functions cfgs
End

val _ = export_theory();
