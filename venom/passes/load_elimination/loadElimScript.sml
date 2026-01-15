(*
 * Load Elimination Pass
 *
 * Port of venom/passes/load_elimination.py.
 *)

Theory loadElim
Ancestors
  list pred_set sorting
  orderedSet
  irOps
  cfgAnalysis dfgAnalysis basePtrAnalysis memAliasAnalysis addrSpace
  memoryLocation
  instUpdater compilerState
  venomSem

Datatype:
  load_effect =
    | LE_MEMORY
    | LE_TRANSIENT
    | LE_STORAGE
    | LE_DLOAD
    | LE_CALLDATALOAD
End

Datatype:
  load_key =
    | LoadOp operand
    | LoadMem memory_location
End

Type lattice = ``:(load_key # operand list) list``
Type inst_lattice_map = ``:(num # lattice) list``
Type bb_lattice_map = ``:(string # lattice) list``

Definition lattice_lookup_def:
  lattice_lookup k lat =
    case ALOOKUP lat k of NONE => [] | SOME v => v
End

Definition lattice_update_def:
  lattice_update k v lat = (k, v) :: FILTER (λ(kk,_). kk <> k) lat
End

Definition lattice_remove_def:
  lattice_remove k lat = FILTER (λ(kk,_). kk <> k) lat
End

Definition lattice_keys_def:
  lattice_keys lat = MAP FST lat
End

Definition inst_lattice_lookup_def:
  inst_lattice_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition inst_lattice_update_def:
  inst_lattice_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition bb_lattice_lookup_def:
  bb_lattice_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition bb_lattice_update_def:
  bb_lattice_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition load_effect_load_op_def:
  load_effect_load_op LE_MEMORY = MLOAD /\
  load_effect_load_op LE_TRANSIENT = TLOAD /\
  load_effect_load_op LE_STORAGE = SLOAD /\
  load_effect_load_op LE_DLOAD = DLOAD /\
  load_effect_load_op LE_CALLDATALOAD = CALLDATALOAD
End

Definition load_effect_store_op_def:
  load_effect_store_op LE_MEMORY = SOME MSTORE /\
  load_effect_store_op LE_TRANSIENT = SOME TSTORE /\
  load_effect_store_op LE_STORAGE = SOME SSTORE /\
  load_effect_store_op LE_DLOAD = NONE /\
  load_effect_store_op LE_CALLDATALOAD = NONE
End

Definition load_effect_word_scale_def:
  load_effect_word_scale LE_MEMORY = (32:num) /\
  load_effect_word_scale LE_TRANSIENT = (1:num) /\
  load_effect_word_scale LE_STORAGE = (1:num) /\
  load_effect_word_scale LE_DLOAD = (32:num) /\
  load_effect_word_scale LE_CALLDATALOAD = (32:num)
End

Definition load_effect_to_space_def:
  load_effect_to_space LE_MEMORY = SOME MEMORY /\
  load_effect_to_space LE_STORAGE = SOME STORAGE /\
  load_effect_to_space LE_TRANSIENT = SOME TRANSIENT /\
  load_effect_to_space _ = NONE
End

Definition load_effect_write_effect_def:
  load_effect_write_effect LE_MEMORY = SOME Eff_MEMORY /\
  load_effect_write_effect LE_STORAGE = SOME Eff_STORAGE /\
  load_effect_write_effect LE_TRANSIENT = SOME Eff_TRANSIENT /\
  load_effect_write_effect _ = NONE
End

Definition inst_load_ptr_def:
  inst_load_ptr inst =
    case inst.inst_operands of
      op::_ => SOME op
    | _ => NONE
End

Definition inst_store_ptr_def:
  inst_store_ptr inst =
    case inst.inst_operands of
      _::op::_ => SOME op
    | _ => NONE
End

Definition load_key_memloc_def:
  load_key_memloc bpa word_scale key =
    case key of
      LoadMem loc => loc
    | LoadOp op =>
        let ops = inst_access_ops (SOME op) (SOME (Lit (n2w word_scale))) NONE in
        segment_from_ops bpa ops
End

Definition load_key_of_read_def:
  load_key_of_read bpa eff inst =
    case load_effect_to_space eff of
      NONE =>
        (case inst_load_ptr inst of
           NONE => LoadMem memory_location_undefined
         | SOME op => LoadOp op)
    | SOME space =>
        let loc = get_read_location bpa inst space in
        if memory_location_is_fixed loc then LoadMem loc
        else
          (case inst_load_ptr inst of
             NONE => LoadMem memory_location_undefined
           | SOME op => LoadOp op)
End

Definition load_key_of_write_def:
  load_key_of_write bpa eff inst =
    case load_effect_to_space eff of
      NONE =>
        (case inst_store_ptr inst of
           NONE => LoadMem memory_location_undefined
         | SOME op => LoadOp op)
    | SOME space =>
        let loc = get_write_location bpa inst space in
        if memory_location_is_fixed loc then LoadMem loc
        else
          (case inst_store_ptr inst of
             NONE => LoadMem memory_location_undefined
           | SOME op => LoadOp op)
End

Definition lattice_merge_def:
  lattice_merge preds bb_map =
    case preds of
      [] => []
    | p::ps =>
        let res0 = bb_lattice_lookup bb_map p in
        FOLDL
          (λacc pred.
             let other = bb_lattice_lookup bb_map pred in
             let common = FILTER (λk. MEM k (lattice_keys other)) (lattice_keys acc) in
             FOLDL
               (λacc2 key.
                  let v1 = lattice_lookup key acc in
                  let v2 = lattice_lookup key other in
                  lattice_update key (ordset_union v1 v2) acc2)
               [] common)
          res0 ps
End

Definition load_analysis_handle_bb_def:
  load_analysis_handle_bb fn cfg dfg bpa mem_alias_opt eff inst_map bb_map bb =
    let preds = fmap_lookup_ordset cfg.cfg_in bb.bb_label in
    let lattice0 = lattice_merge preds bb_map in
    let (inst_map1, lattice1) =
      FOLDL
        (λstate inst.
           let (imap, lat) = state in
           let load_op = load_effect_load_op eff in
           let store_op = load_effect_store_op eff in
           if inst.inst_opcode = load_op then
             let imap1 = inst_lattice_update imap inst.inst_id lat in
             let ptr = load_key_of_read bpa eff inst in
             (case inst_output inst of
                NONE => (imap1, lat)
              | SOME out =>
                  let lat1 = lattice_update ptr [Var out] lat in
                  (imap1, lat1))
           else if store_op <> NONE /\ inst.inst_opcode = THE store_op then
             let imap1 = inst_lattice_update imap inst.inst_id lat in
             (case inst.inst_operands of
                (val::_) =>
                  let ptr = load_key_of_write bpa eff inst in
                  let memloc = load_key_memloc bpa (load_effect_word_scale eff) ptr in
                  let lat1 =
                    case mem_alias_opt of
                      NONE => lat
                    | SOME ma =>
                        FOLDL
                          (λacc key.
                             let loc = load_key_memloc bpa (load_effect_word_scale eff) key in
                             if mem_alias_may_alias ma loc memloc then lattice_remove key acc else acc)
                          lat (lattice_keys lat) in
                  let lat2 = lattice_update ptr [val] lat1 in
                  (imap1, lat2)
              | _ => (imap1, lat))
           else
             (case load_effect_write_effect eff of
                NONE => (imap, lat)
              | SOME e =>
                  if e IN write_effects inst.inst_opcode then (imap, [])
                  else (imap, lat)))
        (inst_map, lattice0) bb.bb_instructions in
    let before = bb_lattice_lookup bb_map bb.bb_label in
    let bb_map1 = bb_lattice_update bb_map bb.bb_label lattice1 in
    (inst_map1, bb_map1, before <> lattice1)
End

Definition load_analysis_iter_def:
  load_analysis_iter 0 fn cfg dfg bpa mem_alias_opt eff inst_map bb_map work =
    (inst_map, bb_map) /\
  load_analysis_iter (SUC fuel) fn cfg dfg bpa mem_alias_opt eff inst_map bb_map work =
    case work of
      [] => (inst_map, bb_map)
    | lbl::rest =>
        (case lookup_block lbl fn.fn_blocks of
           NONE => load_analysis_iter fuel fn cfg dfg bpa mem_alias_opt eff inst_map bb_map rest
         | SOME bb =>
             let (imap1, bbmap1, changed) =
               load_analysis_handle_bb fn cfg dfg bpa mem_alias_opt eff inst_map bb_map bb in
             let succs = fmap_lookup_ordset cfg.cfg_out lbl in
             let work' = if changed then rest ++ succs else rest in
             load_analysis_iter fuel fn cfg dfg bpa mem_alias_opt eff imap1 bbmap1 work')
End

Definition load_analysis_effect_def:
  load_analysis_effect ctx fn cfg dfg bpa eff =
    let mem_alias_opt =
      case load_effect_to_space eff of
        NONE => NONE
      | SOME space =>
          (case load_effect_store_op eff of
             NONE => NONE
           | SOME _ => SOME (mem_alias_analyze space ctx fn cfg bpa)) in
    let fuel = (LENGTH fn.fn_blocks + 1) * (LENGTH fn.fn_blocks + 1) in
    load_analysis_iter fuel fn cfg dfg bpa mem_alias_opt eff [] [] cfg.dfs_pre
End

Definition load_elim_equivalent_def:
  load_elim_equivalent fn dfg op1 op2 =
    dfg_are_equivalent fn dfg op1 op2
End

Definition find_join_block_def:
  find_join_block 0 fn cfg lbl = lbl /\
  find_join_block (SUC fuel) fn cfg lbl =
    let preds = fmap_lookup_ordset cfg.cfg_in lbl in
    if LENGTH preds = 1 then
      find_join_block fuel fn cfg (HD preds)
    else lbl
End

Definition load_elim_handle_load_def:
  load_elim_handle_load updater fn cfg bpa eff inst_map bb_map bb_label inst =
    let lat = inst_lattice_lookup inst_map inst.inst_id in
    let ptr = load_key_of_read bpa eff inst in
    let existing = lattice_lookup ptr lat in
    if LENGTH existing = 1 then
      inst_updater_mk_assign updater inst (HD existing) NONE
    else if LENGTH existing > 1 then
      let fuel = LENGTH fn.fn_blocks + 1 in
      let join_lbl = find_join_block fuel fn cfg bb_label in
      (case lookup_block join_lbl fn.fn_blocks of
         NONE => updater
       | SOME join_bb =>
           case join_bb.bb_instructions of
             [] => updater
           | first_inst::_ =>
               let preds = fmap_lookup_ordset cfg.cfg_in join_lbl in
               let ops =
                 FOLDL
                   (λacc pred.
                      let pred_lat = bb_lattice_lookup bb_map pred in
                      if lattice_lookup ptr pred_lat = [] then acc
                      else
                        let vals = lattice_lookup ptr pred_lat in
                        if LENGTH vals <> 1 then acc
                        else
                          case HD vals of
                            Var v => acc ++ [Label pred; Var v]
                          | _ => acc)
                   [] preds in
               if LENGTH ops <> 2 * LENGTH existing then updater
               else
                 let (up1, out_opt) = inst_updater_add_before updater first_inst PHI ops in
                 (case out_opt of
                    NONE => updater
                  | SOME v => inst_updater_mk_assign up1 inst (Var v) NONE))
    else updater
End

Definition load_elim_handle_store_def:
  load_elim_handle_store updater fn dfg bpa eff inst_map inst =
    let lat = inst_lattice_lookup inst_map inst.inst_id in
    case inst.inst_operands of
      val::_ =>
        let ptr = load_key_of_write bpa eff inst in
        let existing = lattice_lookup ptr lat in
        if existing = [] then updater
        else if EVERY (λtmp. load_elim_equivalent fn dfg val tmp) existing then
          inst_updater_nop updater inst
        else updater
    | _ => updater
End

Definition load_elim_run_effect_def:
  load_elim_run_effect updater fn cfg dfg bpa eff inst_map bb_map =
    FOLDL
      (λup bb.
         FOLDL
           (λacc inst.
              let load_op = load_effect_load_op eff in
              let store_op = load_effect_store_op eff in
              if inst.inst_opcode = load_op then
                load_elim_handle_load acc fn cfg bpa eff inst_map bb_map bb.bb_label inst
              else if store_op <> NONE /\ inst.inst_opcode = THE store_op then
                load_elim_handle_store acc fn dfg bpa eff inst_map inst
              else acc)
           up bb.bb_instructions)
      updater fn.fn_blocks
End

Definition load_elim_function_def:
  load_elim_function ctx fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let bpa = base_ptr_analyze ctx fn cfg in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let (imap_m, bbmap_m) = load_analysis_effect ctx fn cfg dfg bpa LE_MEMORY in
    let updater1 = load_elim_run_effect updater fn cfg dfg bpa LE_MEMORY imap_m bbmap_m in
    let (imap_t, bbmap_t) = load_analysis_effect ctx fn cfg dfg bpa LE_TRANSIENT in
    let updater2 = load_elim_run_effect updater1 fn cfg dfg bpa LE_TRANSIENT imap_t bbmap_t in
    let (imap_s, bbmap_s) = load_analysis_effect ctx fn cfg dfg bpa LE_STORAGE in
    let updater3 = load_elim_run_effect updater2 fn cfg dfg bpa LE_STORAGE imap_s bbmap_s in
    let (imap_d, bbmap_d) = load_analysis_effect ctx fn cfg dfg bpa LE_DLOAD in
    let updater4 = load_elim_run_effect updater3 fn cfg dfg bpa LE_DLOAD imap_d bbmap_d in
    let (imap_c, bbmap_c) = load_analysis_effect ctx fn cfg dfg bpa LE_CALLDATALOAD in
    let updater5 = load_elim_run_effect updater4 fn cfg dfg bpa LE_CALLDATALOAD imap_c bbmap_c in
    updater5.iu_fn
End

Definition load_elim_context_def:
  load_elim_context ctx =
    ctx with ctx_functions := MAP (load_elim_function ctx) ctx.ctx_functions
End

val _ = export_theory();
