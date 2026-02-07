(*
 * Dead Store Elimination Pass
 *
 * Port of venom/passes/dead_store_elimination.py.
 *)

Theory deadStoreElim
Ancestors
  list pred_set
  irOps
  cfgAnalysis dfgAnalysis dominatorsAnalysis basePtrAnalysis
  memSSAAnalysis memAliasAnalysis analysisCache
  instUpdater compilerState
  addrSpace
  memoryLocation
  venomSem

Definition non_related_effects_def:
  non_related_effects MEMORY = all_effects DIFF {Eff_MEMORY; Eff_MSIZE} /\
  non_related_effects STORAGE = all_effects DIFF {Eff_STORAGE} /\
  non_related_effects TRANSIENT = all_effects DIFF {Eff_TRANSIENT}
End

Definition inst_outputs_have_uses_def:
  inst_outputs_have_uses dfg inst =
    EXISTS (λv. dfg_get_uses dfg v <> []) inst.inst_outputs
End

Definition find_inst_block_def:
  find_inst_block iid [] = NONE /\
  find_inst_block iid (bb::bbs) =
    case find_inst_index iid bb.bb_instructions of
      NONE => find_inst_block iid bbs
    | SOME idx => SOME (bb.bb_label, idx)
End

Definition mem_def_live_scan_def:
  mem_def_live_scan query_loc mem_ssa [] = NONE /\
  mem_def_live_scan query_loc mem_ssa (inst::rest) =
    case mem_ssa_get_memory_use mem_ssa inst.inst_id of
      SOME u =>
        if mem_alias_may_alias mem_ssa.msa_mem_alias u.mu_loc query_loc then SOME T
        else
          (case mem_ssa_get_memory_def mem_ssa inst.inst_id of
             SOME d =>
               if memory_location_completely_contains d.md_loc query_loc then SOME F
               else mem_def_live_scan query_loc mem_ssa rest
           | NONE => mem_def_live_scan query_loc mem_ssa rest)
    | NONE =>
        (case mem_ssa_get_memory_def mem_ssa inst.inst_id of
           SOME d =>
             if memory_location_completely_contains d.md_loc query_loc then SOME F
             else mem_def_live_scan query_loc mem_ssa rest
         | NONE => mem_def_live_scan query_loc mem_ssa rest)
End

Definition mem_def_live_iter_def:
  mem_def_live_iter 0 fn cfg mem_ssa query_loc worklist visited = F /\
  mem_def_live_iter (SUC fuel) fn cfg mem_ssa query_loc worklist visited =
    case worklist of
      [] => F
    | (lbl, idx)::rest =>
        (case lookup_block lbl fn.fn_blocks of
           NONE => mem_def_live_iter fuel fn cfg mem_ssa query_loc rest visited
         | SOME bb =>
             let insts = DROP idx bb.bb_instructions in
             case mem_def_live_scan query_loc mem_ssa insts of
               SOME T => T
             | SOME F => mem_def_live_iter fuel fn cfg mem_ssa query_loc rest visited
             | NONE =>
                 let succs = fmap_lookup_ordset cfg.cfg_out lbl in
                 let new = FILTER (λl. ~MEM l visited) succs in
                 let visited' = visited ++ new in
                 let worklist' = rest ++ MAP (λl. (l, 0)) new in
                 mem_def_live_iter fuel fn cfg mem_ssa query_loc worklist' visited')
End

Definition mem_def_live_def:
  mem_def_live fn cfg mem_ssa def =
    case find_inst_block def.md_inst_id fn.fn_blocks of
      NONE => F
    | SOME (lbl, idx) =>
        let fuel = (LENGTH fn.fn_blocks + 1) * (LENGTH fn.fn_blocks + 1) in
        mem_def_live_iter fuel fn cfg mem_ssa def.md_loc [(lbl, idx + 1)] []
End

Definition dead_store_is_dead_def:
  dead_store_is_dead fn cfg dfg mem_ssa space def =
    let loc = def.md_loc in
    if loc.ml_volatile then F
    else if ~memory_location_is_fixed loc then F
    else
      case lookup_inst_in_function def.md_inst_id fn of
        NONE => F
      | SOME inst =>
          if inst_outputs_have_uses dfg inst then F
          else
            let eff = write_effects inst.inst_opcode UNION read_effects inst.inst_opcode in
            let has_other = ~(eff INTER non_related_effects space = {}) in
            if has_other then F
            else ~mem_def_live fn cfg mem_ssa def
End

Definition dead_store_elim_step_def:
  dead_store_elim_step fn space ctx volatiles =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let dom_opt = dominators_analyze fn cfg in
    let dom = case dom_opt of NONE => dominators_empty | SOME d => d in
    let bpa = base_ptr_analyze ctx fn cfg in
    let mem_ssa = mem_ssa_analyze space ctx fn cfg dom bpa in
    let mem_ssa' =
      FOLDL (λacc loc. FST (mem_ssa_mark_location_volatile acc loc)) mem_ssa volatiles in
    let volatiles' = mem_ssa'.msa_volatiles in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let (updater', changed) =
      FOLDL
        (λacc def.
           let (up, ch) = acc in
           if dead_store_is_dead up.iu_fn cfg up.iu_dfg mem_ssa' space def then
             case lookup_inst_in_function def.md_inst_id up.iu_fn of
               NONE => (up, ch)
             | SOME inst => (inst_updater_nop up inst, T)
           else (up, ch))
        (updater, F) (mem_ssa_get_memory_defs mem_ssa') in
    (updater'.iu_fn, volatiles', changed)
End

Definition dead_store_elim_iter_def:
  dead_store_elim_iter 0 fn space ctx volatiles = fn /\
  dead_store_elim_iter (SUC fuel) fn space ctx volatiles =
    let (fn1, volatiles1, changed) = dead_store_elim_step fn space ctx volatiles in
    if ~changed then fn1
    else dead_store_elim_iter fuel fn1 space ctx volatiles1
End

Definition dead_store_elim_function_def:
  dead_store_elim_function ctx space fn =
    let n = LENGTH (fn_instructions_list fn) in
    let fuel = (n + 1) * (n + 1) in
    dead_store_elim_iter fuel fn space ctx []
End

Definition dead_store_elim_context_def:
  dead_store_elim_context ctx space =
    ctx with ctx_functions := MAP (dead_store_elim_function ctx space) ctx.ctx_functions
End

val _ = export_theory();
