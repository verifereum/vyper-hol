(*
 * Concretize Memory Location Pass
 *
 * Port of venom/passes/concretize_mem_loc.py.
 *)

Theory concretizeMemLoc
Ancestors
  list pred_set sorting
  orderedSet
  irOps
  cfgAnalysis dfgAnalysis basePtrAnalysis
  memoryLocation memoryAllocator
  instUpdater compilerState
  venomInst

Type inst_alloc_map = ``:(num # allocation list) list``
Type alloc_inst_map = ``:(allocation # num list) list``

Definition inst_alloc_lookup_def:
  inst_alloc_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition inst_alloc_update_def:
  inst_alloc_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition alloc_inst_lookup_def:
  alloc_inst_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition alloc_inst_update_def:
  alloc_inst_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition alloc_inst_add_def:
  alloc_inst_add m k v = alloc_inst_update m k (ordset_add v (alloc_inst_lookup m k))
End

Definition find_base_ptrs_op_def:
  find_base_ptrs_op bpa op =
    case op of
      Var v => ptrs_of_var bpa v
    | _ => []
End

Definition find_base_ptrs_opt_def:
  find_base_ptrs_opt bpa op_opt =
    case op_opt of
      NONE => []
    | SOME op => find_base_ptrs_op bpa op
End

Definition find_first_inst_id_def:
  find_first_inst_id bb =
    case bb.bb_instructions of
      [] => NONE
    | inst::_ => SOME inst.inst_id
End

Definition find_last_inst_id_def:
  find_last_inst_id bb =
    case bb.bb_instructions of
      [] => NONE
    | insts => SOME (LAST insts).inst_id
End

Definition live_palloca_allocations_def:
  live_palloca_allocations fn =
    let insts = fn_instructions_list fn in
    FOLDL
      (λacc inst.
         if inst.inst_opcode = PALLOCA then
           case allocation_of_inst inst of
             NONE => acc
           | SOME alloc => ordset_add alloc acc
         else acc)
      [] insts
End

Definition mem_liveness_handle_liveat_def:
  mem_liveness_handle_liveat fn cfg dfg bpa allocator liveat used bb =
    case bb.bb_instructions of
      [] => (liveat, F)
    | insts =>
        let succs = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
        let live =
          FOLDL
            (λacc lbl.
               case lookup_block lbl fn.fn_blocks of
                 NONE => acc
               | SOME succ =>
                   case find_first_inst_id succ of
                     NONE => acc
                   | SOME iid => ordset_union acc (inst_alloc_lookup liveat iid))
            [] succs in
        let first_id = (HD insts).inst_id in
        let before = inst_alloc_lookup liveat first_id in
        let (liveat', _) =
          FOLDL
            (λstate inst.
               let (live_map, live_set) = state in
               let write_op = get_memory_write_op inst in
               let read_op = get_memory_read_op inst in
               let write_ptrs = find_base_ptrs_opt bpa write_op in
               let read_ptrs = find_base_ptrs_opt bpa read_op in
               let live1 =
                 FOLDL (λacc p. ordset_add p.ptr_alloca acc) live_set read_ptrs in
               let live2 =
                 if inst.inst_opcode = INVOKE then
                   (case inst.inst_operands of
                      (Label callee :: _) =>
                        (case FLOOKUP allocator.ma_mems_used callee of
                           NONE => live1
                         | SOME mems => ordset_union live1 mems)
                    | _ => live1)
                 else live1 in
               let live3 =
                 if inst.inst_opcode = INVOKE then
                   FOLDL
                     (λacc op. ordset_union acc (MAP (λp. p.ptr_alloca) (find_base_ptrs_op bpa op)))
                     live2 inst.inst_operands
                 else live2 in
               let live_map' = inst_alloc_update live_map inst.inst_id live3 in
               let live4 =
                 FOLDL
                   (λacc p.
                      case get_write_size inst of
                        SOME (Lit w) =>
                          if MEM p.ptr_alloca acc /\ w2n w = p.ptr_alloca.alloc_size then
                            let acc1 = ordset_remove p.ptr_alloca acc in
                            if MEM p.ptr_alloca (MAP (λq. q.ptr_alloca) read_ptrs) then
                              ordset_add p.ptr_alloca acc1
                            else acc1
                          else acc
                      | _ => acc)
                   live3 write_ptrs in
               (live_map', live4))
            (liveat, live) (REVERSE insts) in
        let after = inst_alloc_lookup liveat' first_id in
        (liveat', before <> after)
End

Definition mem_liveness_handle_used_def:
  mem_liveness_handle_used fn cfg bpa allocator used bb =
    case bb.bb_instructions of
      [] => (used, F)
    | insts =>
        let used0 = live_palloca_allocations fn in
        let preds = fmap_lookup_ordset cfg.cfg_in bb.bb_label in
        let used1 =
          FOLDL
            (λacc lbl.
               case lookup_block lbl fn.fn_blocks of
                 NONE => acc
               | SOME pred =>
                   case find_last_inst_id pred of
                     NONE => acc
                   | SOME iid => ordset_union acc (inst_alloc_lookup used iid))
            used0 preds in
        let last_id = (LAST insts).inst_id in
        let before = inst_alloc_lookup used last_id in
        let (used', _) =
          FOLDL
            (λstate inst.
               let (used_map, used_set) = state in
               let used1 =
                 FOLDL
                   (λacc op. ordset_union acc (MAP (λp. p.ptr_alloca) (find_base_ptrs_op bpa op)))
                   used_set inst.inst_operands in
               let used2 =
                 if inst.inst_opcode = INVOKE then
                   (case inst.inst_operands of
                      (Label callee :: _) =>
                        (case FLOOKUP allocator.ma_mems_used callee of
                           NONE => used1
                         | SOME mems => ordset_union used1 mems)
                    | _ => used1)
                 else used1 in
               let used_map' = inst_alloc_update used_map inst.inst_id used2 in
               (used_map', used2))
            (used, used1) insts in
        let after = inst_alloc_lookup used' last_id in
        (used', before <> after)
End

Definition mem_liveness_iter_def:
  mem_liveness_iter 0 fn cfg dfg bpa allocator liveat used = (liveat, used) /\
  mem_liveness_iter (SUC fuel) fn cfg dfg bpa allocator liveat used =
    let (liveat1, ch1) =
      FOLDL
        (λacc lbl.
           let (lm, ch) = acc in
           case lookup_block lbl fn.fn_blocks of
             NONE => (lm, ch)
           | SOME bb =>
               let (lm', changed) = mem_liveness_handle_liveat fn cfg dfg bpa allocator lm used bb in
               (lm', ch \/ changed))
        (liveat, F) cfg.dfs_post in
    let (used1, ch2) =
      FOLDL
        (λacc lbl.
           let (um, ch) = acc in
           case lookup_block lbl fn.fn_blocks of
             NONE => (um, ch)
           | SOME bb =>
               let (um', changed) = mem_liveness_handle_used fn cfg bpa allocator um bb in
               (um', ch \/ changed))
        (used, F) cfg.dfs_pre in
    if ~(ch1 \/ ch2) then (liveat1, used1)
    else mem_liveness_iter fuel fn cfg dfg bpa allocator liveat1 used1
End

Definition mem_liveness_build_livesets_def:
  mem_liveness_build_livesets liveat used =
    FOLDL
      (λacc (iid, mems).
         FOLDL
           (λacc2 mem.
              if MEM mem (inst_alloc_lookup used iid) then
                alloc_inst_add acc2 mem iid
              else acc2)
           acc mems)
      [] liveat
End

Definition mem_liveness_analyze_def:
  mem_liveness_analyze fn cfg dfg bpa allocator =
    let fuel = (LENGTH fn.fn_blocks + 1) * (LENGTH fn.fn_blocks + 1) in
    let (liveat, used) = mem_liveness_iter fuel fn cfg dfg bpa allocator [] [] in
    let livesets = mem_liveness_build_livesets liveat used in
    livesets
End

Definition sort_livesets_def:
  sort_livesets livesets =
    QSORT (λa b. LENGTH (SND a) < LENGTH (SND b)) livesets
End

Definition concretize_allocate_all_def:
  concretize_allocate_all allocator livesets =
    let already = FILTER (λp. mem_allocator_is_allocated (FST p) allocator) livesets in
    let to_alloc = FILTER (λp. ~mem_allocator_is_allocated (FST p) allocator) livesets in
    let to_alloc' = sort_livesets to_alloc in
    let allocator1 = mem_allocator_add_allocated (MAP FST already) allocator in
    let (allocator2, _) =
      FOLDL
        (λacc (mem, insts).
           let (st, known) = acc in
           let st1 = mem_allocator_reset st in
           let st2 =
             FOLDL
               (λst' (mem2, insts2).
                  if ordset_inter insts insts2 = [] then st'
                  else mem_allocator_reserve mem2 st')
               st1 known in
           let (_, st3) = mem_allocator_allocate mem st2 in
           (st3, known ++ [(mem, insts)]))
        (allocator1, already) to_alloc' in
    allocator2
End

Definition concretize_remove_unused_calloca_def:
  concretize_remove_unused_calloca updater inst =
    let uses = dfg_get_transitive_uses updater.iu_fn updater.iu_dfg inst.inst_id in
    inst_updater_nop_multi updater uses
End

Definition concretize_handle_inst_def:
  concretize_handle_inst bpa (updater, allocator) inst =
    if inst.inst_opcode IN {ALLOCA; PALLOCA; CALLOCA} then
      case inst_output inst of
        NONE => (updater, allocator)
      | SOME out =>
          (case ptr_from_op bpa (Var out) of
             NONE =>
               if inst.inst_opcode = CALLOCA then
                 (concretize_remove_unused_calloca updater inst, allocator)
               else (updater, allocator)
           | SOME base_ptr =>
               let allocator1 =
                 if mem_allocator_is_allocated base_ptr.ptr_alloca allocator then allocator
                 else SND (mem_allocator_allocate base_ptr.ptr_alloca allocator) in
               let concrete = mem_allocator_get_concrete allocator1 base_ptr in
               let updater1 = inst_updater_update updater inst ASSIGN [concrete] NONE in
               (updater1, allocator1))
    else if inst.inst_opcode = GEP then
      (inst_updater_update updater inst ADD inst.inst_operands NONE, allocator)
    else (updater, allocator)
End

Definition concretize_handle_bb_def:
  concretize_handle_bb bpa updater allocator bb =
    FOLDL
      (λacc inst. concretize_handle_inst bpa acc inst)
      (updater, allocator) bb.bb_instructions
End

Definition concretize_mem_loc_function_def:
  concretize_mem_loc_function allocator ctx fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let bpa = base_ptr_analyze ctx fn cfg in
    let livesets = mem_liveness_analyze fn cfg dfg bpa allocator in
    let allocator1 = mem_allocator_start_fn_allocation fn.fn_name allocator in
    let allocator2 = concretize_allocate_all allocator1 livesets in
    let allocator3 = mem_allocator_reserve_all allocator2 in
    let updater0 =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let (updater1, allocator4) =
      FOLDL
        (λacc bb.
           let (up, al) = acc in
           concretize_handle_bb bpa up al bb)
        (updater0, allocator3) fn.fn_blocks in
    let allocator5 = mem_allocator_end_fn_allocation allocator4 in
    (updater1.iu_fn, allocator5)
End

Definition concretize_mem_loc_context_def:
  concretize_mem_loc_context allocator ctx =
    let (fns, allocator') =
      FOLDL
        (λacc fn.
           let (fs, al) = acc in
           let (fn', al') = concretize_mem_loc_function al ctx fn in
           (fs ++ [fn'], al'))
        ([], allocator) ctx.ctx_functions in
    (ctx with ctx_functions := fns, allocator')
End

val _ = export_theory();
