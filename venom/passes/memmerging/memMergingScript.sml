(*
 * Memory Merging Pass
 *
 * Port of venom/passes/memmerging.py.
 *)

Theory memMerging
Ancestors
  list pred_set sorting
  orderedSet
  irOps dfgAnalysis
  instUpdater compilerState
  venomSem

Datatype:
  interval = <|
    int_start : num;
    int_length : num
  |>
End

Definition interval_end_def:
  interval_end iv = iv.int_start + iv.int_length
End

Definition interval_overlaps_def:
  interval_overlaps a b =
    let start = MAX a.int_start b.int_start in
    let finish = MIN (interval_end a) (interval_end b) in
    start < finish
End

Datatype:
  mem_copy = <|
    mc_dst : num;
    mc_src : num;
    mc_len : num;
    mc_insts : num list
  |>
End

Definition copy_memzero_def:
  copy_memzero dst len insts = <| mc_dst := dst; mc_src := dst; mc_len := len; mc_insts := insts |>
End

Definition copy_src_end_def:
  copy_src_end c = c.mc_src + c.mc_len
End

Definition copy_dst_end_def:
  copy_dst_end c = c.mc_dst + c.mc_len
End

Definition copy_src_interval_def:
  copy_src_interval c = <| int_start := c.mc_src; int_length := c.mc_len |>
End

Definition copy_dst_interval_def:
  copy_dst_interval c = <| int_start := c.mc_dst; int_length := c.mc_len |>
End

Definition copy_overwrites_def:
  copy_overwrites c iv = interval_overlaps (copy_dst_interval c) iv
End

Definition copy_overwrites_self_src_def:
  copy_overwrites_self_src c = copy_overwrites c (copy_src_interval c)
End

Definition copy_can_merge_def:
  copy_can_merge a b <=>
    (a.mc_src - b.mc_src = a.mc_dst - b.mc_dst) /\
    b.mc_dst <= copy_dst_end a
End

Definition copy_merge_def:
  copy_merge a b =
    let new_len = MAX (copy_dst_end a) (copy_dst_end b) - a.mc_dst in
    a with <| mc_len := new_len; mc_insts := a.mc_insts ++ b.mc_insts |>
End

Definition copy_insert_sorted_def:
  copy_insert_sorted c [] = [c] /\
  copy_insert_sorted c (x::xs) =
    if c.mc_dst <= x.mc_dst then c :: x :: xs
    else x :: copy_insert_sorted c xs
End

Definition copy_merge_adjacent_aux_def:
  copy_merge_adjacent_aux fuel [] = [] /\
  copy_merge_adjacent_aux fuel [c] = [c] /\
  copy_merge_adjacent_aux 0 (c1::c2::rest) = c1::c2::rest /\
  copy_merge_adjacent_aux (SUC fuel') (c1::c2::rest) =
    if copy_can_merge c1 c2 then
      copy_merge_adjacent_aux fuel' (copy_merge c1 c2 :: rest)
    else c1 :: copy_merge_adjacent_aux fuel' (c2::rest)
End

Definition copy_merge_adjacent_def:
  copy_merge_adjacent copies =
    copy_merge_adjacent_aux (LENGTH copies + 1) copies
End

Definition copy_add_def:
  copy_add copies c = copy_merge_adjacent (copy_insert_sorted c copies)
End

Definition copy_remove_def:
  copy_remove c [] = [] /\
  copy_remove c (x::xs) = if x = c then xs else x :: copy_remove c xs
End

Definition load_lookup_def:
  load_lookup m k = ALOOKUP m k
End

Definition load_update_def:
  load_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition load_remove_def:
  load_remove m k = FILTER (λ(kk,_). kk <> k) m
End

Definition inst_index_or_def:
  inst_index_or iid insts =
    case find_inst_index iid insts of
      NONE => 0
    | SOME idx => idx
End

Definition inst_id_in_block_def:
  inst_id_in_block iid bb =
    MEM iid (MAP (λinst. inst.inst_id) bb.bb_instructions)
End

Definition sort_inst_ids_by_block_def:
  sort_inst_ids_by_block insts ids =
    QSORT (λa b. inst_index_or a insts < inst_index_or b insts) ids
End

Definition volatile_memory_def:
  volatile_memory inst =
    let eff = read_effects inst.inst_opcode UNION write_effects inst.inst_opcode in
    Eff_MEMORY IN eff \/ Eff_MSIZE IN eff
End

Definition copies_that_overwrite_def:
  copies_that_overwrite copies iv =
    FILTER (λc. copy_overwrites c iv) copies
End

Definition write_after_write_hazards_def:
  write_after_write_hazards copies new_copy =
    FILTER
      (λc.
         ~(copy_can_merge c new_copy) /\
         ~(copy_can_merge new_copy c) /\
         copy_overwrites new_copy (copy_dst_interval c))
      copies
End

Definition read_after_write_hazards_def:
  read_after_write_hazards copies new_copy =
    copies_that_overwrite copies (copy_src_interval new_copy)
End

Definition write_after_read_hazards_def:
  write_after_read_hazards copies new_copy =
    FILTER (λc. copy_overwrites new_copy (copy_src_interval c)) copies
End

Definition invalidate_loads_def:
  invalidate_loads loads iv =
    FILTER
      (λp.
         let ptr = SND p in
         ~interval_overlaps iv <| int_start := ptr; int_length := 32 |>)
      loads
End

Definition memmerge_flush_one_def:
  memmerge_flush_one updater bb copy load_op copy_op =
    let insts = bb.bb_instructions in
    let ids = sort_inst_ids_by_block insts copy.mc_insts in
    case ids of
      [] => (updater, copy)
    | _ =>
        let last_id = LAST ids in
        case lookup_inst_in_function last_id updater.iu_fn of
          NONE => (updater, copy)
        | SOME inst =>
            let (up1, pin_opt) =
              if copy.mc_len <> 32 \/ load_op = DLOAD then
                let ops = [Lit (n2w copy.mc_len); Lit (n2w copy.mc_src); Lit (n2w copy.mc_dst)] in
                (inst_updater_update updater inst copy_op ops NONE, NONE)
              else if inst.inst_opcode = MSTORE then
                (case inst.inst_operands of
                   (Var v :: _) =>
                     (case dfg_get_producing updater.iu_dfg v of
                        NONE => (updater, NONE)
                      | SOME pid => (updater, SOME pid))
                 | _ => (updater, NONE))
              else
                let (up2, out_opt) = inst_updater_add_before updater inst load_op [Lit (n2w copy.mc_src)] in
                (case out_opt of
                   NONE => (up2, NONE)
                 | SOME v =>
                     let up3 = inst_updater_update up2 inst MSTORE [Var v; Lit (n2w copy.mc_dst)] NONE in
                     (up3, NONE)) in
            let to_nop =
              FILTER
                (λiid.
                   if iid = last_id then F
                   else
                     case lookup_inst_in_function iid up1.iu_fn of
                       NONE => F
                     | SOME i =>
                         if i.inst_opcode = load_op then
                           (case pin_opt of
                              SOME pid => if iid = pid then F
                                          else
                                            (case inst_output i of
                                               NONE => F
                                             | SOME v =>
                                                 EVERY (λu. MEM u ids) (dfg_get_uses up1.iu_dfg v))
                            | NONE =>
                                (case inst_output i of
                                   NONE => F
                                 | SOME v =>
                                     EVERY (λu. MEM u ids) (dfg_get_uses up1.iu_dfg v)))
                         else T)
                ids in
            let up2 = inst_updater_nop_multi up1 to_nop in
            (up2, copy)
End

Definition memmerge_flush_copies_def:
  memmerge_flush_copies updater bb copies load_op copy_op to_flush =
    FOLDL
      (λacc c.
         let (up, cs) = acc in
         let (up', _) = memmerge_flush_one up bb c load_op copy_op in
         (up', copy_remove c cs))
      (updater, copies) to_flush
End

Definition memmerge_barrier_def:
  memmerge_barrier updater bb copies load_op copy_op =
    let (up, _) = memmerge_flush_copies updater bb copies load_op copy_op copies in
    (up, ([]:mem_copy list), ([]:(string # num) list))
End

Definition memmerge_handle_bb_def:
  memmerge_handle_bb updater bb load_op copy_op allow_overlap =
    let insts = bb.bb_instructions in
    let (up1, copies1, loads1) =
      FOLDL
        (λacc inst.
           let (up, copies, loads) = acc in
           if inst.inst_opcode = load_op then
             (case inst.inst_operands of
                (Lit w :: _) =>
                  let ptr = w2n w in
                  let read_iv = <| int_start := ptr; int_length := 32 |> in
                  let (up2, copies2, loads2) =
                    if allow_overlap then (up, copies, loads)
                    else
                      let hazards = copies_that_overwrite copies read_iv in
                      let (up', copies') = memmerge_flush_copies up bb copies load_op copy_op hazards in
                      (up', copies', loads) in
                  (case inst_output inst of
                     NONE => (up2, copies2, loads2)
                   | SOME v =>
                       (up2, copies2, load_update loads2 v ptr))
              | _ => memmerge_barrier up bb copies load_op copy_op)
           else if inst.inst_opcode = MSTORE then
             (case inst.inst_operands of
                (Var v :: Lit w :: _) =>
                  (case load_lookup loads v of
                     NONE => memmerge_barrier up bb copies load_op copy_op
                   | SOME src_ptr =>
                       let loads2 =
                         if allow_overlap then loads
                         else invalidate_loads loads <| int_start := w2n w; int_length := 32 |> in
                       let load_inst =
                         case dfg_get_producing up.iu_dfg v of
                           NONE => []
                         | SOME pid => [pid] in
                       let new_copy =
                         <| mc_dst := w2n w;
                            mc_src := src_ptr;
                            mc_len := 32;
                            mc_insts := inst.inst_id :: load_inst |> in
                       let hazards = write_after_write_hazards copies new_copy in
                       let (up2, copies2) =
                         if hazards = [] then (up, copies)
                         else memmerge_flush_copies up bb copies load_op copy_op hazards in
                       let (up3, copies3) =
                         if allow_overlap then (up2, copies2)
                         else
                           let hazards1 = read_after_write_hazards copies2 new_copy in
                           let (up4, copies4) =
                             if hazards1 = [] then (up2, copies2)
                             else memmerge_flush_copies up2 bb copies2 load_op copy_op hazards1 in
                           let hazards2 = write_after_read_hazards copies4 new_copy in
                           if hazards2 = [] then (up4, copies4)
                           else memmerge_flush_copies up4 bb copies4 load_op copy_op hazards2 in
                       (up3, copy_add copies3 new_copy, loads2))
              | _ => memmerge_barrier up bb copies load_op copy_op)
           else if inst.inst_opcode = copy_op then
             (case inst.inst_operands of
                (Lit lenw :: Lit srcw :: Lit dstw :: _) =>
                  let new_copy =
                    <| mc_dst := w2n dstw;
                       mc_src := w2n srcw;
                       mc_len := w2n lenw;
                       mc_insts := [inst.inst_id] |> in
                  let loads2 =
                    if allow_overlap then loads
                    else invalidate_loads loads <| int_start := w2n dstw; int_length := w2n lenw |> in
                  let hazards = write_after_write_hazards copies new_copy in
                  let (up2, copies2) =
                    if hazards = [] then (up, copies)
                    else memmerge_flush_copies up bb copies load_op copy_op hazards in
                  let (up3, copies3) =
                    if allow_overlap then (up2, copies2)
                    else
                      let hazards1 = read_after_write_hazards copies2 new_copy in
                      let (up4, copies4) =
                        if hazards1 = [] then (up2, copies2)
                        else memmerge_flush_copies up2 bb copies2 load_op copy_op hazards1 in
                      let hazards2 = write_after_read_hazards copies4 new_copy in
                      if hazards2 = [] then (up4, copies4)
                      else memmerge_flush_copies up4 bb copies4 load_op copy_op hazards2 in
                  (up3, copy_add copies3 new_copy, loads2)
              | _ => memmerge_barrier up bb copies load_op copy_op)
           else if volatile_memory inst then
             memmerge_barrier up bb copies load_op copy_op
           else (up, copies, loads))
        (updater, ([]:mem_copy list), ([]:(string # num) list)) insts in
    let (up2, _, _) = memmerge_barrier up1 bb copies1 load_op copy_op in
    up2
End

Definition memzero_optimize_def:
  memzero_optimize updater bb copies =
    let insts = bb.bb_instructions in
    FOLDL
      (λup c.
         let ids = sort_inst_ids_by_block insts c.mc_insts in
         case ids of
           [] => up
         | _ =>
             let last_id = LAST ids in
             case lookup_inst_in_function last_id up.iu_fn of
               NONE => up
             | SOME inst =>
                 let up1 =
                   if c.mc_len = 32 then
                     inst_updater_update up inst MSTORE [Lit 0w; Lit (n2w c.mc_dst)] NONE
                   else
                     let (up2, out_opt) = inst_updater_add_before up inst CALLDATASIZE [] in
                     (case out_opt of
                        NONE => up2
                      | SOME v =>
                          inst_updater_update up2 inst CALLDATACOPY
                            [Lit (n2w c.mc_len); Var v; Lit (n2w c.mc_dst)] NONE) in
                 let to_nop = FILTER (λiid. iid <> last_id) ids in
                 inst_updater_nop_multi up1 to_nop)
      updater copies
End

Definition memmerge_handle_bb_memzero_def:
  memmerge_handle_bb_memzero updater bb =
    let insts = bb.bb_instructions in
    let (up1, copies1) =
      FOLDL
        (λacc inst.
           let (up, copies) = acc in
           if inst.inst_opcode = MSTORE then
            (case inst.inst_operands of
               (Lit w :: Lit dstw :: _) =>
                 if w = 0w then
                   let c = copy_memzero (w2n dstw) 32 [inst.inst_id] in
                   (up, copy_add copies c)
                 else
                   let up' = memzero_optimize up bb copies in
                   (up', [])
             | _ =>
                 let up' = memzero_optimize up bb copies in
                 (up', []))
           else if inst.inst_opcode = CALLDATACOPY then
             (case inst.inst_operands of
                (Lit lenw :: Var v :: Lit dstw :: _) =>
                  (case dfg_get_producing up.iu_dfg v of
                     NONE =>
                       let up' = memzero_optimize up bb copies in
                       (up', [])
                   | SOME pid =>
                       (case lookup_inst_in_function pid up.iu_fn of
                          SOME inst' =>
                            if inst'.inst_opcode = CALLDATASIZE then
                              let c = copy_memzero (w2n dstw) (w2n lenw) [inst.inst_id] in
                              (up, copy_add copies c)
                            else
                              let up' = memzero_optimize up bb copies in
                              (up', [])
                        | NONE =>
                            let up' = memzero_optimize up bb copies in
                            (up', [])))
              | _ =>
                  let up' = memzero_optimize up bb copies in
                  (up', []))
           else if volatile_memory inst then
             let up' = memzero_optimize up bb copies in
             (up', [])
           else (up, copies))
        (updater, []) insts in
    memzero_optimize up1 bb copies1
End

Definition memmerge_merge_mstore_dload_def:
  memmerge_merge_mstore_dload updater bb =
    FOLDL
      (λup inst.
         if inst.inst_opcode <> DLOAD then up
         else
           case inst_output inst of
             NONE => up
           | SOME out =>
               let uses = dfg_get_uses up.iu_dfg out in
               if LENGTH uses = 1 then
                 (case lookup_inst_in_function (HD uses) up.iu_fn of
                    SOME mstore_inst =>
                      if mstore_inst.inst_opcode = MSTORE then
                        (case (inst.inst_operands, mstore_inst.inst_operands) of
                           (src::_ , (Var v)::dst::_) =>
                             if v = out then
                               let up1 =
                                 inst_updater_update up mstore_inst DLOADBYTES
                                   [Lit 32w; src; dst] NONE in
                               inst_updater_nop up1 inst
                             else up
                         | _ => up)
                      else up
                  | _ => up)
               else
                 let uses_bb =
                   FILTER
                     (λiid.
                        case lookup_inst_in_function iid up.iu_fn of
                          NONE => F
                        | SOME i => MEM out (inst_input_vars i) /\ inst_id_in_block iid bb)
                     uses in
                 case uses_bb of
                   [] => up
                 | iid::_ =>
                    (case lookup_inst_in_function iid up.iu_fn of
                       SOME mstore_inst =>
                         if mstore_inst.inst_opcode = MSTORE then
                           (case mstore_inst.inst_operands of
                               (Var v :: dst :: _) =>
                                 if v <> out then up
                                 else
                                   let (vnew, st1) = fresh_var up.iu_state in
                                   let up1 = up with iu_state := st1 in
                                   let (up2, _) =
                                     inst_updater_add_before up1 mstore_inst DLOADBYTES
                                       [Lit 32w; HD inst.inst_operands; dst] in
                                   let up3 =
                                     inst_updater_update up2 mstore_inst MLOAD [dst] (SOME vnew) in
                                   (case lookup_inst_in_function mstore_inst.inst_id up3.iu_fn of
                                      NONE => inst_updater_nop up3 inst
                                    | SOME mload_inst =>
                                        let up4 = inst_updater_move_uses up3 out mload_inst in
                                        inst_updater_nop up4 inst)
                             | _ => up)
                          else up
                      | _ => up))
      updater bb.bb_instructions
End

Definition memmerge_function_def:
  memmerge_function mcopy_available fn =
    let dfg = dfg_analyze fn in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let updater1 =
      FOLDL memmerge_merge_mstore_dload updater updater.iu_fn.fn_blocks in
    let updater2 =
      FOLDL memmerge_handle_bb_memzero updater1 updater1.iu_fn.fn_blocks in
    let updater3 =
      FOLDL
        (λup bb. memmerge_handle_bb up bb CALLDATALOAD CALLDATACOPY T)
        updater2 updater2.iu_fn.fn_blocks in
    let updater4 =
      FOLDL
        (λup bb. memmerge_handle_bb up bb DLOAD DLOADBYTES T)
        updater3 updater3.iu_fn.fn_blocks in
    let updater5 =
      if mcopy_available then
        FOLDL (λup bb. memmerge_handle_bb up bb MLOAD MCOPY F)
          updater4 updater4.iu_fn.fn_blocks
      else updater4 in
    updater5.iu_fn
End

Definition memmerge_context_def:
  memmerge_context mcopy_available ctx =
    ctx with ctx_functions := MAP (memmerge_function mcopy_available) ctx.ctx_functions
End

val _ = export_theory();
