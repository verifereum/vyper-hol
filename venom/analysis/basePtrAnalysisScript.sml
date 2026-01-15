(*
 * Base Pointer Analysis
 *
 * Port of venom/analysis/base_ptr_analysis.py.
 *)

Theory basePtrAnalysis
Ancestors
  list finite_map
  orderedSet
  cfgAnalysis
  memoryLocation basePtrTypes addrSpace
  irOps
  venomSem

Datatype:
  base_ptr_analysis = <|
    var_to_mem : (string, ptr list) fmap
  |>
End

Definition ptrs_of_var_def:
  ptrs_of_var bpa v =
    case FLOOKUP bpa.var_to_mem v of NONE => [] | SOME ps => ps
End

Definition ptr_from_op_def:
  ptr_from_op bpa op =
    case op of
      Var v =>
        let ps = ptrs_of_var bpa v in
        if LENGTH ps = 1 then SOME (HD ps) else NONE
    | _ => NONE
End

Definition fn_instructions_list_def:
  fn_instructions_list fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

Definition segment_from_ops_def:
  segment_from_ops bpa ops =
    let size =
      case ops.ia_size of
        SOME (Lit w) => SOME (w2n w)
      | SOME (Var _) => NONE
      | SOME (Label _) => NONE
      | NONE => NONE in
    case ops.ia_ofst of
      NONE => <| ml_offset := NONE; ml_size := size; ml_alloca := NONE; ml_volatile := F |>
    | SOME (Lit w) =>
        <| ml_offset := SOME (w2n w); ml_size := size; ml_alloca := NONE; ml_volatile := F |>
    | SOME (Var v) =>
        (case ptr_from_op bpa (Var v) of
           NONE => <| ml_offset := NONE; ml_size := size; ml_alloca := NONE; ml_volatile := F |>
         | SOME p =>
             <| ml_offset := p.ptr_offset; ml_size := size;
                ml_alloca := SOME p.ptr_alloca; ml_volatile := F |>)
    | SOME (Label _) =>
        <| ml_offset := NONE; ml_size := size; ml_alloca := NONE; ml_volatile := F |>
End

Definition get_memory_write_location_def:
  get_memory_write_location bpa inst =
    if inst.inst_opcode = DLOAD then
      <| ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F |>
    else if inst.inst_opcode = INVOKE then
      memory_location_undefined
    else if ~(Eff_MEMORY IN write_effects inst.inst_opcode) then
      memory_location_empty
    else
      segment_from_ops bpa (memory_write_ops inst)
End

Definition get_memory_read_location_def:
  get_memory_read_location bpa inst =
    if inst.inst_opcode = DLOAD then
      <| ml_offset := SOME 0; ml_size := SOME 32; ml_alloca := NONE; ml_volatile := F |>
    else if inst.inst_opcode = INVOKE then
      memory_location_undefined
    else if ~(Eff_MEMORY IN read_effects inst.inst_opcode) then
      memory_location_empty
    else
      segment_from_ops bpa (memory_read_ops inst)
End

Definition get_storage_write_location_def:
  get_storage_write_location bpa inst space =
    case addr_space_store_op space of
      NONE => memory_location_empty
    | SOME store_op =>
        if inst.inst_opcode = store_op then
          (case inst.inst_operands of
             _::dst::_ =>
               let ops = inst_access_ops (SOME dst) (SOME (Lit (n2w (addr_space_word_scale space)))) NONE in
               segment_from_ops bpa ops
           | _ => memory_location_empty)
        else if inst.inst_opcode IN {CALL; DELEGATECALL; STATICCALL; INVOKE; CREATE; CREATE2} then
          memory_location_undefined
        else memory_location_empty
End

Definition get_storage_read_location_def:
  get_storage_read_location bpa inst space =
    let load_op = addr_space_load_op space in
    if inst.inst_opcode = load_op then
      (case inst.inst_operands of
         ofst::_ =>
           let ops = inst_access_ops (SOME ofst) (SOME (Lit (n2w (addr_space_word_scale space)))) NONE in
           segment_from_ops bpa ops
       | _ => memory_location_empty)
    else if inst.inst_opcode IN {CALL; DELEGATECALL; STATICCALL; INVOKE; CREATE; CREATE2} then
      memory_location_undefined
    else memory_location_empty
End

Definition get_write_location_def:
  get_write_location bpa inst space =
    case space of
      MEMORY => get_memory_write_location bpa inst
    | STORAGE => get_storage_write_location bpa inst space
    | TRANSIENT => get_storage_write_location bpa inst space
End

Definition get_read_location_def:
  get_read_location bpa inst space =
    case space of
      MEMORY => get_memory_read_location bpa inst
    | STORAGE => get_storage_read_location bpa inst space
    | TRANSIENT => get_storage_read_location bpa inst space
End

Definition find_palloca_inst_def:
  find_palloca_inst fn alloca_id =
    let insts = fn_instructions_list fn in
    FIND (λinst.
            inst.inst_opcode = PALLOCA /\
            case inst.inst_operands of
              (_::Lit w::_) => (w2n w = alloca_id)
            | _ => F) insts
End

Definition blocks_from_labels_def:
  blocks_from_labels bbs lbls =
    MAP (\lbl. THE (lookup_block lbl bbs)) lbls
End

Definition handle_inst_baseptr_def:
  handle_inst_baseptr ctx bpa inst =
    if inst_num_outputs inst <> 1 then (bpa, F) else
    case inst.inst_outputs of
      [out] =>
        let old = ptrs_of_var bpa out in
        let new =
          if inst.inst_opcode IN {ALLOCA; PALLOCA} then
            (case allocation_of_inst inst of
               NONE => []
             | SOME alloc => [ptr_from_alloca alloc])
          else if inst.inst_opcode = CALLOCA then
            (case inst.inst_operands of
               (Lit sizew :: Lit idw :: Label callee :: _) =>
                 (case lookup_function callee ctx.ctx_functions of
                    NONE => []
                  | SOME fn =>
                      (case find_palloca_inst fn (w2n idw) of
                         NONE => []
                       | SOME inst' =>
                           if inst'.inst_opcode = PALLOCA then
                             (case allocation_of_inst inst' of
                                NONE => []
                              | SOME alloc => [ptr_from_alloca alloc])
                           else []))
             | _ => [])
          else if inst.inst_opcode = PHI then
            FOLDL
              (λacc (_,v). ordset_union acc (ptrs_of_var bpa v))
              [] (phi_operands inst.inst_operands)
          else if inst.inst_opcode = ASSIGN then
            (case inst.inst_operands of
               [Var v] => ptrs_of_var bpa v
             | _ => [])
          else [] in
        if old = new then (bpa, F)
        else (bpa with var_to_mem := bpa.var_to_mem |+ (out, new), T)
    | _ => (bpa, F)
End

Definition base_ptr_iter_def:
  base_ptr_iter ctx cfg bbs bpa work fuel =
    case fuel of
      0 => bpa
    | SUC fuel' =>
        (case work of
           [] => bpa
         | bb::rest =>
             let (bpa', changed) =
               FOLDL
                 (λacc inst.
                    let (bpa1, ch) = acc in
                    let (bpa2, ch2) = handle_inst_baseptr ctx bpa1 inst in
                    (bpa2, ch \/ ch2))
                 (bpa, F) bb.bb_instructions in
             let succs = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
             let work' =
               if changed then rest ++ (blocks_from_labels bbs succs)
               else rest in
             base_ptr_iter ctx cfg bbs bpa' work' fuel')
End

Definition base_ptr_analyze_def:
  base_ptr_analyze ctx fn cfg =
    let work = MAP (\lbl. THE (lookup_block lbl fn.fn_blocks)) cfg.dfs_pre in
    let fuel = (LENGTH fn.fn_blocks) * (LENGTH fn.fn_blocks) + 1 in
    base_ptr_iter ctx cfg fn.fn_blocks <| var_to_mem := FEMPTY |> work fuel
End

val _ = export_theory();
