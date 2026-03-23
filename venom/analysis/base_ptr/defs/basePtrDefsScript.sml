(*
 * Base Pointer Analysis — Definitions
 *
 * Ported from vyper/venom/analysis/base_ptr_analysis.py.
 * Forward flow analysis: traces memory/storage pointers back to
 * their base allocation (alloca).
 *
 * TOP-LEVEL:
 *   ptr, offset_by,
 *   bp_get_ptrs, bp_handle_inst, bp_process_block,
 *   bp_one_pass, bp_analyze,
 *   bp_ptr_from_op, bp_segment_from_ops,
 *   bp_get_write_location, bp_get_read_location
 *
 * Helper:
 *   phi_operand_vars
 *
 * Divergences from Python:
 *   - allocation uses inst_id (num) instead of instruction object
 *   - var_to_mem is (string, ptr set) fmap (string keys, not IRVariable)
 *   - get_write_location / get_read_location take bp_result as explicit arg
 *)

Theory basePtrDefs
Ancestors
  memLocDefs cfgDefs dfIterateDefs venomEffects

(* ===== Pointer Type ===== *)

(* A pointer: base allocation + optional offset from base.
 * offset = NONE means offset is unknown/ambiguous. *)
Datatype:
  ptr = Ptr allocation (num option)
End

(* ===== Pointer Operations ===== *)

(* Offset a pointer by a given amount.
 * If either offset is unknown, result offset is unknown. *)
Definition offset_by_def:
  offset_by (Ptr alloc (SOME base)) (SOME n) =
    Ptr alloc (SOME (base + n)) ∧
  offset_by (Ptr alloc _) _ = Ptr alloc NONE
End

(* Create a pointer from an alloca instruction *)
Definition ptr_from_alloca_def:
  ptr_from_alloca inst = Ptr (Allocation (inst.inst_id)) (SOME 0)
End

(* ===== Analysis State ===== *)

(* Map from variable name to set of possible base pointers *)
Type bp_result = ``:(string, ptr set) fmap``

(* Lookup possible pointers for a variable. Empty set if not tracked. *)
Definition bp_get_ptrs_def:
  bp_get_ptrs (result : bp_result) v =
    case FLOOKUP result v of
      SOME ptrs => ptrs
    | NONE => {}
End

(* ===== Transfer Function ===== *)

(* Process a single instruction, updating the pointer map.
 * Returns (changed, new_result).
 * Matches Python _handle_inst. *)
Definition bp_handle_inst_def:
  bp_handle_inst (result : bp_result) inst =
    case inst_output inst of
      NONE => (F, result)
    | SOME out =>
        let original = bp_get_ptrs result out in
        let new_result =
          case inst.inst_opcode of
            (* alloca: fresh allocation at offset 0 *)
            ALLOCA => result |+ (out, {ptr_from_alloca inst})
            (* gep/add: base + offset. operands = [base_var, offset_operand]
             * add propagates pointers when one operand is a tracked pointer
             * and the other is a literal offset. Matches Python (c58034a22). *)
          | GEP =>
              (case inst.inst_operands of
                 [Var base_var; offset_op] =>
                   let base_ptrs = bp_get_ptrs result base_var in
                   let off = case offset_op of Lit n => SOME (w2n n)
                                             | _ => NONE in
                   result |+ (out, IMAGE (λp. offset_by p off) base_ptrs)
               | _ => result)
            (* add/sub: pointer arithmetic. Matches Python (c58034a22).
             * HOL semantic order: [lhs; rhs].
             * Python stack order: rhs, lhs = inst.operands.
             * Exact offset when one side is pointer + other is literal.
             * Unknown offset when both are vars but one is pointer.
             * SUB: only lhs can be pointer (ptr - offset). *)
          | ADD =>
              (case inst.inst_operands of
                 [Var lhs; Lit rhs] =>
                   let ptrs = bp_get_ptrs result lhs in
                   if ptrs ≠ {} then
                     result |+ (out, IMAGE (λp. offset_by p (SOME (w2n rhs))) ptrs)
                   else result
               | [Lit lhs; Var rhs] =>
                   let ptrs = bp_get_ptrs result rhs in
                   if ptrs ≠ {} then
                     result |+ (out, IMAGE (λp. offset_by p (SOME (w2n lhs))) ptrs)
                   else result
               | [Var lhs; Var rhs] =>
                   let p_lhs = bp_get_ptrs result lhs in
                   let p_rhs = bp_get_ptrs result rhs in
                   if p_lhs ≠ {} ∧ p_rhs = {} then
                     result |+ (out, IMAGE (λp. offset_by p NONE) p_lhs)
                   else if p_lhs = {} ∧ p_rhs ≠ {} then
                     result |+ (out, IMAGE (λp. offset_by p NONE) p_rhs)
                   else result
               | _ => result)
          | SUB =>
              (case inst.inst_operands of
                 [Var lhs; Lit _] =>
                   let ptrs = bp_get_ptrs result lhs in
                   if ptrs ≠ {} then
                     (* sub ptr literal: same alloca, unknown offset *)
                     result |+ (out, IMAGE (λp. offset_by p NONE) ptrs)
                   else result
               | [Var lhs; Var _] =>
                   let ptrs = bp_get_ptrs result lhs in
                   if ptrs ≠ {} then
                     result |+ (out, IMAGE (λp. offset_by p NONE) ptrs)
                   else result
               | _ => result)
            (* phi: union of all operand pointer sets *)
          | PHI =>
              let vars = MAP SND (phi_pairs inst.inst_operands) in
              let all_ptrs = BIGUNION (set (MAP (bp_get_ptrs result) vars)) in
              result |+ (out, all_ptrs)
            (* assign: propagate pointers from source variable *)
          | ASSIGN =>
              (case inst.inst_operands of
                 [Var src] => result |+ (out, bp_get_ptrs result src)
               | _ => result)
            (* all other opcodes: don't update pointer info *)
          | _ => result
        in
        let new_ptrs = bp_get_ptrs new_result out in
        (new_ptrs ≠ original, new_result)
End

(* ===== Block-Level Processing ===== *)

(* Process all instructions in a block, accumulating the result.
 * Returns (changed, result). *)
Definition bp_process_block_def:
  bp_process_block result [] = (F, result) ∧
  bp_process_block result (inst::insts) =
    let (c1, r1) = bp_handle_inst result inst in
    let (c2, r2) = bp_process_block r1 insts in
    (c1 ∨ c2, r2)
End

(* ===== Fixpoint Iteration ===== *)

(* One pass over all blocks in DFS pre-order.
 * Returns (changed, result). *)
Definition bp_one_pass_aux_def:
  bp_one_pass_aux fn result [] = (F, result) ∧
  bp_one_pass_aux fn result (lbl::lbls) =
    case FIND (λbb. bb.bb_label = lbl) fn.fn_blocks of
      NONE => bp_one_pass_aux fn result lbls
    | SOME bb =>
        let (c1, r1) = bp_process_block result bb.bb_instructions in
        let (c2, r2) = bp_one_pass_aux fn r1 lbls in
        (c1 ∨ c2, r2)
End

Definition bp_one_pass_def:
  bp_one_pass fn order result =
    bp_one_pass_aux fn result order
End

(* Top-level analysis: iterate one-pass until fixpoint.
 * Uses df_iterate (WHILE-based). *)
Definition bp_analyze_def:
  bp_analyze cfg fn =
    let order = cfg.cfg_dfs_pre in
    let init : bp_result = FEMPTY in
    df_iterate (λr. SND (bp_one_pass fn order r)) init
End

(* ===== Memory Location Queries ===== *)

(* Return the unique pointer for a variable operand, if exactly one exists.
 * Matches Python ptr_from_op. *)
Definition bp_ptr_from_op_def:
  bp_ptr_from_op (result : bp_result) op =
    case op of
      Var v =>
        let ptrs = bp_get_ptrs result v in
        if CARD ptrs = 1 then SOME (CHOICE ptrs)
        else NONE
    | _ => NONE
End

(* Build a mem_loc from InstAccessOps using pointer info.
 * Matches Python segment_from_ops. *)
Definition bp_segment_from_ops_def:
  bp_segment_from_ops result (ops : inst_access_ops) =
    let size = case ops.iao_size of
                 SOME (Lit n) => SOME (w2n n)
               | _ => NONE
    in
    let offset_op = ops.iao_ofst in
    case offset_op of
      Lit n => <| ml_offset := SOME (w2n n); ml_size := size;
                  ml_alloca := NONE; ml_volatile := F |>
    | Var _ =>
        (case bp_ptr_from_op result offset_op of
           NONE => <| ml_offset := NONE; ml_size := size;
                      ml_alloca := NONE; ml_volatile := F |>
         | SOME (Ptr alloc off) =>
             <| ml_offset := off; ml_size := size;
                ml_alloca := SOME alloc; ml_volatile := F |>)
    | Label _ => ml_undefined
End

(* ===== Write Location ===== *)

(* Get the memory location written by an instruction in a given address space.
 * Matches Python get_write_location. *)
Definition bp_get_write_location_def:
  bp_get_write_location result inst addr_sp =
    case addr_sp of
      AddrSp_Memory =>
        (* Special cases first *)
        if inst.inst_opcode = DLOAD then
          <| ml_offset := SOME 0; ml_size := SOME 32;
             ml_alloca := NONE; ml_volatile := F |>
        else if inst.inst_opcode = INVOKE then ml_undefined
        else if Eff_MEMORY ∉ write_effects inst.inst_opcode then ml_empty
        else
          (case mem_write_ops inst of
             NONE => ml_undefined
           | SOME ops => bp_segment_from_ops result ops)
    | AddrSp_Storage =>
        (* EVM: SSTORE key val — key is 1st operand *)
        if inst.inst_opcode = SSTORE then
          let ws = Lit (n2w (addr_space_word_scale AddrSp_Storage)) in
          (case inst.inst_operands of
             [dst; _] =>
               bp_segment_from_ops result
                 <| iao_ofst := dst; iao_size := SOME ws;
                    iao_max_size := SOME ws |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else ml_empty
    | AddrSp_Transient =>
        (* EVM: TSTORE key val — key is 1st operand *)
        if inst.inst_opcode = TSTORE then
          let ws = Lit (n2w (addr_space_word_scale AddrSp_Transient)) in
          (case inst.inst_operands of
             [dst; _] =>
               bp_segment_from_ops result
                 <| iao_ofst := dst; iao_size := SOME ws;
                    iao_max_size := SOME ws |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else ml_empty
    | _ => ml_empty  (* read-only address spaces have no writes *)
End

(* ===== Read Location ===== *)

(* Get the memory location read by an instruction in a given address space.
 * Matches Python get_read_location. *)
Definition bp_get_read_location_def:
  bp_get_read_location result inst addr_sp =
    case addr_sp of
      AddrSp_Memory =>
        if inst.inst_opcode = DLOAD then
          <| ml_offset := SOME 0; ml_size := SOME 32;
             ml_alloca := NONE; ml_volatile := F |>
        else if inst.inst_opcode ∈ {ILOAD; INVOKE; RET} then ml_undefined
        else if Eff_MEMORY ∉ read_effects inst.inst_opcode then ml_empty
        else
          (case mem_read_ops inst of
             NONE => ml_undefined
           | SOME ops => bp_segment_from_ops result ops)
    | AddrSp_Storage =>
        (* Storage is word-addressed: word_scale = 1 *)
        if inst.inst_opcode = SLOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 1w);
                    iao_max_size := SOME (Lit 1w) |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else if inst.inst_opcode ∈ {RETURN; STOP; SINK; RET} then ml_undefined
        else ml_empty
    | AddrSp_Transient =>
        (* Transient is word-addressed: word_scale = 1 *)
        if inst.inst_opcode = TLOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 1w);
                    iao_max_size := SOME (Lit 1w) |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else if inst.inst_opcode ∈ {RETURN; STOP; SINK; RET} then ml_undefined
        else ml_empty
    (* Read-only/copyable address spaces.
     * Matches Python _get_copyable_read_location.
     * EVM order bulk copy ops: [dst, src_ofst, size].
     * Single-word load ops: [ofst] → word_scale=32 bytes. *)
    | AddrSp_Calldata =>
        if inst.inst_opcode = CALLDATACOPY then
          (* EVM: CALLDATACOPY dst src sz — reads from src in calldata *)
          (case inst.inst_operands of
             [_; src_ofst; sz] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else if inst.inst_opcode = CALLDATALOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
           | _ => ml_empty)
        else ml_empty
    | AddrSp_Data =>
        if inst.inst_opcode = DLOADBYTES then
          (* EVM: DLOADBYTES dst src sz — reads from src in data *)
          (case inst.inst_operands of
             [_; src_ofst; sz] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else if inst.inst_opcode = DLOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
           | _ => ml_empty)
        else ml_empty
    | AddrSp_Code =>
        if inst.inst_opcode = CODECOPY then
          (* EVM: CODECOPY dst src sz — reads from src in code *)
          (case inst.inst_operands of
             [_; src_ofst; sz] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else ml_empty
    | AddrSp_Returndata =>
        if inst.inst_opcode = RETURNDATACOPY then
          (* EVM: RETURNDATACOPY dst src sz — reads from src in returndata *)
          (case inst.inst_operands of
             [_; src_ofst; sz] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else ml_empty
    | _ => ml_empty  (* Immutables handled by Memory case *)
End

