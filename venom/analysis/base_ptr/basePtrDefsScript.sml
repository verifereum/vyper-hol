(*
 * Base Pointer Analysis — Definitions
 *
 * Ported from vyper/venom/analysis/base_ptr_analysis.py.
 * Forward flow analysis: traces memory/storage pointers back to
 * their base allocation (alloca/palloca).
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
 *   - calloca not yet handled (requires cross-function context)
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

(* ===== PHI Operand Variables ===== *)

(* Extract variable names from PHI operands.
 * PHI format: Label l1, Var v1, Label l2, Var v2, ...
 * Returns just the variable names. *)
Definition phi_operand_vars_def:
  phi_operand_vars [] = [] ∧
  phi_operand_vars [_] = [] ∧
  phi_operand_vars (Label _ :: Var v :: rest) = v :: phi_operand_vars rest ∧
  phi_operand_vars (_ :: _ :: rest) = phi_operand_vars rest
End

(* ===== Cross-Function Helpers ===== *)

(* Find a palloca instruction with a given alloca_id in a function.
 * Scans all blocks' instructions for a PALLOCA with matching inst_id.
 * Matches Python IRFunction.get_palloca_inst. *)
Definition find_palloca_inst_def:
  find_palloca_inst fn alloca_id =
    FIND (λinst. inst.inst_opcode = PALLOCA ∧ inst.inst_id = alloca_id)
         (FLAT (MAP (λbb. bb.bb_instructions) fn.fn_blocks))
End

(* ===== Transfer Function ===== *)

(* Process a single instruction, updating the pointer map.
 * ctx: program context (needed for calloca cross-function lookup)
 * Returns (changed, new_result).
 * Matches Python _handle_inst. *)
Definition bp_handle_inst_def:
  bp_handle_inst ctx (result : bp_result) inst =
    case inst_output inst of
      NONE => (F, result)
    | SOME out =>
        let original = bp_get_ptrs result out in
        let new_result =
          case inst.inst_opcode of
            (* alloca/palloca: fresh allocation at offset 0 *)
            ALLOCA => result |+ (out, {ptr_from_alloca inst})
          | PALLOCA => result |+ (out, {ptr_from_alloca inst})
            (* gep: base + offset. operands = [base_var, offset_operand] *)
          | GEP =>
              (case inst.inst_operands of
                 [Var base_var; offset_op] =>
                   let base_ptrs = bp_get_ptrs result base_var in
                   let off = case offset_op of Lit n => SOME (w2n n)
                                             | _ => NONE in
                   result |+ (out, IMAGE (λp. offset_by p off) base_ptrs)
               | _ => result)
            (* phi: union of all operand pointer sets *)
          | PHI =>
              let vars = phi_operand_vars inst.inst_operands in
              let all_ptrs = BIGUNION (set (MAP (bp_get_ptrs result) vars)) in
              result |+ (out, all_ptrs)
            (* assign: propagate pointers from source variable *)
          | ASSIGN =>
              (case inst.inst_operands of
                 [Var src] => result |+ (out, bp_get_ptrs result src)
               | _ => result)
            (* calloca: cross-function allocation.
             * operands = [size, Lit alloca_id, Label callee_label]
             * Look up callee's palloca instruction and use its allocation. *)
          | CALLOCA =>
              (case inst.inst_operands of
                 [_; Lit alloca_id; Label callee_label] =>
                   (case lookup_function callee_label ctx.ctx_functions of
                      SOME callee =>
                        (case find_palloca_inst callee (w2n alloca_id) of
                           SOME palloca =>
                             if palloca.inst_opcode = PALLOCA then
                               result |+ (out, {ptr_from_alloca palloca})
                             else result
                         | NONE => result)
                    | NONE => result)
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
  bp_process_block ctx result [] = (F, result) ∧
  bp_process_block ctx result (inst::insts) =
    let (c1, r1) = bp_handle_inst ctx result inst in
    let (c2, r2) = bp_process_block ctx r1 insts in
    (c1 ∨ c2, r2)
End

(* ===== Fixpoint Iteration ===== *)

(* One pass over all blocks in DFS pre-order.
 * Returns (changed, result). *)
Definition bp_one_pass_aux_def:
  bp_one_pass_aux ctx fn result [] = (F, result) ∧
  bp_one_pass_aux ctx fn result (lbl::lbls) =
    case FIND (λbb. bb.bb_label = lbl) fn.fn_blocks of
      NONE => bp_one_pass_aux ctx fn result lbls
    | SOME bb =>
        let (c1, r1) = bp_process_block ctx result bb.bb_instructions in
        let (c2, r2) = bp_one_pass_aux ctx fn r1 lbls in
        (c1 ∨ c2, r2)
End

Definition bp_one_pass_def:
  bp_one_pass ctx fn order result =
    bp_one_pass_aux ctx fn result order
End

(* Top-level analysis: iterate one-pass until fixpoint.
 * Uses df_iterate (WHILE-based). *)
Definition bp_analyze_def:
  bp_analyze ctx cfg fn =
    let order = cfg.cfg_dfs_pre in
    let init : bp_result = FEMPTY in
    df_iterate (λr. SND (bp_one_pass ctx fn order r)) init
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
        if inst.inst_opcode = SSTORE then
          (case inst.inst_operands of
             [_; dst] =>
               bp_segment_from_ops result
                 <| iao_ofst := dst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else ml_empty
    | AddrSp_Transient =>
        if inst.inst_opcode = TSTORE then
          (case inst.inst_operands of
             [_; dst] =>
               bp_segment_from_ops result
                 <| iao_ofst := dst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
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
        if inst.inst_opcode = SLOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else if inst.inst_opcode ∈ {RETURN; STOP; SINK; RET} then ml_undefined
        else ml_empty
    | AddrSp_Transient =>
        if inst.inst_opcode = TLOAD then
          (case inst.inst_operands of
             [ofst] =>
               bp_segment_from_ops result
                 <| iao_ofst := ofst; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>
           | _ => ml_undefined)
        else if inst.inst_opcode ∈ {CALL; DELEGATECALL; STATICCALL;
                                     INVOKE; CREATE; CREATE2} then ml_undefined
        else if inst.inst_opcode ∈ {RETURN; STOP; SINK; RET} then ml_undefined
        else ml_empty
    (* Read-only/copyable address spaces.
     * Matches Python _get_copyable_read_location.
     * Bulk copy ops: [size, src_ofst, dst].
     * Single-word load ops: [ofst] → word_scale=32 bytes. *)
    | AddrSp_Calldata =>
        if inst.inst_opcode = CALLDATACOPY then
          (case inst.inst_operands of
             [sz; src_ofst; _] =>
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
          (case inst.inst_operands of
             [sz; src_ofst; _] =>
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
          (case inst.inst_operands of
             [sz; src_ofst; _] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else ml_empty
    | AddrSp_Returndata =>
        if inst.inst_opcode = RETURNDATACOPY then
          (case inst.inst_operands of
             [sz; src_ofst; _] =>
               bp_segment_from_ops result
                 <| iao_ofst := src_ofst; iao_size := SOME sz;
                    iao_max_size := SOME sz |>
           | _ => ml_empty)
        else ml_empty
    | _ => ml_empty  (* Immutables handled by Memory case *)
End

