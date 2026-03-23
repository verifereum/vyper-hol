(*
 * Mem2Var Pass — Definitions
 *
 * Ports vyper/venom/passes/mem2var.py to HOL4.
 *
 * Promotes memory operations to variable operations where safe:
 *   - alloca only used by mstore/mload/return → promote to variable
 *
 * For alloca promotion (size = 32):
 *   mstore [alloca_addr; val]  → assign [val] → [alloca_var]
 *   mload [alloca_addr]        → assign [alloca_var] → [orig_out]
 *   return with alloca_addr    → insert mstore before, keep return
 *
 * Uses DFG analysis (use tracking per variable).
 *
 * TOP-LEVEL:
 *   m2v_can_promote_alloca      — check if alloca uses are all mstore/mload/return
 *   m2v_promote_inst            — promote a single alloca use
 *   m2v_transform_function      — function-level transform
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
 *)

Theory mem2varDefs
Ancestors
  passSimulationDefs dfgDefs venomExecSemantics venomInst
Libs
  pred_setTheory finite_mapTheory

(* ===== Fresh Variable ===== *)

Definition m2v_fresh_var_def:
  m2v_fresh_var (varname : string) (count : num) =
    STRCAT "alloca_" (STRCAT varname (STRCAT "_" (toString count)))
End

(* ===== Use Analysis ===== *)

(* Check if all uses are mstore/mload/return (promotable).
   Requires at least one mstore (otherwise never written). *)
Definition m2v_can_promote_alloca_def:
  m2v_can_promote_alloca uses <=>
    EVERY (\inst. inst.inst_opcode = MSTORE \/
                  inst.inst_opcode = MLOAD \/
                  inst.inst_opcode = RETURN) uses /\
    EXISTS (\inst. inst.inst_opcode = MSTORE) uses
End



(* ===== Promotion Transform ===== *)

(*
 * Promote a single mstore/mload/return instruction that uses an alloca.
 *
 * Parameters:
 *   alloca_var  — the promoted variable name
 *   alloca_out  — the original alloca output (address variable)
 *   size        — alloca size (only promote if 32)
 *   inst        — instruction to transform
 *
 * In HOL4 semantic operand order:
 *   mstore [offset; value] → if offset = alloca_out: assign [value] → [alloca_var]
 *   mload [addr] → if addr = alloca_out: assign [Var alloca_var] → [orig_out]
 *   return [offset; size] → if offset = alloca_out: insert mstore before, keep return
 *)
Definition m2v_promote_inst_def:
  m2v_promote_inst alloca_var alloca_out (size : num) inst =
    if inst.inst_opcode = MSTORE /\ size = 32 then
      case inst.inst_operands of
        [ofs; val_op] =>
          if ofs = Var alloca_out then
            (* mstore to alloca → assign val to promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [val_op];
                          inst_outputs := [alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = MLOAD /\ size = 32 then
      case inst.inst_operands of
        [addr] =>
          if addr = Var alloca_out then
            (* mload from alloca → assign promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [Var alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = RETURN /\ size <= 32 then
      case inst.inst_operands of
        (* HOL4 RETURN: [offset; size]. Python operands[1] = offset = HOL4 op1.
           Check if offset (first operand) is the alloca address. *)
        [off_op; sz_op] =>
          if off_op = Var alloca_out then
            (* return from alloca: insert mstore to materialize value *)
            let store = <| inst_id := inst.inst_id;
                           inst_opcode := MSTORE;
                           inst_operands := [Var alloca_out; Var alloca_var];
                           inst_outputs := [] |> in
            [store; inst]
          else [inst]
      | _ => [inst]
    else [inst]
End

(* ===== Function-Level Transform ===== *)

(*
 * Transform function: collect promotion info, then rewrite instructions.
 *
 * Single-pass approach (post alloca_id removal — upstream 8780b3134):
 *   1. Scan ALLOCA instructions, determine which are promotable
 *   2. Rewrite all instructions according to promotion decisions
 *
 * An alloca is promotable iff ALL uses are mstore/mload/return
 * (checked by m2v_can_promote_alloca). Non-promotable allocas are
 * left unchanged — the old _fix_adds / escape_use path was removed
 * upstream because phi/assign guards on alloca are impossible after
 * alloca_id removal.
 *)
Definition m2v_transform_function_def:
  m2v_transform_function fn =
    let dfg = dfg_build_function fn in
    (* Collect alloca instructions *)
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    (* Build promotion map *)
    let scan_result = FOLDL (\(ctr, promos) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos)
          else
            (ctr, promos)
      | _ => (ctr, promos))
      (0, []) alloca_insts in
    let promo_list = SND scan_result in
    (* Rewrite instructions *)
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE => [i] in
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        FLAT (MAP rewrite_inst bb.bb_instructions))
      fn.fn_blocks
End
