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
 * For any alloca used by add: convert add to GEP (pointer arithmetic).
 *
 * Uses DFG analysis (use tracking per variable).
 *
 * TOP-LEVEL:
 *   m2v_can_promote_alloca      — check if alloca uses are all mstore/mload/return
 *   m2v_has_escape_use          — check for add/phi/assign uses (escaping)
 *   m2v_promote_inst            — promote a single alloca use
 *   m2v_fix_add_inst            — convert add to GEP for escaped allocas
 *   m2v_transform_function      — function-level transform
 *
 * Upstream: vyper-ref cff4f6822 (palloca/calloca sunset)
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

(* Check if any use is an escaping opcode (add, phi, assign).
   If so, the alloca address escapes and we can't fully promote. *)
Definition m2v_has_escape_use_def:
  m2v_has_escape_use [] = F /\
  m2v_has_escape_use (inst :: rest) =
    if inst.inst_opcode = ADD \/
       inst.inst_opcode = PHI \/
       inst.inst_opcode = ASSIGN
    then T
    else m2v_has_escape_use rest
End

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

(* ===== Fix Adds (Escaped Allocas) ===== *)

(*
 * Collect all variable names reachable from an alloca output through
 * phi/assign/add chains. These are addresses that "are" the alloca pointer.
 * ADD is included because Python _fix_adds recursively follows through
 * converted ADD→GEP instructions, making their outputs aliases too.
 *
 * Termination: lex ordering on (CARD(FDOM dfg.dfg_defs DIFF set visited),
 * LENGTH worklist). Processing a defined var decreases the first component;
 * skipping (visited or undefined) decreases the second.
 *)
Definition m2v_collect_aliases_def:
  m2v_collect_aliases dfg [] visited = visited /\
  m2v_collect_aliases dfg (v :: rest) visited =
    if MEM v visited then m2v_collect_aliases dfg rest visited
    else
      case FLOOKUP dfg.dfg_defs v of
        NONE => m2v_collect_aliases dfg rest (v :: visited)
      | SOME _ =>
          let visited' = v :: visited in
          let uses = dfg_get_uses dfg v in
          let new_vars = FLAT (MAP (\(i : instruction).
            if i.inst_opcode = PHI \/ i.inst_opcode = ASSIGN \/
               i.inst_opcode = ADD then
              i.inst_outputs
            else []) uses) in
          m2v_collect_aliases dfg (new_vars ++ rest) visited'
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\(dfg,wl,vis). (CARD (FDOM dfg.dfg_defs DIFF set vis), LENGTH wl))`
  >> cheat
End

(*
 * Fix a single instruction: if it's an ADD that uses any alias of the
 * alloca, convert to GEP [alloca_addr; offset].
 *)
Definition m2v_fix_add_inst_def:
  m2v_fix_add_inst aliases inst =
    if inst.inst_opcode = ADD then
      case inst.inst_operands of
        [op1; op2] =>
          (case (op1, op2) of
             (Var v1, _) =>
               if MEM v1 aliases then
                 inst with <| inst_opcode := GEP;
                              inst_operands := [op1; op2] |>
               else (case op2 of
                       Var v2 =>
                         if MEM v2 aliases then
                           inst with <| inst_opcode := GEP;
                                        inst_operands := [op2; op1] |>
                         else inst
                     | _ => inst)
           | (_, Var v2) =>
               if MEM v2 aliases then
                 inst with <| inst_opcode := GEP;
                              inst_operands := [op2; op1] |>
               else inst
           | _ => inst)
      | _ => inst
    else inst
End

(* ===== Function-Level Transform ===== *)

(*
 * Transform function: collect promotion info, then rewrite instructions.
 *
 * Two-pass approach:
 *   1. Scan ALLOCA instructions, determine promotions vs escapes
 *   2. Rewrite all instructions according to promotion decisions
 *
 * Post-sunset: only ALLOCA, no PALLOCA/CALLOCA.
 *)
Definition m2v_transform_function_def:
  m2v_transform_function fn =
    let dfg = dfg_build_function fn in
    (* Collect alloca instructions *)
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    (* Build promotion map + escaped alloca outputs in one pass *)
    let scan_result = FOLDL (\(ctr, promos, escaped) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_has_escape_use uses then
            (ctr, promos, alloca_out :: escaped)
          else if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos, escaped)
          else
            (ctr, promos, alloca_out :: escaped)
      | _ => (ctr, promos, escaped))
      (0, [], []) alloca_insts in
    let promo_list = FST (SND scan_result) in
    let escaped_vars = SND (SND scan_result) in
    (* Compute aliases: for each escaped var, collect transitive phi/assign chain *)
    let all_aliases = FLAT (MAP
      (\ev. m2v_collect_aliases dfg [ev] []) escaped_vars) in
    (* Rewrite instructions *)
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE =>
          (* Fix adds for escaped allocas — uses transitive aliases *)
          [m2v_fix_add_inst all_aliases i] in
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        FLAT (MAP rewrite_inst bb.bb_instructions))
      fn.fn_blocks
End
