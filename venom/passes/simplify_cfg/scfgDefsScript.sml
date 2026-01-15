(*
 * Simplify-CFG Definitions
 *
 * This theory defines CFG utilities, label/PHI helpers, and equivalence
 * relations used in simplify-cfg correctness proofs.
 *)

Theory scfgDefs
Ancestors
  list relation
  venomState venomInst venomSem stateEquiv

(* ===== CFG Helpers ===== *)

Definition entry_label_def:
  entry_label fn = (HD fn.fn_blocks).bb_label
End

Definition block_last_inst_def:
  block_last_inst bb =
    if NULL bb.bb_instructions then NONE else SOME (LAST bb.bb_instructions)
End

Definition block_successors_def:
  block_successors bb =
    case block_last_inst bb of
      NONE => []
    | SOME inst => get_successors inst
End

Definition cfg_edge_def:
  cfg_edge fn src dst <=>
    ?bb. MEM bb fn.fn_blocks /\
         bb.bb_label = src /\
         MEM dst (block_successors bb)
End

Definition reachable_label_def:
  reachable_label fn entry lbl <=>
    RTC (cfg_edge fn) entry lbl
End

Definition pred_labels_def:
  pred_labels fn lbl =
    MAP (\bb. bb.bb_label)
      (FILTER (\bb. MEM lbl (block_successors bb)) fn.fn_blocks)
End

(* ===== CFG Well-Formedness ===== *)

Definition block_terminator_last_def:
  block_terminator_last bb <=>
    !idx inst.
      get_instruction bb idx = SOME inst /\
      is_terminator inst.inst_opcode ==>
      idx = LENGTH bb.bb_instructions - 1
End

Definition cfg_wf_def:
  cfg_wf fn <=>
    fn.fn_blocks <> [] /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
    !bb. MEM bb fn.fn_blocks ==>
      bb.bb_instructions <> [] /\ block_terminator_last bb
End

(* ===== Block Predicates ===== *)

Definition block_has_phi_def:
  block_has_phi bb <=>
    ?inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI
End

Definition block_has_no_phi_def:
  block_has_no_phi bb <=> ~block_has_phi bb
End

Definition block_last_jmp_to_def:
  block_last_jmp_to lbl bb <=>
    ?inst. block_last_inst bb = SOME inst /\
           inst.inst_opcode = JMP /\
           inst.inst_operands = [Label lbl]
End

Definition jump_only_target_def:
  jump_only_target bb =
    case bb.bb_instructions of
      [inst] =>
        if inst.inst_opcode = JMP then
          case inst.inst_operands of
            [Label lbl] => SOME lbl
          | _ => NONE
        else NONE
    | _ => NONE
End

(* ===== List Helpers for Blocks ===== *)

Definition update_last_inst_def:
  update_last_inst f [] = [] /\
  update_last_inst f [x] = [f x] /\
  update_last_inst f (x::xs) = x :: update_last_inst f xs
End

Definition remove_block_def:
  remove_block lbl [] = [] /\
  remove_block lbl (bb::bbs) =
    if bb.bb_label = lbl then remove_block lbl bbs
    else bb :: remove_block lbl bbs
End

Definition replace_block_def:
  replace_block bb' [] = [] /\
  replace_block bb' (bb::bbs) =
    if bb.bb_label = bb'.bb_label then bb' :: bbs
    else bb :: replace_block bb' bbs
End

(* ===== Label Replacement ===== *)

Definition replace_label_operand_def:
  replace_label_operand old new (Label l) =
    (if l = old then Label new else Label l) /\
  replace_label_operand old new op = op
End

Definition replace_label_inst_def:
  replace_label_inst old new inst =
    inst with inst_operands := MAP (replace_label_operand old new) inst.inst_operands
End

Definition replace_label_block_def:
  replace_label_block old new bb =
    bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions
End

Definition replace_label_fn_def:
  replace_label_fn old new fn =
    fn with fn_blocks := MAP (replace_label_block old new) fn.fn_blocks
End

Definition replace_label_in_phi_def:
  replace_label_in_phi old new inst =
    if inst.inst_opcode = PHI then
      inst with inst_operands := MAP (replace_label_operand old new) inst.inst_operands
    else inst
End

Definition replace_phi_in_block_def:
  replace_phi_in_block old new bb =
    bb with bb_instructions := MAP (replace_label_in_phi old new) bb.bb_instructions
End

(* ===== PHI Cleanup ===== *)

(* ===== PHI Well-Formedness ===== *)

Definition phi_vals_not_label_def:
  phi_vals_not_label [] = T /\
  phi_vals_not_label [_] = T /\
  phi_vals_not_label (Label lbl :: op :: rest) =
    (case op of
       Label _ => F
     | _ => phi_vals_not_label rest) /\
  phi_vals_not_label (_ :: _ :: rest) = phi_vals_not_label rest
End

Definition phi_ops_all_preds_def:
  phi_ops_all_preds preds ops <=>
    !lbl. MEM (Label lbl) ops ==> MEM lbl preds
End

Definition phi_ops_complete_def:
  phi_ops_complete preds ops <=>
    !lbl. MEM lbl preds ==> ?val_op. resolve_phi lbl ops = SOME val_op
End

Definition phi_inst_wf_def:
  phi_inst_wf preds inst <=>
    inst.inst_opcode <> PHI \/
    (?out.
       inst.inst_outputs = [out] /\
       phi_ops_all_preds preds inst.inst_operands /\
       phi_ops_complete preds inst.inst_operands /\
       phi_vals_not_label inst.inst_operands)
End

Definition phi_block_wf_def:
  phi_block_wf preds bb <=>
    !inst. MEM inst bb.bb_instructions ==> phi_inst_wf preds inst
End

Definition phi_fn_wf_def:
  phi_fn_wf fn <=>
    fn.fn_blocks <> [] /\
    (!bb. MEM bb fn.fn_blocks ==> phi_block_wf (pred_labels fn bb.bb_label) bb) /\
    block_has_no_phi (HD fn.fn_blocks)
End

Definition phi_remove_non_preds_def:
  phi_remove_non_preds preds [] = [] /\
  phi_remove_non_preds preds [_] = [] /\
  phi_remove_non_preds preds (Label lbl :: op :: rest) =
    (if MEM lbl preds then Label lbl :: op :: phi_remove_non_preds preds rest
     else phi_remove_non_preds preds rest) /\
  phi_remove_non_preds preds (_ :: _ :: rest) = phi_remove_non_preds preds rest
End

Definition simplify_phi_inst_def:
  simplify_phi_inst preds inst =
    if inst.inst_opcode <> PHI then inst
    else
      let ops = phi_remove_non_preds preds inst.inst_operands in
      if NULL ops then inst with <| inst_opcode := NOP; inst_operands := []; inst_outputs := [] |>
      else if LENGTH ops = 2 then inst with <| inst_opcode := ASSIGN; inst_operands := [EL 1 ops] |>
      else inst with inst_operands := ops
End

Definition simplify_phi_block_def:
  simplify_phi_block preds bb =
    bb with bb_instructions := MAP (simplify_phi_inst preds) bb.bb_instructions
End

(* ===== Instruction-List Execution Helpers ===== *)

Definition exec_inst_list_def:
  exec_inst_list [] s = OK s /\
  exec_inst_list (inst::insts) s =
    case step_inst inst s of
      OK s' => exec_inst_list insts (next_inst s')
    | Halt s' => Halt s'
    | Revert s' => Revert s'
    | Error e => Error e
End

Definition run_inst_list_def:
  run_inst_list [] s = Error "block not terminated" /\
  run_inst_list (inst::insts) s =
    case step_inst inst s of
      OK s' =>
        if is_terminator inst.inst_opcode then OK s'
        else run_inst_list insts (next_inst s')
    | Halt s' => Halt s'
    | Revert s' => Revert s'
    | Error e => Error e
End

(* ===== Equivalence Ignoring CFG Labels ===== *)

Definition state_equiv_cfg_def:
  state_equiv_cfg s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx
End

Definition result_equiv_cfg_def:
  result_equiv_cfg (OK s1) (OK s2) = state_equiv_cfg s1 s2 /\
  result_equiv_cfg (Halt s1) (Halt s2) = state_equiv_cfg s1 s2 /\
  result_equiv_cfg (Revert s1) (Revert s2) = state_equiv_cfg s1 s2 /\
  result_equiv_cfg (Error e1) (Error e2) = T /\
  result_equiv_cfg _ _ = F
End

Definition terminates_def:
  terminates (OK s) = T /\
  terminates (Halt s) = T /\
  terminates (Revert s) = T /\
  terminates (Error e) = F
End

Definition run_function_equiv_cfg_def:
  run_function_equiv_cfg fn fn' s <=>
    (!fuel.
       terminates (run_function fuel fn s) ==>
       ?fuel'.
         terminates (run_function fuel' fn' s) /\
         result_equiv_cfg (run_function fuel fn s)
                          (run_function fuel' fn' s)) /\
    (!fuel'.
       terminates (run_function fuel' fn' s) ==>
       ?fuel.
         terminates (run_function fuel fn s) /\
         result_equiv_cfg (run_function fuel fn s)
                          (run_function fuel' fn' s))
End

val _ = export_theory();
