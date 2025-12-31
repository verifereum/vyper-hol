(*
 * Simplify-CFG Transformations
 *
 * This theory defines simplify-cfg transformations and the step relation
 * used in correctness proofs.
 *)

Theory scfgTransform
Ancestors
  scfgDefs list relation

(* ===== Unreachable Block Removal ===== *)

Definition remove_unreachable_blocks_def:
  remove_unreachable_blocks fn =
    if fn.fn_blocks = [] then fn
    else
      let entry = (HD fn.fn_blocks).bb_label in
      let keep = FILTER (\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks in
      let fn' = fn with fn_blocks := keep in
      let fix = MAP (\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) keep in
      fn with fn_blocks := fix
End

(* ===== Block Merge ===== *)

Definition merge_blocks_cond_def:
  merge_blocks_cond fn a_lbl b_lbl <=>
    ?a b.
      lookup_block a_lbl fn.fn_blocks = SOME a /\
      lookup_block b_lbl fn.fn_blocks = SOME b /\
      pred_labels fn b_lbl = [a_lbl] /\
      block_has_no_phi b /\
      block_last_jmp_to b_lbl a
End

Definition merge_blocks_def:
  merge_blocks fn a_lbl b_lbl =
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) =>
        let a' = a with bb_instructions := BUTLAST a.bb_instructions ++ b.bb_instructions in
        let blocks1 = remove_block b_lbl fn.fn_blocks in
        let blocks2 = replace_block a' blocks1 in
        let fn1 = fn with fn_blocks := blocks2 in
        replace_label_fn b_lbl a_lbl fn1
    | _ => fn
End

(* ===== Jump Threading (Jump-Only Block) ===== *)

Definition merge_jump_cond_def:
  merge_jump_cond fn a_lbl b_lbl <=>
    ?a b c_lbl.
      lookup_block a_lbl fn.fn_blocks = SOME a /\
      lookup_block b_lbl fn.fn_blocks = SOME b /\
      MEM b_lbl (block_successors a) /\
      ~MEM c_lbl (block_successors a) /\
      pred_labels fn b_lbl = [a_lbl] /\
      jump_only_target b = SOME c_lbl
End

Definition merge_jump_def:
  merge_jump fn a_lbl b_lbl =
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) =>
        (case jump_only_target b of
           NONE => fn
         | SOME c_lbl =>
             let a' =
               a with bb_instructions :=
                 update_last_inst (replace_label_inst b_lbl c_lbl) a.bb_instructions in
             let blocks1 = replace_block a' fn.fn_blocks in
             let blocks2 = remove_block b_lbl blocks1 in
             let fn1 = fn with fn_blocks := blocks2 in
             let succs = block_successors a' in
             let blocks3 =
               MAP (\bb. if MEM bb.bb_label succs
                         then replace_phi_in_block b_lbl a_lbl bb
                         else bb) fn1.fn_blocks in
             let fn2 = fn1 with fn_blocks := blocks3 in
             replace_label_fn b_lbl c_lbl fn2)
    | _ => fn
End

(* ===== Simplify-CFG Step Relation ===== *)

Definition simplify_cfg_step_def:
  simplify_cfg_step fn fn' <=>
    fn' = remove_unreachable_blocks fn \/
    (?a b. merge_blocks_cond fn a b /\ fn' = merge_blocks fn a b) \/
    (?a b. merge_jump_cond fn a b /\ fn' = merge_jump fn a b)
End

Definition simplify_cfg_def:
  simplify_cfg fn fn' <=>
    RTC simplify_cfg_step fn fn'
End

val _ = export_theory();
