(*
 * Branch Optimization Pass
 *
 * Port of venom/passes/branch_optimization.py.
 *)

Theory branchOpt
Ancestors
  list
  irOps dfgAnalysis livenessAnalysis cfgAnalysis
  instUpdater compilerState

Definition prefer_iszero_def:
  prefer_iszero inst <=>
    inst.inst_opcode = EQ \/
    (inst_is_comparator inst /\ EXISTS (λop. case op of Lit _ => T | _ => F) inst.inst_operands)
End

Definition branch_optimize_block_def:
  branch_optimize_block fn cfg live dfg updater bb =
    let insts = bb.bb_instructions in
    if insts = [] then updater else
    let term = LAST insts in
    if term.inst_opcode <> JNZ then updater else
    let succ_lbls = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
    case succ_lbls of
      [lbl1; lbl2] =>
        (case (lookup_block lbl1 fn.fn_blocks, lookup_block lbl2 fn.fn_blocks) of
           (SOME b1, SOME b2) =>
             let live1 =
               case b1.bb_instructions of
                 [] => []
               | i1::_ => liveness_live_vars_at live i1.inst_id in
             let live2 =
               case b2.bb_instructions of
                 [] => []
               | i2::_ => liveness_live_vars_at live i2.inst_id in
             let cost_a = LENGTH live1 in
             let cost_b = LENGTH live2 in
             case term.inst_operands of
               (cond::Label l1::Label l2::rest) =>
                 (case cond of
                    Var v =>
                      (case dfg_get_producing dfg v of
                         NONE => updater
                       | SOME pid =>
                           (case lookup_inst_in_function pid updater.iu_fn of
                              NONE => updater
                            | SOME prev_inst =>
                                if cost_a >= cost_b /\ prev_inst.inst_opcode = ISZERO then
                                  let new_operands = [HD prev_inst.inst_operands; Label l2; Label l1] in
                                  inst_updater_update updater term term.inst_opcode new_operands NONE
                                else if cost_a > cost_b \/ (cost_a >= cost_b /\ prefer_iszero prev_inst) then
                                  let (updater', out_opt) =
                                    inst_updater_add_before updater term ISZERO [cond] in
                                  (case out_opt of
                                     NONE => updater
                                   | SOME v' =>
                                       let new_operands = [Var v'; Label l2; Label l1] in
                                       inst_updater_update updater' term term.inst_opcode new_operands NONE)
                                else updater))
                  | _ => updater)
             | _ => updater
         | _ => updater)
    | _ => updater
End

Definition branch_optimize_function_def:
  branch_optimize_function fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let live = liveness_analyze fn cfg in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let updater' =
      FOLDL
        (λacc bb. branch_optimize_block acc.iu_fn cfg live acc.iu_dfg acc bb)
        updater fn.fn_blocks in
    updater'.iu_fn
End

Definition branch_optimize_context_def:
  branch_optimize_context ctx =
    ctx with ctx_functions := MAP branch_optimize_function ctx.ctx_functions
End

val _ = export_theory();
