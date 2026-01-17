(*
 * Algebraic Optimization Pass
 *
 * Port of venom/passes/algebraic_optimization.py.
 *)

Theory algebraicOpt
Ancestors
  list pred_set
  irOps
  dfgAnalysis livenessAnalysis
  instUpdater compilerUtils compilerState

Definition is_lit_def:
  is_lit op <=> case op of Lit _ => T | _ => F
End

Definition lit_eq_def:
  lit_eq op val <=>
    case op of
      Lit w => w = (i2w val : bytes32)
    | _ => F
End

Definition lit_to_num_opt_def:
  lit_to_num_opt op =
    case op of
      Lit w => SOME (w2n w)
    | _ => NONE
End

Definition lit_to_int_signed_opt_def:
  lit_to_int_signed_opt op =
    case op of
      Lit w => SOME (w2i w)
    | _ => NONE
End

Definition truthy_opcodes_def:
  truthy_opcodes = [ISZERO; JNZ; ASSERT; ASSERT_UNREACHABLE]
End

Definition prefer_iszero_opcodes_def:
  prefer_iszero_opcodes = [ASSERT; ISZERO]
End

Definition insts_from_ids_def:
  insts_from_ids fn ids =
    FOLDL
      (λacc iid.
         case lookup_inst_in_function iid fn of
           NONE => acc
         | SOME inst => acc ++ [inst])
      [] ids
End

Definition all_inst_opcode_in_def:
  all_inst_opcode_in insts ops =
    EVERY (λinst. MEM inst.inst_opcode ops) insts
End

Definition first_use_inst_def:
  first_use_inst fn ids =
    case ids of
      [] => NONE
    | iid::_ => lookup_inst_in_function iid fn
End

Definition flip_for_peephole_def:
  flip_for_peephole updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if inst_flippable inst /\ is_lit op2 /\ ~is_lit op1 then
          let inst' = inst_flip inst in
          (inst_updater_update updater inst inst'.inst_opcode inst'.inst_operands NONE, inst')
        else (updater, inst)
    | _ => (updater, inst)
End

Definition algebraic_opt_handle_shift_def:
  algebraic_opt_handle_shift updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if lit_eq op2 0 then inst_updater_mk_assign updater inst op1 NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_exp_def:
  algebraic_opt_handle_exp updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if lit_eq op1 0 then inst_updater_mk_assign updater inst (Lit 1w) NONE
        else if lit_eq op2 1 then inst_updater_mk_assign updater inst (Lit 1w) NONE
        else if lit_eq op2 0 then inst_updater_update updater inst ISZERO [op1] NONE
        else if lit_eq op1 1 then inst_updater_mk_assign updater inst op2 NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_gep_def:
  algebraic_opt_handle_gep updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if lit_eq op2 0 then inst_updater_mk_assign updater inst op1 NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_add_sub_xor_def:
  algebraic_opt_handle_add_sub_xor updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if (inst.inst_opcode = XOR \/ inst.inst_opcode = SUB) /\ op1 = op2 then
          inst_updater_mk_assign updater inst (Lit 0w) NONE
        else if lit_eq op1 0 then inst_updater_mk_assign updater inst op2 NONE
        else if inst.inst_opcode = SUB /\ lit_eq op2 (-1) then
          inst_updater_update updater inst NOT [op1] NONE
        else if inst.inst_opcode = XOR /\ lit_eq op1 (-1) then
          inst_updater_update updater inst NOT [op2] NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_and_def:
  algebraic_opt_handle_and updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if lit_eq op1 (-1) then inst_updater_mk_assign updater inst op2 NONE
        else updater
    | _ => updater
End

Definition any_lit_zero_def:
  any_lit_zero ops =
    EXISTS (λop. lit_eq op 0) ops
End

Definition algebraic_opt_handle_mul_div_mod_def:
  algebraic_opt_handle_mul_div_mod updater inst =
    let ops = inst.inst_operands in
    if any_lit_zero ops then inst_updater_mk_assign updater inst (Lit 0w) NONE
    else
      case ops of
        op1::op2::_ =>
          if (inst.inst_opcode = Mod \/ inst.inst_opcode = SMOD) /\ lit_eq op1 1 then
            inst_updater_mk_assign updater inst (Lit 0w) NONE
          else if (inst.inst_opcode = MUL \/ inst.inst_opcode = Div \/ inst.inst_opcode = SDIV) /\
                  lit_eq op1 1 then
            inst_updater_mk_assign updater inst op2 NONE
          else
            (case lit_to_num_opt op1 of
               NONE => updater
             | SOME val =>
                 if is_power_of_two val then
                  if inst.inst_opcode = Mod then
                     inst_updater_update updater inst AND
                       [Lit (n2w (val - 1)); op2] NONE
                   else if inst.inst_opcode = Div then
                     inst_updater_update updater inst SHR
                       [op2; Lit (n2w (int_log2 val))] NONE
                   else if inst.inst_opcode = MUL then
                     inst_updater_update updater inst SHL
                       [op2; Lit (n2w (int_log2 val))] NONE
                   else updater
                 else updater)
      | _ => updater
End

Definition algebraic_opt_handle_or_def:
  algebraic_opt_handle_or updater inst is_truthy =
    case inst.inst_operands of
      op1::op2::_ =>
        if EXISTS (λop. lit_eq op size_limits_max_uint256) inst.inst_operands then
          inst_updater_mk_assign updater inst (Lit (i2w size_limits_max_uint256)) NONE
        else if is_truthy /\ is_lit op1 /\
                (case op1 of Lit w => w2n w <> 0 | _ => F) then
          inst_updater_mk_assign updater inst (Lit 1w) NONE
        else if lit_eq op1 0 then inst_updater_mk_assign updater inst op2 NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_eq_def:
  algebraic_opt_handle_eq updater inst prefer_iszero =
    case inst.inst_operands of
      op1::op2::_ =>
        if op1 = op2 then inst_updater_mk_assign updater inst (Lit 1w) NONE
        else if lit_eq op1 0 then inst_updater_update updater inst ISZERO [op2] NONE
        else if lit_eq op1 (-1) then
          let (upd1, vopt) = inst_updater_add_before updater inst NOT [op2] in
          (case vopt of
             NONE => upd1
           | SOME v => inst_updater_update upd1 inst ISZERO [Var v] NONE)
        else if prefer_iszero then
          let (upd1, vopt) = inst_updater_add_before updater inst XOR [op1; op2] in
          (case vopt of
             NONE => upd1
           | SOME v => inst_updater_update upd1 inst ISZERO [Var v] NONE)
        else updater
    | _ => updater
End

Definition algebraic_opt_comparator_def:
  algebraic_opt_comparator updater inst prefer_iszero =
    case inst.inst_operands of
      op1::op2::_ =>
        if op1 = op2 then inst_updater_mk_assign updater inst (Lit 0w) NONE
        else
          (case lit_to_int_signed_opt op1 of
             NONE => updater
           | SOME _ =>
               let is_gt = ((inst.inst_opcode = GT) \/ (inst.inst_opcode = SGT)) in
               let signed = ((inst.inst_opcode = SGT) \/ (inst.inst_opcode = SLT)) in
               let (lo, hi) = int_bounds signed 256 in
               let (almost_always, never, almost_never) =
                 if is_gt then (lo, hi, hi - 1) else (hi, lo, lo + 1) in
               if lit_eq op1 never then
                 inst_updater_mk_assign updater inst (Lit 0w) NONE
               else if lit_eq op1 almost_never then
                 inst_updater_update updater inst EQ [op2; Lit (i2w never)] NONE
               else if prefer_iszero /\ lit_eq op1 almost_always then
                 let (upd1, vopt) = inst_updater_add_before updater inst EQ [op1; op2] in
                 (case vopt of
                    NONE => upd1
                  | SOME v => inst_updater_update upd1 inst ISZERO [Var v] NONE)
               else if inst.inst_opcode = GT /\ lit_eq op1 0 then
                 let (upd1, vopt) = inst_updater_add_before updater inst ISZERO [op2] in
                 (case vopt of
                    NONE => upd1
                  | SOME v => inst_updater_update upd1 inst ISZERO [Var v] NONE)
               else
                 (case inst_output inst of
                    NONE => updater
                  | SOME out =>
                      let uses = dfg_get_uses updater.iu_dfg out in
                      if LENGTH uses <> 1 then updater else
                        (case first_use_inst updater.iu_fn uses of
                           NONE => updater
                         | SOME after =>
                             if ~(after.inst_opcode = ISZERO \/ after.inst_opcode = ASSERT) then updater
                             else
                               let ok =
                                 if after.inst_opcode = ISZERO then
                                   case inst_output after of
                                     NONE => F
                                   | SOME out2 =>
                                       let uses2 = dfg_get_uses updater.iu_dfg out2 in
                                       if LENGTH uses2 <> 1 then F
                                       else
                                         (case first_use_inst updater.iu_fn uses2 of
                                            SOME inst2 => inst2.inst_opcode <> ASSERT
                                          | NONE => F)
                                 else T in
                               if ~ok then updater
                               else
                                 let val =
                                   if signed then
                                     (case lit_to_int_signed_opt op1 of SOME v => v | NONE => 0)
                                   else
                                     (case lit_to_num_opt op1 of
                                        SOME n => int_of_num n | NONE => 0) in
                                 let val' = if is_gt then val + 1 else val - 1 in
                                 let new_op = flip_comparison_opcode inst.inst_opcode in
                                 let upd1 =
                                   inst_updater_update updater inst new_op
                                     [Lit (i2w val'); op2] NONE in
                                 if after.inst_opcode = ASSERT then
                                   let (upd2, vopt) =
                                     inst_updater_add_before upd1 after ISZERO [Var out] in
                                   (case vopt of
                                      NONE => upd2
                                    | SOME v =>
                                        case after.inst_operands of
                                          op0::_ =>
                                            inst_updater_update_operands upd2 after [(op0, Var v)]
                                        | _ => upd2)
                                 else
                                   inst_updater_update upd1 after ASSIGN after.inst_operands NONE)))
    | _ => updater
End

Definition algebraic_opt_handle_inst_peephole_def:
  algebraic_opt_handle_inst_peephole updater inst =
    if inst_num_outputs inst <> 1 then updater
    else if inst_is_volatile inst then updater
    else if inst.inst_opcode = ASSIGN then updater
    else if inst_is_pseudo inst then updater
    else
      let (updater1, inst1) = flip_for_peephole updater inst in
      if inst1.inst_opcode IN {SHL; SHR; SAR} then
        algebraic_opt_handle_shift updater1 inst1
      else if inst1.inst_opcode = venomInst$EXP then
        algebraic_opt_handle_exp updater1 inst1
      else if inst1.inst_opcode = GEP then
        algebraic_opt_handle_gep updater1 inst1
      else if inst1.inst_opcode IN {ADD; SUB; XOR} then
        algebraic_opt_handle_add_sub_xor updater1 inst1
      else if inst1.inst_opcode = AND then
        algebraic_opt_handle_and updater1 inst1
      else if inst1.inst_opcode IN {MUL; Div; SDIV; Mod; SMOD; AND} then
        (if inst1.inst_opcode = AND then
           (if any_lit_zero inst1.inst_operands then
              inst_updater_mk_assign updater1 inst1 (Lit 0w) NONE
            else updater1)
         else
           algebraic_opt_handle_mul_div_mod updater1 inst1)
      else
        let uses =
          case inst_output inst1 of
            NONE => []
          | SOME out => dfg_get_uses updater1.iu_dfg out in
        let use_insts = insts_from_ids updater1.iu_fn uses in
        let is_truthy = all_inst_opcode_in use_insts truthy_opcodes in
        let prefer_iszero = all_inst_opcode_in use_insts prefer_iszero_opcodes in
        if inst1.inst_opcode = OR then
          algebraic_opt_handle_or updater1 inst1 is_truthy
        else if inst1.inst_opcode = EQ then
          algebraic_opt_handle_eq updater1 inst1 prefer_iszero
        else if inst_is_comparator inst1 then
          algebraic_opt_comparator updater1 inst1 prefer_iszero
        else updater1
End

Definition algebraic_opt_flip_inst_def:
  algebraic_opt_flip_inst updater inst =
    case inst.inst_operands of
      op1::op2::_ =>
        if inst_flippable inst /\ is_lit op1 /\ ~is_lit op2 then
          let inst' = inst_flip inst in
          inst_updater_update updater inst inst'.inst_opcode inst'.inst_operands NONE
        else updater
    | _ => updater
End

Definition algebraic_opt_pass_block_def:
  algebraic_opt_pass_block updater bb =
    let ids = MAP (λinst. inst.inst_id) bb.bb_instructions in
    FOLDL
      (λacc iid.
         case lookup_inst_in_function iid acc.iu_fn of
           NONE => acc
         | SOME inst =>
             let acc1 = algebraic_opt_handle_inst_peephole acc inst in
             case lookup_inst_in_function iid acc1.iu_fn of
               NONE => acc1
             | SOME inst' => algebraic_opt_flip_inst acc1 inst')
      updater ids
End

Definition algebraic_opt_pass_def:
  algebraic_opt_pass updater =
    FOLDL (λacc bb. algebraic_opt_pass_block acc bb) updater updater.iu_fn.fn_blocks
End

Definition algebraic_opt_get_iszero_chain_aux_def:
  algebraic_opt_get_iszero_chain_aux fn dfg op 0 acc = REVERSE acc /\
  algebraic_opt_get_iszero_chain_aux fn dfg op (SUC fuel) acc =
    case op of
      Var v =>
        (case dfg_get_producing dfg v of
           NONE => REVERSE acc
         | SOME iid =>
             (case lookup_inst_in_function iid fn of
                NONE => REVERSE acc
              | SOME inst =>
                  if inst.inst_opcode = ISZERO then
                    case inst.inst_operands of
                      op1::_ => algebraic_opt_get_iszero_chain_aux fn dfg op1 fuel (inst::acc)
                    | _ => REVERSE acc
                  else REVERSE acc))
    | _ => REVERSE acc
End

Definition algebraic_opt_get_iszero_chain_def:
  algebraic_opt_get_iszero_chain fn dfg op =
    let fuel = LENGTH (fn_instructions_list fn) + 1 in
    algebraic_opt_get_iszero_chain_aux fn dfg op fuel []
End

Definition algebraic_opt_optimize_iszero_inst_def:
  algebraic_opt_optimize_iszero_inst updater inst =
    if inst.inst_opcode <> ISZERO then updater
    else
      case inst.inst_operands of
        [] => updater
      | op::_ =>
          let chain = algebraic_opt_get_iszero_chain updater.iu_fn updater.iu_dfg op in
          let count = LENGTH chain in
          if count = 0 then updater
          else
            case inst_output inst of
              NONE => updater
            | SOME out_var =>
                let uses = dfg_get_uses updater.iu_dfg out_var in
                FOLDL
                  (λacc iid.
                     case lookup_inst_in_function iid acc.iu_fn of
                       NONE => acc
                     | SOME use_inst =>
                         if use_inst.inst_opcode = ISZERO then acc
                         else
                           let mod2 = count MOD 2 in
                           let keep =
                             if MEM use_inst.inst_opcode truthy_opcodes
                             then 1 - mod2 else 1 + mod2 in
                           if keep >= count then acc
                           else
                             let dep_inst = EL keep chain in
                             let new_op =
                               case dep_inst.inst_operands of
                                 op0::_ => op0
                               | _ => Var out_var in
                             inst_updater_update_operands acc use_inst [(Var out_var, new_op)])
                  updater uses
End

Definition algebraic_opt_optimize_iszero_def:
  algebraic_opt_optimize_iszero updater =
    FOLDL
      (λacc bb. FOLDL (λacc2 inst. algebraic_opt_optimize_iszero_inst acc2 inst)
                       acc bb.bb_instructions)
      updater updater.iu_fn.fn_blocks
End

Definition algebraic_opt_handle_offset_inst_def:
  algebraic_opt_handle_offset_inst updater inst =
    if inst.inst_opcode = ADD then
      case inst.inst_operands of
        op1::op2::_ =>
          (case (op1, op2) of
             (Lit _, Label _) =>
               inst_updater_update updater inst OFFSET inst.inst_operands NONE
           | _ => updater)
      | _ => updater
    else updater
End

Definition algebraic_opt_handle_offset_def:
  algebraic_opt_handle_offset updater =
    FOLDL
      (λacc bb. FOLDL (λacc2 inst. algebraic_opt_handle_offset_inst acc2 inst)
                       acc bb.bb_instructions)
      updater updater.iu_fn.fn_blocks
End

Definition algebraic_opt_function_def:
  algebraic_opt_function fn =
    let dfg = dfg_analyze fn in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let updater1 = algebraic_opt_handle_offset updater in
    let updater2 = algebraic_opt_pass updater1 in
    let updater3 = algebraic_opt_optimize_iszero updater2 in
    let updater4 = algebraic_opt_pass updater3 in
    updater4.iu_fn
End

Definition algebraic_opt_context_def:
  algebraic_opt_context ctx =
    ctx with ctx_functions := MAP algebraic_opt_function ctx.ctx_functions
End

val _ = export_theory();
