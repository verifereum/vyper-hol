(*
 * Lower DLOAD/DLOADBYTES Pass
 *
 * Port of venom/passes/lower_dload.py.
 *)

Theory lowerDload
Ancestors
  list
  venomState venomInst
  compilerState

Definition lower_dload_insts_def:
  lower_dload_insts st [] = ([], st) /\
  lower_dload_insts st (inst::rest) =
    case inst.inst_opcode of
      DLOAD =>
        (case inst.inst_operands of
           [ptr] =>
             let (tmp_var, st1) = fresh_var st in
             let (tmp_id, st2) = fresh_inst_id st1 in
             let alloca_inst =
               mk_inst tmp_id ALLOCA [Lit (n2w 32)] [tmp_var] in
             let (code_ptr, st3) = fresh_var st2 in
             let (add_id, st4) = fresh_inst_id st3 in
             let add_inst =
               mk_inst add_id ADD [ptr; Label "code_end"] [code_ptr] in
             let (copy_id, st5) = fresh_inst_id st4 in
             let copy_inst =
               mk_inst copy_id CODECOPY
                 [Lit (n2w 32); Var code_ptr; Var tmp_var] [] in
             let inst' =
               inst with <| inst_opcode := MLOAD;
                            inst_operands := [Var tmp_var] |> in
             let (rest', st6) = lower_dload_insts st5 rest in
             (alloca_inst :: add_inst :: copy_inst :: inst' :: rest', st6)
         | _ =>
             let (rest', st1) = lower_dload_insts st rest in
             (inst :: rest', st1))
    | DLOADBYTES =>
        (case inst.inst_operands of
           sz::src::dst_op::rest_ops =>
             let (code_ptr, st1) = fresh_var st in
             let (add_id, st2) = fresh_inst_id st1 in
             let add_inst =
               mk_inst add_id ADD [src; Label "code_end"] [code_ptr] in
             let inst' =
               inst with <| inst_opcode := CODECOPY;
                            inst_operands := sz :: Var code_ptr :: dst_op :: rest_ops |> in
             let (rest', st3) = lower_dload_insts st2 rest in
             (add_inst :: inst' :: rest', st3)
         | _ =>
             let (rest', st1) = lower_dload_insts st rest in
             (inst :: rest', st1))
    | _ =>
        let (rest', st1) = lower_dload_insts st rest in
        (inst :: rest', st1)
End

Definition lower_dload_block_def:
  lower_dload_block st bb =
    let (insts', st') = lower_dload_insts st bb.bb_instructions in
    (bb with bb_instructions := insts', st')
End

Definition lower_dload_function_def:
  lower_dload_function fn =
    let st0 = init_state_for_function fn in
    let (bbs', _) =
      FOLDL
        (λacc bb.
           let (bbs, st) = acc in
           let (bb', st') = lower_dload_block st bb in
           (bbs ++ [bb'], st'))
        ([], st0) fn.fn_blocks in
    fn with fn_blocks := bbs'
End

Definition lower_dload_context_def:
  lower_dload_context ctx =
    ctx with ctx_functions := MAP lower_dload_function ctx.ctx_functions
End

val _ = export_theory();
