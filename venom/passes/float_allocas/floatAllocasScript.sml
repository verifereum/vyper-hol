(*
 * Float Allocas Pass
 *
 * Port of venom/passes/float_allocas.py.
 *)

Theory floatAllocas
Ancestors
  list
  venomInst

Definition is_alloca_inst_def:
  is_alloca_inst inst <=>
    inst.inst_opcode IN {ALLOCA; PALLOCA; CALLOCA}
End

Definition split_allocas_def:
  split_allocas [] = ([], []) /\
  split_allocas (inst::rest) =
    let (allocas, others) = split_allocas rest in
    if is_alloca_inst inst then (inst::allocas, others)
    else (allocas, inst::others)
End

Definition float_allocas_function_def:
  float_allocas_function fn =
    case fn.fn_blocks of
      [] => fn
    | entry_bb::rest =>
        if entry_bb.bb_instructions = [] then fn else
        let term = LAST entry_bb.bb_instructions in
        let entry_body = BUTLAST entry_bb.bb_instructions in
        let (entry_body', rest') =
          FOLDL
            (λacc bb.
               let (entry_acc, bbs_acc) = acc in
               let (allocas, others) = split_allocas bb.bb_instructions in
               let entry_acc' = entry_acc ++ allocas in
               let bb' = bb with bb_instructions := others in
               (entry_acc', bbs_acc ++ [bb']))
            (entry_body, []) rest in
        let entry' = entry_bb with bb_instructions := entry_body' ++ [term] in
        fn with fn_blocks := entry' :: rest'
End

Definition float_allocas_context_def:
  float_allocas_context ctx =
    ctx with ctx_functions := MAP float_allocas_function ctx.ctx_functions
End

val _ = export_theory();
