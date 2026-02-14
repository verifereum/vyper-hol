(*
 * Data-Flow Graph Analysis
 *
 * Reusable DFG helpers for Venom passes.
 * Tracks:
 *  - Uses: variable -> instructions that read it (in program order)
 *  - Defs: variable -> producing instruction
 *  - IDs: instruction id -> instruction
 *)

Theory dfgAnalysis
Ancestors
  list finite_map
  venomState venomInst

(* ==========================================================================
   Core DFG Type
   ========================================================================== *)

Datatype:
  dfg_analysis = <|
    dfg_uses : (string, instruction list) fmap;
    dfg_defs : (string, instruction) fmap;
    dfg_ids : (num, instruction) fmap
  |>
End

Definition dfg_empty_def:
  dfg_empty = <| dfg_uses := FEMPTY; dfg_defs := FEMPTY; dfg_ids := FEMPTY |>
End

Definition dfg_get_uses_def:
  dfg_get_uses dfg v =
    case FLOOKUP dfg.dfg_uses v of
      NONE => []
    | SOME uses => uses
End

Definition dfg_get_def_def:
  dfg_get_def dfg v = FLOOKUP dfg.dfg_defs v
End

Definition dfg_get_inst_by_id_def:
  dfg_get_inst_by_id dfg id = FLOOKUP dfg.dfg_ids id
End

(* ==========================================================================
   Variable/Instruction Helpers
   ========================================================================== *)

Definition operand_var_def:
  operand_var op =
    case op of
      Var v => SOME v
    | _ => NONE
End

Definition operand_vars_def:
  operand_vars [] = [] /\
  operand_vars (op::ops) =
    case operand_var op of
      NONE => operand_vars ops
    | SOME v => v :: operand_vars ops
End

Definition dfg_add_use_def:
  dfg_add_use dfg v inst =
    let uses = dfg_get_uses dfg v in
      if MEM inst uses then dfg
      else dfg with dfg_uses := dfg.dfg_uses |+ (v, inst :: uses)
End

Definition dfg_remove_use_def:
  dfg_remove_use dfg v inst_id =
    let uses = dfg_get_uses dfg v in
    let uses' = FILTER (λinst. inst.inst_id <> inst_id) uses in
      dfg with dfg_uses := dfg.dfg_uses |+ (v, uses')
End

Definition dfg_add_uses_def:
  dfg_add_uses dfg [] inst = dfg /\
  dfg_add_uses dfg (v::vs) inst =
    dfg_add_uses (dfg_add_use dfg v inst) vs inst
End

Definition dfg_add_defs_def:
  dfg_add_defs dfg [] inst = dfg /\
  dfg_add_defs dfg (v::vs) inst =
    dfg_add_defs (dfg with dfg_defs := dfg.dfg_defs |+ (v, inst)) vs inst
End

Definition dfg_set_def_def:
  dfg_set_def dfg v inst =
    dfg with dfg_defs := dfg.dfg_defs |+ (v, inst)
End

Definition dfg_remove_def_def:
  dfg_remove_def dfg v =
    dfg with dfg_defs := FDIFF dfg.dfg_defs {v}
End

Definition dfg_set_inst_by_id_def:
  dfg_set_inst_by_id dfg inst =
    dfg with dfg_ids := dfg.dfg_ids |+ (inst.inst_id, inst)
End

Definition dfg_remove_inst_by_id_def:
  dfg_remove_inst_by_id dfg id =
    dfg with dfg_ids := FDIFF dfg.dfg_ids {id}
End

Definition dfg_add_inst_def:
  dfg_add_inst dfg inst =
    let in_vars = operand_vars inst.inst_operands in
    let dfg1 = dfg_add_uses dfg in_vars inst in
    let dfg2 = dfg_add_defs dfg1 inst.inst_outputs inst in
      dfg2 with dfg_ids := dfg2.dfg_ids |+ (inst.inst_id, inst)
End

(* ==========================================================================
   Build DFG from Instruction Lists / Functions
   ========================================================================== *)

Definition fn_insts_blocks_def:
  fn_insts_blocks [] = [] /\
  fn_insts_blocks (bb::bbs) =
    bb.bb_instructions ++ fn_insts_blocks bbs
End

Definition fn_insts_def:
  fn_insts fn = fn_insts_blocks fn.fn_blocks
End

Definition dfg_build_insts_rev_def:
  dfg_build_insts_rev dfg [] = dfg /\
  dfg_build_insts_rev dfg (inst::rest) =
    dfg_build_insts_rev (dfg_add_inst dfg inst) rest
End

Definition dfg_build_insts_def:
  dfg_build_insts insts =
    dfg_build_insts_rev dfg_empty (REVERSE insts)
End

Definition dfg_build_function_def:
  dfg_build_function fn = dfg_build_insts (fn_insts fn)
End

val _ = export_theory();
