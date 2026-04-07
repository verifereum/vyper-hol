(*
 * Readonly Invoke Arg Copy Forwarding — Definitions
 *
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * Forwards staged memory args into readonly invoke parameters:
 *
 *   %tmp = alloca ...
 *   mcopy %tmp, %src, ...
 *   invoke @callee, ..., %tmp, ...
 *
 * Only readonly callee memory params are rewritten: %tmp → %src.
 * The mcopy is NOP'd.
 *
 * Prerequisites for forwarding:
 *   1. dst root is an alloca instruction
 *   2. dst aliases are used only as: ASSIGN output, mcopy dst (this copy),
 *      or readonly invoke operand
 *   3. All uses are in the same block, after the copy
 *   4. No source memory clobber between copy and uses
 *   5. src doesn't alias dst (self-copy check)
 *   6. No mutable sibling arg in the same invoke has the same source root
 *
 * SOUNDNESS NOTE (pointer arithmetic in callees):
 *   RICF rewrites INVOKE operands: Var dst_alias → Var src_root.
 *   The callee receives a different pointer value.  Even for "readonly"
 *   parameters (no memory WRITE through the pointer), the callee may
 *   compute on the pointer value itself (e.g. ADD %param, 32) and
 *   return a different result.  A correct proof requires an additional
 *   precondition: the callee uses the parameter ONLY at memory-address
 *   operand positions (is_mem_addr_position).  This is an inter-
 *   procedural property that cannot be checked from the call-site
 *   alone; it requires whole-program analysis or a per-function
 *   annotation.
 *
 * Runs to local fixpoint (chained staging copies).
 *
 * TOP-LEVEL:
 *   ricf_has_mutable_sibling — check for aliasing with mutable sibling arg
 *   ricf_try_forward         — try to forward a single mcopy
 *   ricf_pass_block          — single pass over a block's mcopy instructions
 *   ricf_function_step       — one iteration over all blocks
 *   ricf_transform_function  — function-level fixpoint transform
 *)

Theory readonlyInvokeCopyFwdDefs
Ancestors
  invokeCopyFwdCommonDefs

(* ===== Mutable Sibling Check ===== *)

(* Check if forwarding would create aliasing between a rewritten
   readonly arg and a sibling mutable arg in the same invoke.
   Matches Python _has_mutable_same_source_sibling_arg. *)
Definition ricf_has_mutable_sibling_def:
  ricf_has_mutable_sibling (ctx : icf_ctx)
                           (rewrite_sites : (instruction # num) list)
                           (src_root : string) =
    EXISTS (\(invoke_inst, rewritten_pos).
      EXISTS (\(pos, op).
        if pos = (0 : num) \/ pos = rewritten_pos then F
        else if icf_is_readonly_op ctx.icf_rma invoke_inst pos then F
        else
          let root = icf_assign_root_op ctx.icf_dfg op in
          case root of
            Var v => v = src_root
          | _ => F)
      (MAPi (\i op. (i, op)) invoke_inst.inst_operands))
    rewrite_sites
End

(* ===== Per-mcopy Transform ===== *)

(* Try to forward a single mcopy instruction.
   Matches Python _try_forward_readonly_copy.

   Returns SOME (new_block_instructions) if forwarding succeeds,
   NONE if the mcopy cannot be forwarded. *)
Definition ricf_try_forward_def:
  ricf_try_forward (ctx : icf_ctx) (bb : basic_block) (copy_idx : num) =
    let insts = bb.bb_instructions in
    if copy_idx >= LENGTH insts then NONE else
    let copy_inst = EL copy_idx insts in
    if copy_inst.inst_opcode <> MCOPY then NONE else
    (* HOL4 EVM order: [dst; src; size].  Python order: [size; src; dst]. *)
    case copy_inst.inst_operands of
      [Var dst; src_op; size_op] =>
        let root = icf_assign_root ctx.icf_dfg {} dst in
        (case dfg_get_def ctx.icf_dfg root of
           NONE => NONE
         | SOME root_inst =>
             if root_inst.inst_opcode <> ALLOCA then NONE
             else
             let aliases = icf_collect_aliases ctx.icf_dfg root in
             let use_positions = icf_alias_use_positions ctx.icf_dfg aliases in
             (* Validate use pattern *)
             let rewrite_sites_opt =
               FOLDL (\acc (v, inst, (pos : num)).
                 case acc of
                   NONE => NONE
                 | SOME sites =>
                     if icf_is_assign_output_use inst pos then SOME sites
                     (* pos = 0 is mcopy dst in HOL4 EVM order [dst;src;size] *)
                     else if inst.inst_opcode = MCOPY /\ pos = 0 then
                       if inst.inst_id = copy_inst.inst_id then SOME sites
                       else NONE  (* other mcopy dst use *)
                     else if inst.inst_opcode = INVOKE /\
                             icf_is_readonly_op ctx.icf_rma inst pos
                     then SOME ((inst, pos) :: sites)
                     else NONE)  (* invalid use *)
                 (SOME []) use_positions in
             case rewrite_sites_opt of
               NONE => NONE
             | SOME [] => NONE  (* no rewrite sites *)
             | SOME rewrite_sites =>
                 (* Check all invoke sites are in same block and after copy *)
                 let invoke_idxs = MAP (\(inst, pos).
                   findi (\el. el.inst_id = inst.inst_id) insts)
                   rewrite_sites in
                 if EXISTS (\idx. idx = NONE) invoke_idxs then NONE
                 else
                 let actual_idxs = MAP THE invoke_idxs in
                 if EXISTS (\idx. idx < copy_idx) actual_idxs then NONE
                 else
                 (* Check no source clobber *)
                 if icf_has_src_clobber ctx.icf_aliases ctx.icf_bp
                      insts copy_idx actual_idxs
                      (bp_get_read_location ctx.icf_bp copy_inst AddrSp_Memory)
                 then NONE
                 else
                 (* Resolve source *)
                 let src = icf_assign_root_op ctx.icf_dfg src_op in
                 (* Self-copy check + mutable sibling check *)
                 (case src of
                    Var sv => if sv IN aliases then NONE
                              else if ricf_has_mutable_sibling ctx
                                       rewrite_sites sv
                              then NONE
                              else SOME (SOME sv, rewrite_sites)
                  | _ => SOME (NONE, rewrite_sites))
        )
    | _ => NONE
End

(* Apply forwarding: NOP the mcopy, rewrite invoke operands.
   Collects ALL matching positions per instruction (an invoke may have
   the same alias at multiple arg positions). Matches Python's loop
   over all rewrite_sites. *)
Definition ricf_apply_forward_def:
  ricf_apply_forward (insts : instruction list) (copy_idx : num)
                     (src : operand)
                     (rewrite_sites : (instruction # num) list) =
    MAPi (\i inst.
      if i = copy_idx then mk_nop_inst inst
      else
        let positions = MAP SND
          (FILTER (\(ri, pos). ri.inst_id = inst.inst_id)
                  rewrite_sites) in
        if NULL positions then inst
        else inst with inst_operands :=
          MAPi (\j op.
            if MEM j positions /\ op <> src then src else op)
          inst.inst_operands)
    insts
End

(* ===== Block and Function Transform ===== *)

(* Single pass over a block: try forwarding each mcopy once.
   Returns (changed, new_bb). *)
Definition ricf_pass_block_def:
  ricf_pass_block (ctx : icf_ctx) (bb : basic_block) =
    FOLDL (\(changed, cur_bb) i.
      if i >= LENGTH cur_bb.bb_instructions then (changed, cur_bb)
      else
        let inst = EL i cur_bb.bb_instructions in
        if inst.inst_opcode <> MCOPY then (changed, cur_bb)
        else
          case ricf_try_forward ctx cur_bb i of
            NONE => (changed, cur_bb)
          | SOME (src_var_opt, rewrite_sites) =>
              let src_op =
                case src_var_opt of
                  SOME sv => Var sv
                | NONE =>
                    EL 1 (EL i cur_bb.bb_instructions).inst_operands in
              let new_insts = ricf_apply_forward
                cur_bb.bb_instructions i src_op rewrite_sites in
              (T, cur_bb with bb_instructions := new_insts))
      (F, bb) (COUNT_LIST (LENGTH bb.bb_instructions))
End

(* One iteration over all blocks in a function.
   Matches one iteration of Python's while-True loop in run_pass. *)
Definition ricf_function_step_def:
  ricf_function_step (ctx : icf_ctx) (fn : ir_function) =
    let (changed, new_blocks) = FOLDL (\(changed, acc) bb.
      let (bb_changed, new_bb) = ricf_pass_block ctx bb in
      (changed \/ bb_changed, acc ++ [new_bb]))
      (F, []) fn.fn_blocks in
    (changed, fn with fn_blocks := new_blocks)
End

(* Function-level fixpoint transform.
   Matches Python run_pass: iterates over all blocks until no change,
   rebuilding the DFG between iterations (Python uses InstUpdater to
   keep DFG fresh; we rebuild from the modified function). *)
Definition ricf_transform_function_def:
  ricf_transform_function (fn_meta : (string, invoke_fn_meta) fmap)
                          (ctx_fns : ir_function list)
                          (rma : (string, bool list) fmap)
                          (fn : ir_function) =
    let ctx0 = icf_build_ctx fn_meta ctx_fns rma fn in
    let result = OWHILE (\(changed, _, _). changed)
      (\(_, ctx, cur_fn).
        let (changed, new_fn) = ricf_function_step ctx cur_fn in
        if changed then
          (* Rebuild DFG from modified function, keep other analyses *)
          let ctx' = ctx with icf_dfg := dfg_build_function new_fn in
          (T, ctx', new_fn)
        else (F, ctx, cur_fn))
      (T, ctx0, fn) in
    case result of
      NONE => fn  (* non-termination fallback: return unchanged *)
    | SOME (_, _, fn') =>
        if fn'.fn_blocks <> fn.fn_blocks then clear_nops_function fn'
        else fn'
End
