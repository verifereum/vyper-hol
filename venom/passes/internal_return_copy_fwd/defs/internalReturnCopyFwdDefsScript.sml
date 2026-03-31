(*
 * Internal Return Copy Forwarding — Definitions
 *
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * Forwards copies of internal call memory return buffers:
 *
 *   invoke @callee_returning_memory, %ret_buf, ...
 *   mcopy %dst, %ret_buf, ...
 *
 * When %ret_buf has the expected constrained use-shape, rewrites %dst
 * uses to %ret_buf and removes the copy.
 *
 * Prerequisites for forwarding:
 *   1. Both dst and src roots are alloca instructions with matching sizes
 *   2. src is used exactly as: invoke return buffer (pos 1) + this mcopy src
 *   3. dst aliases are used only in same block, after the copy
 *   4. No memory clobber between the copy and the last dst use
 *   5. No PHI uses of dst aliases
 *
 * TOP-LEVEL:
 *   ircf_is_ret_buf_source    — validate src usage pattern
 *   ircf_invoke_may_clobber   — check if invoke may clobber src location
 *   ircf_invoke_op_may_write  — check if invoke operand position may write
 *   ircf_try_forward          — try to forward a single mcopy
 *   ircf_transform_block      — transform all mcopy in a block
 *   ircf_transform_function   — function-level transform
 *)

Theory internalReturnCopyFwdDefs
Ancestors
  invokeCopyFwdCommonDefs

(* ===== Return Buffer Source Validation ===== *)

(* Check if an invoke operand at position pos may write memory.
   Matches Python _invoke_operand_may_write:
   - pos 1 with return buffer: writable
   - non-readonly positions: writable *)
Definition ircf_invoke_op_may_write_def:
  ircf_invoke_op_may_write (ctx : icf_ctx) inst pos =
    if pos = 1 /\ icf_invoke_has_ret_buf ctx.icf_fn_meta ctx.icf_functions inst
    then T
    else ~icf_is_readonly_op ctx.icf_rma inst pos
End

(* Check if an invoke instruction may clobber a given memory location.
   Matches Python _invoke_may_clobber_src: for each writable operand,
   compute its pointer and check alias against src_loc. *)
Definition ircf_invoke_may_clobber_def:
  ircf_invoke_may_clobber (ctx : icf_ctx) inst (src_loc : mem_loc) =
    EXISTS (\(pos, op).
      if pos = 0 then F
      else if ~ircf_invoke_op_may_write ctx inst pos then F
      else
        case op of
          Var v =>
            (case bp_ptr_from_op ctx.icf_bp (Var v) of
               NONE => T  (* unknown pointer shape → conservative *)
             | SOME (Ptr alloc off) =>
                 let op_loc =
                   <| ml_offset := off;
                      ml_size := NONE;
                      ml_alloca := SOME alloc;
                      ml_volatile := F |> in
                 ma_may_alias ctx.icf_aliases src_loc op_loc)
        | _ => F)
    (MAPi (\i op. (i, op)) inst.inst_operands)
End

(* Validate that src_root is used as an internal return buffer source.
   Matches Python _is_internal_return_buffer_source:
   - All aliases of src_root are used only as:
     a) ASSIGN output (ignored)
     b) mcopy src (pos 1) for the given copy_inst
     c) invoke ret buffer (pos 1), must be in same block before copy
   - Exactly one invoke site
   - The copy is among the uses *)
Definition ircf_is_ret_buf_source_def:
  ircf_is_ret_buf_source (ctx : icf_ctx)
                          (bb_insts : instruction list)
                          (src_root : string)
                          (copy_inst_id : num)
                          (copy_idx : num) =
    let aliases = icf_collect_aliases ctx.icf_dfg src_root in
    let use_positions = icf_alias_use_positions ctx.icf_dfg aliases in
    let copy_seen = EXISTS (\(v, inst, (pos : num)).
      inst.inst_opcode = MCOPY /\ pos = 1 /\
      inst.inst_id = copy_inst_id) use_positions in
    let invoke_sites = FILTER (\(v, inst, (pos : num)).
      ~icf_is_assign_output_use inst pos /\
      ~(inst.inst_opcode = MCOPY /\ pos = 1 /\
        inst.inst_id = copy_inst_id) /\
      inst.inst_opcode = INVOKE /\ pos = 1)
      use_positions in
    (* Check all non-assign, non-copy, non-invoke uses are absent *)
    let other_uses = FILTER (\(v, inst, (pos : num)).
      ~icf_is_assign_output_use inst pos /\
      ~(inst.inst_opcode = MCOPY /\ pos = 1 /\
        inst.inst_id = copy_inst_id) /\
      ~(inst.inst_opcode = INVOKE /\ pos = 1))
      use_positions in
    if other_uses <> [] then F
    else if ~copy_seen then F
    else if LENGTH invoke_sites <> 1 then F
    else
      (* The single invoke must be in same BB, before copy, with ret buffer *)
      let (_, inv_inst, _) = HD invoke_sites in
      (* Check invoke is in the same block *)
      case findi (\el. el.inst_id = inv_inst.inst_id) bb_insts of
        NONE => F  (* invoke not in this block *)
      | SOME inv_idx =>
          (* Invoke must come before the copy *)
          if inv_idx >= copy_idx then F
          else icf_invoke_has_ret_buf ctx.icf_fn_meta ctx.icf_functions inv_inst
End

(* ===== Per-mcopy Transform ===== *)

(* Try to forward a single mcopy instruction.
   Matches Python _try_forward_internal_return_copy.

   Returns SOME (new_block_instructions) if forwarding succeeds,
   NONE if the mcopy cannot be forwarded. *)
Definition ircf_try_forward_def:
  ircf_try_forward (ctx : icf_ctx) (bb : basic_block) (copy_idx : num) =
    let insts = bb.bb_instructions in
    if copy_idx >= LENGTH insts then NONE else
    let copy_inst = EL copy_idx insts in
    if copy_inst.inst_opcode <> MCOPY then NONE else
    (* HOL4 EVM order: [dst; src; size].  Python order: [size; src; dst]. *)
    case copy_inst.inst_operands of
      [Var dst; Var src; Lit size_val] =>
             let dst_root = icf_assign_root ctx.icf_dfg {} dst in
             let src_root = icf_assign_root ctx.icf_dfg {} src in
             if dst_root = src_root then NONE else
             (case (dfg_get_def ctx.icf_dfg dst_root,
                    dfg_get_def ctx.icf_dfg src_root) of
                (SOME dst_inst, SOME src_inst) =>
                  if ~icf_is_alloca dst_inst \/
                     ~icf_is_alloca src_inst then NONE
                  else if ~icf_matches_alloca_size dst_inst size_val \/
                          ~icf_matches_alloca_size src_inst size_val
                  then NONE
                  else if ~ircf_is_ret_buf_source ctx insts src_root
                            copy_inst.inst_id copy_idx
                  then NONE
                  else
                  let dst_aliases = icf_collect_aliases ctx.icf_dfg dst_root in
                  let use_positions =
                    icf_alias_use_positions ctx.icf_dfg dst_aliases in
                  (* Check all non-assign, non-copy uses are in same BB,
                     after copy, no PHI *)
                  (* pos = 0 is mcopy dst in HOL4 EVM order [dst;src;size] *)
                  let rewrite_uses = FILTER (\(v, inst, (pos : num)).
                    ~icf_is_assign_output_use inst pos /\
                    ~(inst.inst_opcode = MCOPY /\ pos = 0 /\
                      inst.inst_id = copy_inst.inst_id))
                    use_positions in
                  if EXISTS (\(v, inst, (pos : num)). inst.inst_opcode = PHI)
                     rewrite_uses then NONE
                  else
                  (* Reject if any rewrite use is NOT at a memory address
                     operand position.  Non-address uses (e.g. ADD) would
                     compute on the raw pointer value, which differs
                     between src and dst allocas. *)
                  if EXISTS (\(v, inst, (pos : num)).
                       ~is_mem_addr_position inst.inst_opcode pos)
                     rewrite_uses then NONE
                  else
                  (* All rewrite uses must be in same block *)
                  let rewrite_insts = MAP (\(v, inst, pos). inst) rewrite_uses in
                  (* Get their indices in bb *)
                  let rewrite_idxs = MAP (\inst.
                    findi (\el. el.inst_id = inst.inst_id) insts) rewrite_insts in
                  if EXISTS (\idx. idx = NONE) rewrite_idxs then NONE
                  else
                  let actual_idxs = MAP THE rewrite_idxs in
                  if EXISTS (\idx. idx <= copy_idx) actual_idxs then NONE
                  else
                  (* Check no clobber between copy and last use *)
                  if actual_idxs <> [] then
                    let last_use_idx = FOLDL MAX 0 actual_idxs in
                    let src_loc = bp_get_read_location ctx.icf_bp
                                    copy_inst AddrSp_Memory in
                    if src_loc.ml_size <> SOME 0 then
                      if EXISTS (\i.
                        let idx = copy_idx + 1 + i in
                        if idx >= LENGTH insts then F
                        else
                          let inst = EL idx insts in
                          if inst.inst_opcode = INVOKE then
                            ircf_invoke_may_clobber ctx inst src_loc
                          else if Eff_MEMORY NOTIN
                                  write_effects inst.inst_opcode then F
                          else
                            let wloc = bp_get_write_location ctx.icf_bp
                                         inst AddrSp_Memory in
                            ma_may_alias ctx.icf_aliases src_loc wloc)
                        (COUNT_LIST (last_use_idx - copy_idx - 1))
                      then NONE
                      else
                      (* Rewrite: replace dst aliases with src_root in operands *)
                      let replace_set = dst_aliases in
                      SOME (MAPi (\i inst.
                        if i = copy_idx then mk_nop_inst inst
                        else if MEM inst.inst_id
                                    (MAP (\ri. ri.inst_id) rewrite_insts)
                        then inst with inst_operands :=
                          MAP (\op. case op of
                                 Var v => if v IN replace_set
                                          then Var src_root else op
                               | _ => op)
                            inst.inst_operands
                        else inst) insts)
                    else NONE  (* src_loc is empty (size=0) *)
                  else
                    (* No rewrite uses — just NOP the copy *)
                    SOME (MAPi (\i inst.
                      if i = copy_idx then mk_nop_inst inst
                      else inst) insts)
              | _ => NONE)
    | _ => NONE
End

(* ===== Block and Function Transform ===== *)

(* Transform a block: try forwarding each mcopy.
   Processes mcopy instructions left to right.
   Matches Python run_pass inner loop (per-block). *)
Definition ircf_transform_block_def:
  ircf_transform_block (ctx : icf_ctx) (bb : basic_block) =
    let result = FOLDL (\(changed, cur_bb) i.
      if i >= LENGTH cur_bb.bb_instructions then (changed, cur_bb)
      else
        let inst = EL i cur_bb.bb_instructions in
        if inst.inst_opcode <> MCOPY then (changed, cur_bb)
        else
          case ircf_try_forward ctx cur_bb i of
            NONE => (changed, cur_bb)
          | SOME new_insts =>
              (T, cur_bb with bb_instructions := new_insts))
      (F, bb) (COUNT_LIST (LENGTH bb.bb_instructions)) in
    result
End

(* Function-level transform.
   Matches Python run_pass: prepare analyses, iterate blocks, finish. *)
Definition ircf_transform_function_def:
  ircf_transform_function (fn_meta : (string, invoke_fn_meta) fmap)
                          (ctx_fns : ir_function list)
                          (rma : (string, bool list) fmap)
                          (fn : ir_function) =
    let ctx = icf_build_ctx fn_meta ctx_fns rma fn in
    let (changed, new_blocks) = FOLDL (\(changed, acc) bb.
      let (bb_changed, new_bb) = ircf_transform_block ctx bb in
      (changed \/ bb_changed, acc ++ [new_bb]))
      (F, []) fn.fn_blocks in
    let fn' = fn with fn_blocks := new_blocks in
    if changed then clear_nops_function fn' else fn'
End
