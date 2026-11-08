(*
 * Internal Return Copy Forwarding — what a transformed block is
 *
 * ircf_transform_block folds ircf_try_forward over a block's MCOPYs,
 * always consulting the DFG of the original function while the block
 * changes under it.  This theory states its result without the fold:
 * the forwarded copies are the source MCOPYs that became NOPs, each
 * meets the use-shape conditions on the original function, ASSIGNs are
 * untouched, and every other instruction has each destination alias of
 * a forwarded copy replaced by that copy's source root.
 *
 * TOP-LEVEL:
 *   ircf_alias              — v reachable from x by ASSIGN chains
 *   ircf_fwd_ok             — the conditions one forwarded copy meets
 *   ircf_block_plan         — the transformed block, described
 *   ircf_transform_block_plan — ircf_transform_block meets it
 *)

Theory internalReturnCopyFwdPlan
Ancestors
  internalReturnCopyFwdDefs invokeCopyFwdCommonDefs dfgDefs passSharedDefs
  venomWf venomInst list pred_set

(* v is x, or the output of an ASSIGN of an alias of x *)
Inductive ircf_alias:
[~refl:]
  (!fn x. ircf_alias fn x x)
[~assign:]
  (!fn x v inst out.
     ircf_alias fn x v /\ MEM inst (fn_insts fn) /\
     inst.inst_opcode = ASSIGN /\ MEM (Var v) inst.inst_operands /\
     inst.inst_outputs = [out] ==>
     ircf_alias fn x out)
End

Definition ircf_alloca_of_def:
  ircf_alloca_of fn x sz <=>
    ?ai. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
         ai.inst_outputs = [x] /\ ai.inst_operands = [Lit sz]
End

(* The destination root, source root and size of a forwardable copy, as
   ircf_try_forward computes them. *)
Definition ircf_copy_roots_def:
  ircf_copy_roots fn (inst:instruction) =
    case inst.inst_operands of
      [Var dv; Var sv; Lit sz] =>
        SOME (icf_assign_root (dfg_build_function fn) {} dv,
              icf_assign_root (dfg_build_function fn) {} sv, sz)
    | _ => NONE
End

(* The copies forwarded from bb to bb2 *)
Definition ircf_fwds_def:
  ircf_fwds (bb:basic_block) (bb2:basic_block) =
    {k | k < LENGTH bb.bb_instructions /\
         (EL k bb.bb_instructions).inst_opcode = MCOPY /\
         (EL k bb2.bb_instructions).inst_opcode = NOP}
End

(* Copy k of bb, MCOPY d <- s of sz bytes, meets the use shape:
   both roots are ALLOCAs of sz bytes; the source's aliases are used only
   by ASSIGNs, this copy, and INVOKEs earlier in bb; the destination's
   aliases, apart from ASSIGNs and this copy, only later in bb, by
   non-PHIs, as memory addresses. *)
Definition ircf_fwd_ok_def:
  ircf_fwd_ok fn bb k d s sz <=>
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = MCOPY /\
    (?dv sv.
       (EL k bb.bb_instructions).inst_operands = [Var dv; Var sv; Lit sz] /\
       ircf_alias fn d dv /\ ircf_alias fn s sv) /\
    d <> s /\ ircf_alloca_of fn d sz /\ ircf_alloca_of fn s sz /\
    (!inst v.
       MEM inst (fn_insts fn) /\ ircf_alias fn s v /\
       MEM (Var v) inst.inst_operands ==>
       inst.inst_opcode = ASSIGN \/
       inst.inst_id = (EL k bb.bb_instructions).inst_id \/
       (inst.inst_opcode = INVOKE /\
        ?i. i < k /\ EL i bb.bb_instructions = inst)) /\
    (!inst v.
       MEM inst (fn_insts fn) /\ ircf_alias fn d v /\
       MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> ASSIGN /\
       inst.inst_id <> (EL k bb.bb_instructions).inst_id ==>
       inst.inst_opcode <> PHI /\
       (?i. k < i /\ i < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = inst) /\
       (!pos v'.
          pos < LENGTH inst.inst_operands /\
          EL pos inst.inst_operands = Var v' /\ ircf_alias fn d v' ==>
          is_mem_addr_position inst.inst_opcode pos))
End

(* v redirected to the source root of the forwarded copy whose
   destination it aliases, if any *)
Definition ircf_redirect_def:
  ircf_redirect fn bb bb2 v =
    if ?k d s sz. k IN ircf_fwds bb bb2 /\
                  ircf_copy_roots fn (EL k bb.bb_instructions) =
                    SOME (d,s,sz) /\
                  ircf_alias fn d v
    then @s. ?k d sz. k IN ircf_fwds bb bb2 /\
                      ircf_copy_roots fn (EL k bb.bb_instructions) =
                        SOME (d,s,sz) /\
                      ircf_alias fn d v
    else v
End

Definition ircf_redirect_op_def:
  ircf_redirect_op fn bb bb2 op =
    case op of Var v => Var (ircf_redirect fn bb bb2 v) | _ => op
End

Definition ircf_block_plan_def:
  ircf_block_plan fn bb bb2 <=>
    bb2.bb_label = bb.bb_label /\
    LENGTH bb2.bb_instructions = LENGTH bb.bb_instructions /\
    (!k. k IN ircf_fwds bb bb2 ==>
         ?d s sz.
           ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
           ircf_fwd_ok fn bb k d s sz) /\
    (!i. i < LENGTH bb.bb_instructions ==>
         EL i bb2.bb_instructions =
           if i IN ircf_fwds bb bb2 then mk_nop_inst (EL i bb.bb_instructions)
           else if (EL i bb.bb_instructions).inst_opcode = ASSIGN
           then EL i bb.bb_instructions
           else (EL i bb.bb_instructions) with inst_operands :=
                  MAP (ircf_redirect_op fn bb bb2)
                    (EL i bb.bb_instructions).inst_operands)
End

(* Why it holds: ircf_try_forward keeps the length and every inst_id, and
   only NOPs its copy and rewrites the instructions the original DFG lists
   as non-ASSIGN uses of the destination aliases.  A forwarded copy is
   never rewritten before it is forwarded (a destination alias used by an
   MCOPY other than its own copy writes memory, which
   ircf_no_dst_write_alias forbids; a source alias used by another copy
   fails ircf_is_ret_buf_source), so its operands and the DFG facts are
   the original ones.  icf_collect_aliases over the original DFG is
   ircf_alias (dfg_build_function_uses_sound/complete), and distinct
   roots have disjoint alias sets under SSA, so the redirect is
   well-defined. *)
Theorem ircf_transform_block_plan:
  !fn_meta ctx_fns rma fn bb.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks ==>
    ircf_block_plan fn bb
      (SND (ircf_transform_block (icf_build_ctx fn_meta ctx_fns rma fn) bb))
Proof
  cheat
QED
