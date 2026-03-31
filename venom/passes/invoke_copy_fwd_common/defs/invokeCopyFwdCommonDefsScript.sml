(*
 * Invoke Copy Forwarding Common — Definitions
 *
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * Shared helpers for both invoke copy forwarding passes:
 *   - InternalReturnCopyForwardingPass
 *   - ReadonlyInvokeArgCopyForwardingPass
 *
 * Models the InvokeCopyForwardingBase Python class, which provides:
 *   - DFG, dominator tree, base ptr, mem alias analysis setup
 *   - Assign chain traversal (assign_root, collect_assign_aliases)
 *   - Alloca matching
 *   - Readonly operand checking via ReadonlyMemoryArgsGlobalAnalysis
 *   - Source clobber detection
 *
 * TOP-LEVEL:
 *   icf_ctx                  — analysis context for copy forwarding
 *   icf_build_ctx            — build context from function + readonly analysis
 *   icf_assign_root          — follow assign chain to root variable
 *   icf_assign_root_op       — same for operand
 *   icf_collect_aliases      — collect all assign chain aliases
 *   icf_is_alloca            — check if instruction is alloca
 *   icf_matches_alloca_size  — check alloca size matches
 *   icf_invoke_has_ret_buf   — check if invoke has return buffer
 *   icf_is_readonly_invoke_op — check if invoke operand position is readonly
 *   icf_get_invoke_callee    — resolve invoke callee name
 *   icf_has_src_clobber      — check for source clobber between copy and uses
 *
 * Proof:
 *   icf_equiv                — state equiv allowing vs_memory to differ
 *
 * Helper:
 *   icf_iter_use_positions   — iterate use positions for a variable
 *)

Theory invokeCopyFwdCommonDefs
Ancestors
  readonlyMemoryArgsDefs dfgDefs basePtrDefs memAliasDefs dominatorDefs
  passSharedDefs venomEffects cfgDefs

(* ===== Analysis Context ===== *)

(* Bundles all analyses needed by copy forwarding passes.
   Matches Python InvokeCopyForwardingBase fields. *)
Datatype:
  icf_ctx = <|
    icf_dfg : dfg_analysis;
    icf_dom : dom_analysis;
    icf_bp : bp_result;
    icf_aliases : alias_sets;
    icf_rma : (string, bool list) fmap;
    icf_fn_meta : (string, invoke_fn_meta) fmap;
    icf_functions : ir_function list
  |>
End

(* Build context for a function.
   Matches Python InvokeCopyForwardingBase._prepare. *)
Definition icf_build_ctx_def:
  icf_build_ctx (fn_meta : (string, invoke_fn_meta) fmap)
                (functions : ir_function list)
                (rma_result : (string, bool list) fmap)
                (fn : ir_function) =
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let dom = dom_analyze cfg fn in
    let bp = bp_analyze cfg fn in
    let aliases = memory_alias_analyze bp fn in
    <| icf_dfg := dfg;
       icf_dom := dom;
       icf_bp := bp;
       icf_aliases := aliases;
       icf_rma := rma_result;
       icf_fn_meta := fn_meta;
       icf_functions := functions |>
End

(* ===== Assign Chain Traversal ===== *)

(* Follow ASSIGN chain to root variable.
   Matches Python _assign_root_var: iterates through ASSIGN instructions
   until a non-ASSIGN producer or non-variable source is found.
   Uses visited set for termination. *)
Definition icf_assign_root_def:
  icf_assign_root (dfg : dfg_analysis) (visited : string set) (v : string) =
    if v IN visited then v
    else
      case dfg_get_def dfg v of
        NONE => v
      | SOME inst =>
          if inst.inst_opcode = ASSIGN then
            case inst.inst_operands of
              [Var src] => icf_assign_root dfg (v INSERT visited) src
            | _ => v
          else v
Termination
  WF_REL_TAC `measure (\(dfg, visited, v).
    CARD (FDOM dfg.dfg_defs DIFF visited))`
  >> rw[]
  >> irule pred_setTheory.CARD_PSUBSET >> conj_tac
  >- simp[pred_setTheory.FINITE_DIFF, finite_mapTheory.FDOM_FINITE]
  >> simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
          pred_setTheory.EXTENSION]
  >> qexists_tac `v`
  >> fs[finite_mapTheory.FLOOKUP_DEF, dfgDefsTheory.dfg_get_def_def]
End

(* Follow assign chain for an operand.
   Matches Python _assign_root. *)
Definition icf_assign_root_op_def:
  icf_assign_root_op dfg (Var v) = Var (icf_assign_root dfg {} v) /\
  icf_assign_root_op dfg op = op
End

(* ===== Alias Collection ===== *)

(* Collect all variables reachable through ASSIGN chains from a root.
   Matches Python _collect_assign_aliases: BFS through ASSIGN uses.
   We model this as a fixpoint: start with {root}, repeatedly add
   outputs of ASSIGN instructions that use any alias.

   Uses OWHILE for termination. *)
Definition icf_aliases_step_def:
  icf_aliases_step (dfg : dfg_analysis)
                   (aliases : string set) =
    let new_vars =
      BIGUNION (IMAGE (\v.
        let uses = dfg_get_uses dfg v in
        IMAGE (\inst.
          if inst.inst_opcode = ASSIGN then
            case inst.inst_outputs of
              [out] => out
            | _ => ""
          else "")
          (set uses))
        aliases) in
    let added = new_vars DIFF aliases DIFF {""} in
    (added <> {}, aliases UNION added)
End

Definition icf_collect_aliases_def:
  icf_collect_aliases dfg root =
    let result = OWHILE (\(changed, _). changed)
      (\(_, als). icf_aliases_step dfg als)
      (T, {root}) in
    case result of
      NONE => {root}
    | SOME (_, aliases) => aliases
End

(* ===== Alloca Checks ===== *)

(* Check if an instruction is an alloca.
   Matches Python _is_alloca_like. *)
Definition icf_is_alloca_def:
  icf_is_alloca (inst : instruction) = (inst.inst_opcode = ALLOCA)
End

(* Check if alloca size matches expected value.
   Matches Python _matches_alloca_size. *)
Definition icf_matches_alloca_size_def:
  icf_matches_alloca_size (inst : instruction) (expected : bytes32) =
    case inst.inst_operands of
      [Lit n] => (n = expected)
    | _ => F
End

(* ===== Invoke Helpers ===== *)

(* Get the callee function name from an INVOKE instruction.
   Matches Python _get_invoke_callee. *)
Definition icf_get_callee_name_def:
  icf_get_callee_name (inst : instruction) =
    case inst.inst_operands of
      (Label lbl :: _) => SOME lbl
    | _ => NONE
End

(* Check if invoke has a return buffer (first arg is memory return buffer).
   Matches Python _invoke_has_return_buffer. *)
Definition icf_invoke_has_ret_buf_def:
  icf_invoke_has_ret_buf (fn_meta : (string, invoke_fn_meta) fmap)
                         (functions : ir_function list)
                         (inst : instruction) =
    case icf_get_callee_name inst of
      NONE => F
    | SOME name =>
        if ~EXISTS (\fn. fn.fn_name = name) functions then F
        else
        case FLOOKUP fn_meta name of
          NONE => F
        | SOME meta =>
            let invoke_arg_count = LENGTH inst.inst_operands - 1 in
            if invoke_arg_count <> meta.ifm_invoke_param_count then F
            else meta.ifm_has_memory_return_buffer
End

(* Check if an invoke operand at position pos is readonly.
   Matches Python _is_readonly_invoke_operand.
   pos is 0-based over all operands (pos 0 = target label). *)
Definition icf_is_readonly_op_def:
  icf_is_readonly_op (rma : (string, bool list) fmap)
                     (inst : instruction)
                     (pos : num) =
    if pos = 0 then F
    else
      case icf_get_callee_name inst of
        NONE => F
      | SOME name =>
          rma_is_readonly rma name (pos - 1)
End

(* ===== Source Clobber Detection ===== *)

(* Check if any instruction between copy and use sites may alias
   the copy's source location.
   Matches Python _has_src_clobber_between.

   copy_inst_idx: index of mcopy in its block's instruction list.
   rewrite_sites: set of (instruction_index) in the same block.
   src_loc: memory location being read by the copy. *)
Definition icf_has_src_clobber_def:
  icf_has_src_clobber (aliases : alias_sets) (bp : bp_result)
                      (bb_insts : instruction list)
                      (copy_idx : num)
                      (invoke_idxs : num list)
                      (src_loc : mem_loc) =
    (* Matches Python _has_src_clobber_between: empty locations (size=0)
       cannot be clobbered *)
    if src_loc.ml_size = SOME 0 then F
    else
    EXISTS (\invoke_idx.
      EXISTS (\i.
        let inst = EL (copy_idx + 1 + i) bb_insts in
        if Eff_MEMORY NOTIN write_effects inst.inst_opcode then F
        else
          let write_loc = bp_get_write_location bp inst AddrSp_Memory in
          ma_may_alias aliases src_loc write_loc)
      (COUNT_LIST (invoke_idx - copy_idx - 1)))
    invoke_idxs
End

(* ===== Use Position Iteration ===== *)

(* Find all positions where a variable is used as an operand.
   Returns list of (instruction, operand_position) pairs.
   Matches Python _iter_use_positions. *)
Definition icf_use_positions_def:
  icf_use_positions (dfg : dfg_analysis) (v : string) =
    let uses = dfg_get_uses dfg v in
    FLAT (MAP (\inst.
      FLAT (MAPi (\pos op.
        case op of
          Var u => if u = v then [(inst, pos)] else []
        | _ => [])
        inst.inst_operands))
      uses)
End

(* Find index of element in list by predicate.
   Wrapper around stdlib INDEX_FIND for readability. *)
Definition findi_def:
  findi P l = OPTION_MAP FST (INDEX_FIND 0 P l)
End

(* Check if a use is an ASSIGN output use (operand 0 of ASSIGN).
   Matches Python _is_assign_output_use. *)
Definition icf_is_assign_output_use_def:
  icf_is_assign_output_use inst (pos : num) =
    (inst.inst_opcode = ASSIGN /\ pos = 0)
End

(* Iterate alias use positions: for each alias variable, find all
   use positions. Callers filter as needed. *)
Definition icf_alias_use_positions_def:
  icf_alias_use_positions (dfg : dfg_analysis) (aliases : string set) =
    FLAT (MAP (\v. MAP (\(inst, pos). (v, inst, pos))
                       (icf_use_positions dfg v))
      (SET_TO_LIST aliases))
End

(* ===== Memory Address Position Check ===== *)

(* Check whether operand position `pos` of `opc` is a memory address position,
   i.e., the value is used solely as a memory address (w2n addr) and never
   computed upon.  Forwarding a pointer at such a position is safe: the
   instruction will read/write at the substituted address rather than
   performing arithmetic on the pointer value.

   Derived from step_inst_base semantics (venomExecSemanticsScript.sml)
   and mem_write_ops/mem_read_ops (memLocDefsScript.sml).

   INVOKE is excluded: callee parameter usage is interprocedural and
   requires separate analysis (see ricf). *)
Definition is_mem_addr_position_def:
  is_mem_addr_position opc (pos : num) <=>
    (* Memory read/write — single-address operands *)
    (opc = MLOAD  /\ pos = 0) \/   (* mload [addr] *)
    (opc = MSTORE /\ pos = 0) \/   (* mstore [addr; val] *)
    (opc = ISTORE /\ pos = 0) \/   (* istore [addr; val] — immutable space *)
    (* Bulk copy — dst and src addresses *)
    (opc = MCOPY         /\ pos = 0) \/  (* mcopy [dst; src; sz] *)
    (opc = MCOPY         /\ pos = 1) \/
    (opc = CALLDATACOPY  /\ pos = 0) \/  (* calldatacopy [dst; cdsrc; sz] *)
    (opc = DLOADBYTES    /\ pos = 0) \/  (* dloadbytes [dst; dsrc; sz] *)
    (opc = CODECOPY      /\ pos = 0) \/  (* codecopy [dst; csrc; sz] *)
    (opc = RETURNDATACOPY /\ pos = 0) \/ (* returndatacopy [dst; rdsrc; sz] *)
    (opc = EXTCODECOPY   /\ pos = 1) \/  (* extcodecopy [addr; dst; src; sz] *)
    (* External calls — memory offset operands only *)
    (opc = CALL         /\ pos = 3) \/  (* call [gas;addr;val;argsOff;as;retOff;rs] *)
    (opc = CALL         /\ pos = 5) \/
    (opc = STATICCALL   /\ pos = 2) \/  (* staticcall [gas;addr;argsOff;as;retOff;rs] *)
    (opc = STATICCALL   /\ pos = 4) \/
    (opc = DELEGATECALL /\ pos = 2) \/  (* delegatecall [gas;addr;argsOff;as;retOff;rs] *)
    (opc = DELEGATECALL /\ pos = 4) \/
    (* Create — init code memory region *)
    (opc = CREATE  /\ pos = 1) \/       (* create [val; off; sz] *)
    (opc = CREATE2 /\ pos = 1) \/       (* create2 [val; off; sz; salt] *)
    (* Hash / terminator reads *)
    (opc = SHA3    /\ pos = 0) \/       (* sha3 [off; sz] *)
    (opc = RETURN  /\ pos = 0) \/       (* return [off; sz] *)
    (opc = REVERT  /\ pos = 0) \/       (* revert [off; sz] *)
    (* Log — operand 0 is Lit topic_count, operand 1 is memory offset *)
    (opc = LOG     /\ pos = 1)          (* log [tc; off; sz; topics...] *)
End

(* ===== Proof Equivalence Relation ===== *)

(* State equivalence allowing vs_memory to differ.
   Both copy forwarding passes NOP mcopy instructions, removing a memory
   write to the dst allocation. The forwarding preconditions ensure no
   instruction reads from that memory after the rewrite, so the memory
   difference is at a dead location.
   Includes control flow fields so it can serve as both R_ok and R_term
   in lift_result. *)
Definition icf_equiv_def:
  icf_equiv s1 s2 <=>
    (!v. lookup_var v s1 = lookup_var v s2) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas
End
