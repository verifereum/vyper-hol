(*
 * Mem2Var Pass — Definitions
 *
 * Ports vyper/venom/passes/mem2var.py to HOL4.
 *
 * Promotes memory operations to variable operations where safe:
 *   - alloca only used by mstore/mload/return → promote to variable
 *
 * For alloca promotion (size = 32):
 *   mstore [alloca_addr; val]  → assign [val] → [alloca_var]
 *   mload [alloca_addr]        → assign [alloca_var] → [orig_out]
 *   return with alloca_addr    → insert mstore before, keep return
 *
 * Uses DFG analysis (use tracking per variable).
 *
 * TOP-LEVEL:
 *   m2v_can_promote_alloca      — check if alloca uses are all mstore/mload/return
 *   m2v_promote_inst            — promote a single alloca use
 *   m2v_transform_function      — function-level transform
 *   m2v_stores_dominate_loads   — precondition: MSTOREs dominate MLOADs per alloca
 *   m2v_promotable_wf           — all promoted allocas satisfy domination
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
 *)

Theory mem2varDefs
Ancestors
  passTransform dfgDefs venomExecSemantics venomInst venomWf
  pred_set finite_map irSupply

(* ===== Fresh Variable ===== *)

Definition m2v_fresh_var_def:
  m2v_fresh_var (varname : string) (count : num) =
    STRCAT "alloca_" (STRCAT varname (STRCAT "_" (toString count)))
End

(* ===== Use Analysis ===== *)

(* Check if all uses are mstore/mload/return (promotable).
   Requires at least one mstore (otherwise never written). *)
Definition m2v_can_promote_alloca_def:
  m2v_can_promote_alloca uses <=>
    EVERY (\inst. inst.inst_opcode = MSTORE \/
                  inst.inst_opcode = MLOAD \/
                  inst.inst_opcode = RETURN) uses /\
    EXISTS (\inst. inst.inst_opcode = MSTORE) uses
End



(* ===== Store-Dominates-Load Precondition ===== *)

(* For a given alloca output variable, every MLOAD use is dominated
   by some MSTORE use of the same alloca.  Without this, promotion
   can turn a read-from-zero-memory into a read-from-undefined-variable.
   Python's SSA sandwich (MakeSSA before mem2var) ensures this in practice. *)
Definition m2v_stores_dominate_loads_def:
  m2v_stores_dominate_loads fn alloca_out <=>
    !bb load_inst.
      MEM bb fn.fn_blocks /\
      MEM load_inst bb.bb_instructions /\
      (load_inst.inst_opcode = MLOAD \/ load_inst.inst_opcode = RETURN) /\
      MEM (Var alloca_out) load_inst.inst_operands ==>
      ?store_bb store_inst.
        MEM store_bb fn.fn_blocks /\
        MEM store_inst store_bb.bb_instructions /\
        store_inst.inst_opcode = MSTORE /\
        MEM (Var alloca_out) store_inst.inst_operands /\
        fn_dominates fn store_bb.bb_label bb.bb_label /\
        (store_bb = bb ==>
          ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
                EL i bb.bb_instructions = store_inst /\
                EL j bb.bb_instructions = load_inst)
End

(* Every promoted alloca satisfies the store-dominates-load property. *)
Definition m2v_promotable_wf_def:
  m2v_promotable_wf fn <=>
    let dfg = dfg_build_function fn in
    !inst alloca_out.
      MEM inst (fn_insts fn) /\
      inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [alloca_out] /\
      m2v_can_promote_alloca (dfg_get_uses dfg alloca_out) ==>
      m2v_stores_dominate_loads fn alloca_out
End

(* ===== Promotion Transform ===== *)

(*
 * Promote a single mstore/mload/return instruction that uses an alloca.
 *
 * Parameters:
 *   alloca_var  — the promoted variable name
 *   alloca_out  — the original alloca output (address variable)
 *   size        — alloca size (only promote if 32)
 *   inst        — instruction to transform
 *
 * In HOL4 semantic operand order:
 *   mstore [offset; value] → if offset = alloca_out: assign [value] → [alloca_var]
 *   mload [addr] → if addr = alloca_out: assign [Var alloca_var] → [orig_out]
 *   return [offset; size] → if offset = alloca_out: insert mstore before, keep return
 *)
Definition m2v_promote_inst_def:
  m2v_promote_inst alloca_var alloca_out (size : num) inst =
    if inst.inst_opcode = MSTORE /\ size = 32 then
      case inst.inst_operands of
        [ofs; val_op] =>
          if ofs = Var alloca_out then
            (* mstore to alloca → assign val to promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [val_op];
                          inst_outputs := [alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = MLOAD /\ size = 32 then
      case inst.inst_operands of
        [addr] =>
          if addr = Var alloca_out then
            (* mload from alloca → assign promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [Var alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = RETURN /\ size <= 32 then
      case inst.inst_operands of
        (* HOL4 RETURN: [offset; size]. Python operands[1] = offset = HOL4 op1.
           Check if offset (first operand) is the alloca address. *)
        [off_op; sz_op] =>
          if off_op = Var alloca_out then
            (* return from alloca: insert mstore to materialize value *)
            let store = <| inst_id := inst.inst_id;
                           inst_opcode := MSTORE;
                           inst_operands := [Var alloca_out; Var alloca_var];
                           inst_outputs := [] |> in
            [store; inst]
          else [inst]
      | _ => [inst]
    else [inst]
End

(* ===== Function-Level Transform ===== *)

(*
 * Transform function: collect promotion info, then rewrite instructions.
 *
 * Single-pass approach (post alloca_id removal — upstream 8780b3134):
 *   1. Scan ALLOCA instructions, determine which are promotable
 *   2. Rewrite all instructions according to promotion decisions
 *
 * An alloca is promotable iff ALL uses are mstore/mload/return
 * (checked by m2v_can_promote_alloca). Non-promotable allocas are
 * left unchanged — the old _fix_adds / escape_use path was removed
 * upstream because phi/assign guards on alloca are impossible after
 * alloca_id removal.
 *)
Definition m2v_transform_function_def:
  m2v_transform_function fn =
    let dfg = dfg_build_function fn in
    (* Collect alloca instructions *)
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    (* Build promotion map *)
    let scan_result = FOLDL (\(ctr, promos) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos)
          else
            (ctr, promos)
        | _ => (ctr, promos))
      (0, []) alloca_insts in
    let promo_list = SND scan_result in
    (* Rewrite instructions *)
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE => [i] in
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        FLAT (MAP rewrite_inst bb.bb_instructions))
      fn.fn_blocks
End

(* Fresh variables introduced by the transform *)
Definition m2v_fresh_vars_def:
  m2v_fresh_vars fn =
    let dfg = dfg_build_function fn in
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    let scan_result = FOLDL (\(ctr, fresh) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, var INSERT fresh)
          else
            (ctr, fresh)
        | _ => (ctr, fresh))
      (0, {}) alloca_insts in
    SND scan_result
End

(* Fresh variable names don't collide with any original instruction
   output or operand variable. This ensures:
   (1) original execution never writes to fresh variables
   (2) original instructions never read fresh variables
   so operand agreement holds between original and transformed states. *)
Definition m2v_fresh_names_disjoint_def:
  m2v_fresh_names_disjoint fn <=>
    !v. v IN m2v_fresh_vars fn ==>
      !inst. MEM inst (fn_insts fn) ==>
        ~MEM v inst.inst_outputs /\ ~MEM (Var v) inst.inst_operands
End


(* ================================================================
   INVARIANT DEFINITIONS (moved from mem2varProofsScript)
   ================================================================ *)

(* Promotion list: extracted from function *)
Definition m2v_promo_list_def:
  m2v_promo_list fn =
    let dfg = dfg_build_function fn in
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA) (fn_insts fn) in
    SND (FOLDL (\(ctr, promos) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos)
          else (ctr, promos)
        | _ => (ctr, promos))
      (0, []) alloca_insts)
End

(* Block transform *)
Definition m2v_bt_def:
  m2v_bt fn bb =
    let promo_list = m2v_promo_list fn in
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE => [i] in
    bb with bb_instructions :=
      FLAT (MAP rewrite_inst bb.bb_instructions)
End

(* ===== Supply-aware Function-Level Transform ===== *)

(*
 * Same rewrite as m2v_transform_function, except that the mstore inserted
 * before a promoted return takes a fresh inst_id from the supply instead of
 * reusing the return's (Python's add_before creates a new instruction).
 * m2v_promote_inst returns two instructions only in that case.
 *)
Definition m2v_promote_inst_supply_def:
  m2v_promote_inst_supply alloca_var alloca_out (size : num) s inst =
    case m2v_promote_inst alloca_var alloca_out size inst of
      [store; ret] =>
        (case fresh_inst_id s of
           (id, s1) => ([store with inst_id := id; ret], s1))
    | out => (out, s)
End

Definition m2v_rewrite_inst_supply_def:
  m2v_rewrite_inst_supply promo_list s (i : instruction) =
    case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
      SOME (ao, pvar, sz) => m2v_promote_inst_supply pvar ao sz s i
    | NONE => ([i], s)
End

Definition m2v_rewrite_insts_supply_def:
  m2v_rewrite_insts_supply promo_list s [] = ([], s) /\
  m2v_rewrite_insts_supply promo_list s (i :: is) =
    case m2v_rewrite_inst_supply promo_list s i of
      (out, s1) =>
        case m2v_rewrite_insts_supply promo_list s1 is of
          (outs, s2) => (out ++ outs, s2)
End

Definition m2v_rewrite_blocks_supply_def:
  m2v_rewrite_blocks_supply promo_list s [] = ([], s) /\
  m2v_rewrite_blocks_supply promo_list s (bb :: bbs) =
    case m2v_rewrite_insts_supply promo_list s bb.bb_instructions of
      (insts, s1) =>
        case m2v_rewrite_blocks_supply promo_list s1 bbs of
          (bbs', s2) => ((bb with bb_instructions := insts) :: bbs', s2)
End

Definition m2v_transform_function_supply_def:
  m2v_transform_function_supply s fn =
    case m2v_rewrite_blocks_supply (m2v_promo_list fn) s fn.fn_blocks of
      (bbs, s1) => (fn with fn_blocks := bbs, s1)
End

(* Set of promoted alloca instruction IDs *)
Definition m2v_promoted_ids_def:
  m2v_promoted_ids fn =
    { inst.inst_id |
      inst |
      MEM inst (fn_insts fn) /\
      inst.inst_opcode = ALLOCA /\
      ?alloca_out. inst.inst_outputs = [alloca_out] /\
        m2v_can_promote_alloca
          (dfg_get_uses (dfg_build_function fn) alloca_out) }
End

(* A byte address falls in a promoted alloca's memory region.
   Only covers sz=32 entries: these are the actually-promoted allocas
   whose memory writes are replaced by variable assignments.
   sz≠32 entries are left unchanged, so their memory is tracked by
   the general memory agreement clause in m2v_inv_noix. *)
Definition in_promoted_region_def:
  in_promoted_region fn s (addr : num) <=>
    ?aid base.
      aid IN m2v_promoted_ids fn /\
      FLOOKUP s.vs_allocas aid = SOME (base, 32) /\
      base <= addr /\ addr < base + 32
End

(* Read a memory byte with zero-padding beyond allocated memory *)
Definition mem_byte_def:
  mem_byte (i : num) (s : venom_state) =
    if i < LENGTH s.vs_memory then EL i s.vs_memory else (0w : word8)
End

(* Predicate: all promoted allocas have size exactly 32.
 * Required because EVM MSTORE/MLOAD always accesses 32 bytes,
 * and RETURN promotion inserts a MSTORE that writes exactly 32 bytes.
 * In practice, Vyper allocas for single words are always 32 bytes.
 * Provable from a sound bp_ptrs_bounded analysis that tracks alloca pointers. *)
Definition m2v_promo_sizes_bounded_def:
  m2v_promo_sizes_bounded fn <=>
    !ao pvar sz. MEM (ao, pvar, sz) (m2v_promo_list fn) ==> sz = 32
End

(* Predicate: promoted RETURN instructions have literal size ≤ alloca size.
 * Required because the inserted MSTORE only restores 32 bytes (alloca size),
 * so the RETURN must read ≤ 32 bytes from the alloca region for the
 * simulation to produce identical return data.
 * Derivable from bp_ptrs_bounded when the RETURN size operand is a literal. *)
Definition m2v_return_size_bounded_def:
  m2v_return_size_bounded fn <=>
    !bb inst ao pvar sz.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = RETURN /\
      MEM (ao, pvar, sz) (m2v_promo_list fn) /\
      MEM (Var ao) inst.inst_operands ==>
      ?n. inst.inst_operands = [Var ao; Lit n] /\ w2n n <= sz
End

(* Predicate: fresh variables are undefined in a state *)
Definition m2v_fresh_undef_def:
  m2v_fresh_undef fn s <=>
    !v. v IN m2v_fresh_vars fn ==> lookup_var v s = NONE
End

(* Combined scan: compute (ctr, promo_list, fresh_set) in one FOLDL *)
Definition m2v_scan_step_def:
  m2v_scan_step dfg (ctr, promos, fresh) (i : instruction) =
    case i.inst_outputs of
      [alloca_out] =>
        let uses = dfg_get_uses dfg alloca_out in
        let size_val = case i.inst_operands of
                         Lit w :: _ => w2n w | _ => 0 in
        if m2v_can_promote_alloca uses then
          let var = m2v_fresh_var alloca_out ctr in
          (ctr + 1, (alloca_out, var, size_val) :: promos, var INSERT fresh)
        else (ctr, promos, fresh)
    | _ => (ctr, promos, fresh)
End
