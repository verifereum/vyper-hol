(*
 * Load Elimination — Definitions
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
 *
 * Eliminates redundant loads by tracking available values at each
 * memory location via a set-valued lattice. At join points, value
 * sets are unioned (not intersected). When a load finds:
 *   - Single value → replace with ASSIGN
 *   - Multiple values → insert PHI at join block (0:N prepend),
 *     replace load with ASSIGN from PHI output (1:1 transform)
 *
 * Uses the analysis_function_transform_prepend framework:
 *   0:N prepend: PHI instructions at join blocks (fresh vars, no-op)
 *   1:N per-inst: load→ASSIGN, redundant store→NOP
 *
 * TOP-LEVEL:
 *   load_config, load_lattice, load_transfer, load_analyze
 *   load_elim_inst — per-instruction 1:1 transform
 *   load_phi_prepend — 0:N PHI insertion at join blocks
 *   load_elim_function — runs 5 effect types
 *)

Theory loadElimDefs
Ancestors
  analysisSimDefs dfAnalyzeDefs dfgDefs passSharedDefs venomEffects
  memAliasDefs memLocDefs cfgDefs

(* ===== Analysis configuration ===== *)

(* Store opcode is NONE for read-only address spaces (dload, calldataload).
   Python uses store_opcode=None for these; read-only spaces never have
   their lattice cleared by writes. *)
Datatype:
  load_config = <| lc_load : opcode; lc_store : opcode option |>
End

Definition memory_config_def:
  memory_config = <| lc_load := MLOAD; lc_store := SOME MSTORE |>
End

Definition storage_config_def:
  storage_config = <| lc_load := SLOAD; lc_store := SOME SSTORE |>
End

Definition transient_config_def:
  transient_config = <| lc_load := TLOAD; lc_store := SOME TSTORE |>
End

Definition dload_config_def:
  dload_config = <| lc_load := DLOAD; lc_store := NONE |>
End

Definition calldataload_config_def:
  calldataload_config = <| lc_load := CALLDATALOAD; lc_store := NONE |>
End

Definition config_addr_space_def:
  config_addr_space cfg =
    if cfg.lc_load = MLOAD then AddrSp_Memory
    else if cfg.lc_load = SLOAD then AddrSp_Storage
    else if cfg.lc_load = TLOAD then AddrSp_Transient
    else if cfg.lc_load = CALLDATALOAD then AddrSp_Calldata
    else if cfg.lc_load = DLOAD then AddrSp_Data
    else AddrSp_Memory
End

(* ===== Lattice key: operand or MemoryLocation ===== *)

(* Python uses IROperand | MemoryLocation as lattice keys.
   When base pointer analysis resolves to a fixed location (known
   offset + size), MemoryLocation is used — enabling cross-variable
   elimination. Otherwise, normalized operand is used as fallback. *)
Datatype:
  load_key = LK_Op operand | LK_Loc mem_loc
End

(* ml_is_fixed is now in passSharedDefs *)

(* Which address spaces try MemoryLocation keys for reads?
   Python: MEMORY, TRANSIENT, STORAGE, CALLDATA *)
Definition use_memloc_for_read_def:
  use_memloc_for_read AddrSp_Memory = T /\
  use_memloc_for_read AddrSp_Storage = T /\
  use_memloc_for_read AddrSp_Transient = T /\
  use_memloc_for_read AddrSp_Calldata = T /\
  use_memloc_for_read _ = F
End

(* Which address spaces try MemoryLocation keys for writes?
   Python: MEMORY, TRANSIENT, STORAGE *)
Definition use_memloc_for_write_def:
  use_memloc_for_write AddrSp_Memory = T /\
  use_memloc_for_write AddrSp_Storage = T /\
  use_memloc_for_write AddrSp_Transient = T /\
  use_memloc_for_write _ = F
End

(* ===== Set-valued lattice ===== *)

(* Maps load_key → list of possible value operands.
   Python: Lattice = dict[IROperand | MemoryLocation, OrderedSet[IROperand]].

   OPTION wrapping: load elimination is a must-analysis (join =
   intersection of domains). The identity for intersection is ⊤
   (universal set), which can't be represented as a finite map.
   NONE serves as ⊤. SOME FEMPTY = ⊥ (no facts).

   This is needed because df_analyze uses FOLDL join bottom edge_vals:
   with bottom = NONE, FOLDL meet NONE [v1,v2] = meet(v1,v2).
   Without OPTION wrapping, FOLDL meet FEMPTY [v1,v2] = FEMPTY always
   (intersection with empty = empty), killing all cross-BB propagation. *)
Type load_lattice_raw = ``:(load_key, operand list) fmap``
Type load_lattice = ``:(load_key, operand list) fmap option``

Definition operand_list_union_def:
  operand_list_union l1 l2 =
    l1 ++ FILTER (\x. ~MEM x l1) l2
End

(* Raw join: union values for keys in BOTH lattices.
   Python: common_keys; res[k] = tmp[k] | other[k] *)
Definition load_join_raw_def:
  load_join_raw (l1 : load_lattice_raw) (l2 : load_lattice_raw) =
    FUN_FMAP
      (\k. case (FLOOKUP l1 k, FLOOKUP l2 k) of
             (SOME vs1, SOME vs2) => operand_list_union vs1 vs2
           | _ => [])
      (FDOM l1 INTER FDOM l2)
End

(* OPTION-wrapped join: NONE = ⊤ (identity for meet).
   SOME FEMPTY = ⊥ (no facts, annihilator). *)
Definition load_join_def:
  load_join (l1 : load_lattice) (l2 : load_lattice) =
    case (l1, l2) of
      (NONE, _) => l2
    | (_, NONE) => l1
    | (SOME m1, SOME m2) => SOME (load_join_raw m1 m2)
End

(* Unwrap OPTION lattice for transform/transfer.
   NONE (⊤ / unreached) → no facts (FEMPTY). *)
Definition unwrap_load_lattice_def:
  unwrap_load_lattice (ll_opt : load_lattice) =
    case ll_opt of NONE => FEMPTY | SOME l => l
End

(* normalize_operand and operand_equiv are in dfgDefs *)

(* addr_space_word_scale is in passSharedDefs *)

(* Convert an operand to a MemoryLocation using base pointer analysis.
   Python: get_memloc uses InstAccessOps(ofst=op, size=IRLiteral(word_scale))
   to produce a MemoryLocation with proper size. *)
Definition operand_to_memloc_def:
  operand_to_memloc (bp : bp_result) (addr_sp : addr_space) (Var v) =
    bp_segment_from_ops bp
      <| iao_ofst := Var v;
         iao_size := SOME (Lit (n2w (addr_space_word_scale addr_sp)));
         iao_max_size := SOME (Lit (n2w (addr_space_word_scale addr_sp))) |> /\
  operand_to_memloc bp addr_sp (Lit w) =
    <| ml_offset := SOME (w2n w);
       ml_size := SOME (addr_space_word_scale addr_sp);
       ml_alloca := NONE;
       ml_volatile := F |> /\
  operand_to_memloc bp addr_sp _ = ml_undefined
End

(* Convert load_key to mem_loc for alias checking.
   Matches Python get_memloc: MemoryLocation keys are already memlocs;
   operand keys are converted via base pointer analysis. *)
Definition load_key_to_memloc_def:
  load_key_to_memloc bp addr_sp (LK_Loc loc) = loc /\
  load_key_to_memloc bp addr_sp (LK_Op op) = operand_to_memloc bp addr_sp op
End

Definition load_invalidate_def:
  load_invalidate (aliases : alias_sets) (bp : bp_result)
                  (addr_sp : addr_space)
                  (ll : load_lattice_raw) write_key =
    let write_loc = load_key_to_memloc bp addr_sp write_key in
    if write_loc = ml_undefined then FEMPTY
    else DRESTRICT ll
      { k | let kl = load_key_to_memloc bp addr_sp k in
            kl <> ml_undefined /\ ~ma_may_alias aliases kl write_loc }
End

(* ===== Context ===== *)

Datatype:
  load_context = <|
    lctx_config : load_config;
    lctx_aliases : alias_sets;
    lctx_bp : bp_result;
    lctx_addr_space : addr_space;
    lctx_dfg : dfg_analysis
  |>
End

(* ===== Key computation ===== *)

(* Compute lattice key for a load instruction.
   Matches Python get_read: try MemoryLocation if address space supports
   it and result is fixed; otherwise use normalized operand. *)
Definition load_get_read_key_def:
  load_get_read_key (bp : bp_result) addr_sp norm inst =
    if use_memloc_for_read addr_sp then
      let loc = bp_get_read_location bp inst addr_sp in
      if ml_is_fixed loc then LK_Loc loc
      else LK_Op (norm (HD inst.inst_operands))
    else LK_Op (norm (HD inst.inst_operands))
End

(* Compute lattice key for a store instruction.
   Matches Python get_write: try MemoryLocation for MEMORY/STORAGE/TRANSIENT;
   otherwise use normalized operand (address = first operand in EVM order,
   Python operands[1] after reversal). *)
Definition load_get_write_key_def:
  load_get_write_key (bp : bp_result) addr_sp norm inst =
    if use_memloc_for_write addr_sp then
      let loc = bp_get_write_location bp inst addr_sp in
      if ml_is_fixed loc then LK_Loc loc
      else LK_Op (norm (HD inst.inst_operands))
    else LK_Op (norm (HD inst.inst_operands))
End

(* ===== Transfer ===== *)

(* Transfer function.
   Read-only spaces (lc_store = NONE) skip store handling and
   barrier checks entirely — matching Python's `isinstance(eff, Effects)`
   guard which is False for string effects "dload"/"calldataload". *)
(* Transfer: unwraps OPTION, applies raw transfer, wraps back.
   NONE (⊤) → treat as FEMPTY (entry has no known facts). *)
Definition load_transfer_def:
  load_transfer (ctx : load_context) inst (ll_opt : load_lattice) =
    let ll = unwrap_load_lattice ll_opt in
    let cfg = ctx.lctx_config in
    let op = inst.inst_opcode in
    let norm = normalize_operand ctx.lctx_dfg {} in
    let bp = ctx.lctx_bp in
    let addr_sp = ctx.lctx_addr_space in
    SOME (
    if op = cfg.lc_load then
      (case (inst.inst_operands, inst.inst_outputs) of
         ([addr], [out]) =>
           let key = load_get_read_key bp addr_sp norm inst in
           ll |+ (key, [Var out])
       | _ => ll)
    else
      (case cfg.lc_store of
         SOME st =>
           if op = st then
             (case inst.inst_operands of
                [addr; val_op] =>
                  let key = load_get_write_key bp addr_sp norm inst in
                  let ll' = load_invalidate ctx.lctx_aliases bp addr_sp ll key in
                  (* Store RAW value, not normalized — matching Python.
                     Normalization happens at comparison time in transform. *)
                  ll' |+ (key, [val_op])
              | _ => FEMPTY)
           else
             let space_eff = case ctx.lctx_addr_space of
                               AddrSp_Memory => Eff_MEMORY
                             | AddrSp_Storage => Eff_STORAGE
                             | AddrSp_Transient => Eff_TRANSIENT
                             | _ => Eff_MEMORY in  (* unreachable: dload/calldata have lc_store=NONE *)
             if space_eff IN write_effects op then FEMPTY
             else ll
       | NONE => ll))  (* read-only: no stores, no barrier *)
End

Definition load_edge_transfer_def:
  load_edge_transfer (ctx : load_context) src dst
                     (ll : load_lattice) = ll
End

(* Top-level analysis.
   bottom = NONE (⊤, identity for meet). Unreached blocks get NONE.
   entry_val = SOME (entry_lbl, SOME FEMPTY): the entry block starts
   with no known facts (SOME FEMPTY), not ⊤. *)
Definition load_analyze_def:
  load_analyze ctx fn =
    let entry_val = OPTION_MAP (\lbl. (lbl, SOME FEMPTY))
                      (fn_entry_label fn) in
    df_analyze Forward NONE load_join load_transfer
      load_edge_transfer ctx entry_val fn
End

(* ===== PHI action computation ===== *)

(* Walk up single-predecessor chain to find nearest join point.
   Python: while len(preds) == 1: bb = preds.first()
   Uses visited set for termination: each step adds current label,
   CARD(all_labels DIFF visited) strictly decreases. *)
Definition find_join_block_def:
  find_join_block ir_cfg visited lbl =
    if lbl IN visited then lbl
    else case cfg_preds_of ir_cfg lbl of
           [single_pred] =>
             find_join_block ir_cfg (lbl INSERT visited) single_pred
         | _ => lbl
Termination
  WF_REL_TAC `measure (\(cfg, visited, lbl).
    CARD (FDOM cfg.cfg_preds DIFF visited))`
  >> rw[]
  >> irule pred_setTheory.CARD_PSUBSET >> conj_tac
  >- simp[pred_setTheory.FINITE_DIFF, finite_mapTheory.FDOM_FINITE]
  >> simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
          pred_setTheory.EXTENSION]
  >> qexists_tac `lbl`
  >> fs[cfg_preds_of_def, fmap_lookup_list_def, AllCaseEqs(),
        finite_mapTheory.FLOOKUP_DEF]
End

(* Extract single variable from lattice value at a key.
   Returns SOME var_name if exactly [Var v], else NONE. *)
Definition lattice_single_var_def:
  lattice_single_var (ll_opt : load_lattice) (key : load_key) =
    let ll = unwrap_load_lattice ll_opt in
    case FLOOKUP ll key of
      SOME [Var v] => SOME v
    | _ => NONE
End

(* A PHI to be inserted: maps (load_inst_id, phi_output_var) at join_block *)
Datatype:
  phi_action = <|
    pa_join_lbl  : string;       (* block to prepend PHI to *)
    pa_phi_id    : num;          (* PHI instruction ID *)
    pa_phi_out   : string;       (* PHI output variable name *)
    pa_phi_ops   : operand list; (* PHI operands [Label, Var, ...] *)
    pa_load_id   : num;          (* load instruction to replace *)
    pa_load_lbl  : string        (* block containing the load *)
  |>
End

(* Build PHI operand list: [Label pred1, Var val1, Label pred2, Var val2, ...]
   from list of (pred_label, var_name) pairs. *)
Definition mk_phi_ops_from_pairs_def:
  mk_phi_ops_from_pairs [] = [] /\
  mk_phi_ops_from_pairs ((lbl, var) :: rest) =
    Label lbl :: Var var :: mk_phi_ops_from_pairs rest
End

(* Fresh PHI output variable name derived from load instruction ID *)
Definition fresh_phi_var_def:
  fresh_phi_var (load_id : num) = STRCAT "$le_phi_" (toString load_id)
End

(* Fresh PHI instruction ID. Must be distinct from all existing IDs.
   Python uses self.updater.add_before which generates a truly fresh ID.
   We use max_inst_id + load_id + 1 to guarantee uniqueness:
   max_inst_id is the largest ID in the function, so adding any positive
   offset ensures no collision. *)
Definition fresh_phi_id_def:
  fresh_phi_id (max_id : num) (load_id : num) = max_id + load_id + 1
End

(* Compute PHI action for one multi-value load instruction.
   Returns NONE if any predecessor lacks a single variable value
   (matching Python's early returns in _handle_load). *)
Definition compute_phi_action_def:
  compute_phi_action max_id ir_cfg (result : load_lattice df_state)
                     (key : load_key) bb_lbl inst =
    let join_lbl = find_join_block ir_cfg {} bb_lbl in
    let preds = cfg_preds_of ir_cfg join_lbl in
    (* For each predecessor, get its exit lattice single-var value *)
    let pred_results = MAP (\p.
      (p, lattice_single_var (df_boundary NONE result p) key))
      preds in
    (* All predecessors must provide a single variable *)
    if EVERY (\pv. IS_SOME (SND pv)) pred_results
    then
      let phi_out = fresh_phi_var inst.inst_id in
      let phi_ops = mk_phi_ops_from_pairs
        (MAP (\pv. (FST pv, THE (SND pv))) pred_results) in
      SOME <| pa_join_lbl := join_lbl;
              pa_phi_id := fresh_phi_id max_id inst.inst_id;
              pa_phi_out := phi_out;
              pa_phi_ops := phi_ops;
              pa_load_id := inst.inst_id;
              pa_load_lbl := bb_lbl |>
    else NONE
End

(* Collect all PHI actions for multi-value loads in the function. *)
Definition collect_phi_actions_def:
  collect_phi_actions max_id ctx ir_cfg (result : load_lattice df_state) fn =
    let norm = normalize_operand ctx.lctx_dfg {} in
    let bp = ctx.lctx_bp in
    let addr_sp = ctx.lctx_addr_space in
    FLAT (MAP (\bb.
      FLAT (MAPi (\idx inst.
        if inst.inst_opcode = ctx.lctx_config.lc_load then
          (case (inst.inst_operands, inst.inst_outputs) of
             ([addr], [_]) =>
               let key = load_get_read_key bp addr_sp norm inst in
               (case FLOOKUP (unwrap_load_lattice
                               (df_at NONE result bb.bb_label idx))
                             key of
                  SOME vs =>
                    if LENGTH vs > 1 then
                      (case compute_phi_action max_id ir_cfg result
                              key bb.bb_label inst of
                         SOME pa => [pa]
                       | NONE => [])
                    else []
                | NONE => [])
           | _ => [])
        else [])
       bb.bb_instructions))
      fn.fn_blocks)
End

(* ===== 0:N Prepend: PHI insertion ===== *)

(* Build PHI instructions for a block from a list of phi_actions.
   Only actions targeting this block produce instructions. *)
Definition phis_for_block_def:
  phis_for_block (actions : phi_action list) lbl =
    MAP (\pa.
      <| inst_id := pa.pa_phi_id;
         inst_opcode := PHI;
         inst_operands := pa.pa_phi_ops;
         inst_outputs := [pa.pa_phi_out] |>)
    (FILTER (\pa. pa.pa_join_lbl = lbl) actions)
End

(* Prepend function for the framework *)
Definition load_phi_prepend_def:
  load_phi_prepend (actions : phi_action list) lbl =
    phis_for_block actions lbl
End

(* ===== 1:1 Per-instruction transform ===== *)

(* Build a lookup from load_id → phi_output_var for fast access *)
Definition phi_action_lookup_def:
  phi_action_lookup (actions : phi_action list) (inst_id : num) =
    case FILTER (\pa. pa.pa_load_id = inst_id) actions of
      pa :: _ => SOME pa.pa_phi_out
    | [] => NONE
End

(* Per-instruction transform:
   - Load with single value → ASSIGN from value
   - Load with multi value + PHI action → ASSIGN from PHI output
   - Redundant store (all known values match) → NOP
   - Everything else → unchanged *)
Definition load_elim_inst_def:
  load_elim_inst (ctx : load_context) (actions : phi_action list)
                 (ll_opt : load_lattice) inst =
    let ll = unwrap_load_lattice ll_opt in
    let cfg = ctx.lctx_config in
    let norm = normalize_operand ctx.lctx_dfg {} in
    let bp = ctx.lctx_bp in
    let addr_sp = ctx.lctx_addr_space in
    if inst.inst_opcode = INVOKE then inst
    else if inst.inst_opcode = cfg.lc_load then
      (case (inst.inst_operands, inst.inst_outputs) of
         ([addr], [out]) =>
           let key = load_get_read_key bp addr_sp norm inst in
           (case FLOOKUP ll key of
              SOME [v] => mk_assign_inst inst v
            | SOME vs =>
                if LENGTH vs > 1 then
                  (case phi_action_lookup actions inst.inst_id of
                     SOME phi_out => mk_assign_inst inst (Var phi_out)
                   | NONE => inst)
                else inst
            | NONE => inst)
       | _ => inst)
    else
      (case cfg.lc_store of
         SOME st =>
           if inst.inst_opcode = st then
             (case inst.inst_operands of
                [addr; val_op] =>
                  let key = load_get_write_key bp addr_sp norm inst in
                  (* Python's dfg.are_equivalent only normalizes when BOTH
                     operands are IRVariable. Match that behavior. *)
                  let are_equiv = \v1 v2.
                    case (v1, v2) of
                      (Var _, Var _) => norm v1 = norm v2
                    | _ => v1 = v2 in
                  (case FLOOKUP ll key of
                     SOME vs =>
                       if vs <> [] /\
                          EVERY (\v. are_equiv v val_op) vs
                       then mk_nop_inst inst
                       else inst
                   | NONE => inst)
              | _ => inst)
           else inst
       | NONE => inst)
End

(* ===== Function-level transform ===== *)

(* Maximum instruction ID in a function, for generating fresh IDs *)
Definition fn_max_inst_id_def:
  fn_max_inst_id fn =
    FOLDL MAX 0
      (MAP (\inst. inst.inst_id)
        (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)))
End

Definition mk_load_context_def:
  mk_load_context bp_result aliases dfg cfg =
    <| lctx_config := cfg;
       lctx_aliases := aliases;
       lctx_bp := bp_result;
       lctx_addr_space := config_addr_space cfg;
       lctx_dfg := dfg |>
End

(* Run one effect type: analyze, compute PHIs, apply 0:N + 1:1 transform *)
Definition load_elim_one_def:
  load_elim_one ctx ir_cfg fn =
    let result = load_analyze ctx fn in
    let max_id = fn_max_inst_id fn in
    let actions = collect_phi_actions max_id ctx ir_cfg result fn in
    let prepend = load_phi_prepend actions in
    let f = \ll inst.
      [load_elim_inst ctx actions ll inst] in
    analysis_function_transform_prepend NONE result prepend f fn
End

(* Fresh variables introduced by PHI insertion for a given set of actions *)
Definition load_elim_fresh_vars_def:
  load_elim_fresh_vars (actions : phi_action list) =
    set (MAP (\pa. pa.pa_phi_out) actions)
End

(* Fresh variables from a single load_elim_one round *)
Definition load_elim_one_fresh_def:
  load_elim_one_fresh ctx ir_cfg fn =
    let result = load_analyze ctx fn in
    let max_id = fn_max_inst_id fn in
    load_elim_fresh_vars (collect_phi_actions max_id ctx ir_cfg result fn)
End

(* Run all five effect types.
   Python computes LoadAnalysis once then runs 5 _run transforms.
   Python's DFG is updated in-place by InstUpdater after each round,
   so normalize_operand in rounds 2–5 sees ASSIGN chains from earlier
   rounds. We recompute the DFG per round to match this behavior.
   Each round re-analyzes because PHI insertion shifts instruction
   indices (our lattice is keyed by (label, index), not object identity).
   Re-analysis is sound because PHIs/ASSIGNs/NOPs from other rounds
   have no memory effects and don't match the current round's opcodes. *)
Definition load_elim_function_def:
  load_elim_function ir_ctx fn =
    let ir_cfg = cfg_analyze fn in
    let bp = bp_analyze ir_cfg fn in
    let mem_aliases = memory_alias_analyze bp fn in
    let sto_aliases = storage_alias_analyze bp fn in
    let trs_aliases = transient_alias_analyze bp fn in
    let fn1 = load_elim_one
                (mk_load_context bp mem_aliases
                   (dfg_build_function fn) memory_config)
                ir_cfg fn in
    let fn2 = load_elim_one
                (mk_load_context bp trs_aliases
                   (dfg_build_function fn1) transient_config)
                ir_cfg fn1 in
    let fn3 = load_elim_one
                (mk_load_context bp sto_aliases
                   (dfg_build_function fn2) storage_config)
                ir_cfg fn2 in
    let fn4 = load_elim_one
                (mk_load_context bp mem_aliases
                   (dfg_build_function fn3) dload_config)
                ir_cfg fn3 in
    clear_nops_function
      (load_elim_one
        (mk_load_context bp mem_aliases
           (dfg_build_function fn4) calldataload_config)
        ir_cfg fn4)
End
