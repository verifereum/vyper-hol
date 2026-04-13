(*
 * Memory Copy Elision — Definitions
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
 *
 * Eliminates redundant memory copies by tracking which memory
 * locations already contain the expected data.
 *
 * Framework: analysis_inst_simulates + df_analysis_pass_correct_sound.
 *
 * The Python tracks two things:
 *   1. Copy facts: maps dest MemoryLocation → copy_instruction
 *      (knowing what was copied where)
 *   2. Load facts: maps variable → (MemoryLocation, load_instruction)
 *      (knowing what was loaded from where)
 *
 * Three elision patterns:
 *   - Redundant copy: mcopy dst src N when dst already has same data
 *   - Copy forwarding: mcopy dst src N when src was itself copied from X
 *     → mcopy dst X N (skip intermediate buffer)
 *   - Load-store: store val ptr when val was loaded from same ptr
 *     → NOP (store is redundant)
 *
 * Operand comparisons use assign chain normalization (normalize_operand)
 * matching Python's dfg.are_equivalent / _traverse_assign_chain.
 *
 * We model the analysis as a forward dataflow over copy facts.
 *
 * TOP-LEVEL:
 *   copy_fact_lattice     — lattice tracking copy state (mem_loc keys)
 *   copy_elision_inst     — per-instruction transform
 *   copy_elision_function — function-level transform
 *)

Theory memoryCopyElisionDefs
Ancestors
  analysisSimDefs dfAnalyzeDefs dfgDefs passSharedDefs venomEffects
  memAliasDefs memLocDefs basePtrDefs

(* normalize_operand and operand_equiv are in dfgDefs *)

(* ===== Helpers ===== *)

(* A memory location is "fixed" when it has known offset + size.
   Python: MemoryLocation.is_fixed. Only fixed locations are tracked
   as lattice keys (Python: "if write_loc.is_fixed: self.copies[write_loc] = inst").
   ml_is_fixed is in passSharedDefs. *)

(* Compute mem_loc from offset + size operands using base pointer analysis.
   Shared helper for copy read/write locations. *)
Definition ce_memloc_from_ops_def:
  ce_memloc_from_ops bp ofst sz =
    bp_segment_from_ops bp
      <| iao_ofst := ofst; iao_size := SOME sz; iao_max_size := SOME sz |>
End

(* ===== Copy fact lattice ===== *)

(* A copy fact records the source operand and size for a memory region.
   If a location has a copy fact, we know what data it contains. *)
Datatype:
  copy_fact = <|
    cf_opcode : opcode;       (* original copy opcode *)
    cf_source : operand;      (* source operand *)
    cf_size   : operand       (* size operand *)
  |>
End

(* Maps destination MemoryLocation → copy fact.
   Matches Python: CopyMap = dict[MemoryLocation, IRInstruction]

   OPTION wrapping: copy fact analysis is a must-analysis (join =
   intersection). The identity for intersection is ⊤ (universal set),
   which can't be represented as a finite map. NONE serves as ⊤.
   SOME FEMPTY = ⊥ (no facts, annihilator for meet).

   This is needed because df_analyze uses FOLDL join bottom edge_vals:
   with bottom = NONE, FOLDL meet NONE [v1,v2] = meet(v1,v2).
   Without OPTION wrapping, FOLDL meet FEMPTY [v1,v2] = FEMPTY always
   (intersection with empty = empty), killing all cross-BB propagation. *)
Type copy_fact_lattice_raw = ``:(mem_loc, copy_fact) fmap``
Type copy_fact_lattice = ``:(mem_loc, copy_fact) fmap option``

(* Helper: two raw lattices agree on a key.
   Matches Python _copies_equivalent: compares opcode + source + size
   through assign chains via operand_equiv. *)
Definition cf_agree_def:
  cf_agree dfg (f1 : copy_fact_lattice_raw)
               (f2 : copy_fact_lattice_raw) k =
    case (FLOOKUP f1 k, FLOOKUP f2 k) of
      (SOME cf1, SOME cf2) =>
        cf1.cf_opcode = cf2.cf_opcode /\
        operand_equiv dfg cf1.cf_source cf2.cf_source /\
        operand_equiv dfg cf1.cf_size cf2.cf_size
    | _ => F
End

(* Raw join: intersection of copy facts (parameterized by DFG for
   assign chain comparison, matching Python _merge_copies). *)
Definition copy_fact_join_raw_def:
  copy_fact_join_raw dfg
    (f1 : copy_fact_lattice_raw) (f2 : copy_fact_lattice_raw) =
    DRESTRICT f1 { k | cf_agree dfg f1 f2 k }
End

(* OPTION-wrapped join: NONE = ⊤ (identity for meet).
   SOME FEMPTY = ⊥ (no facts, annihilator). *)
Definition copy_fact_join_def:
  copy_fact_join dfg
    (f1 : copy_fact_lattice) (f2 : copy_fact_lattice) =
    case (f1, f2) of
      (NONE, _) => f2
    | (_, NONE) => f1
    | (SOME m1, SOME m2) => SOME (copy_fact_join_raw dfg m1 m2)
End

(* Unwrap OPTION lattice for transform/transfer.
   NONE (⊤ / unreached) → no facts (FEMPTY). *)
Definition unwrap_copy_facts_def:
  unwrap_copy_facts (cfl_opt : copy_fact_lattice) =
    case cfl_opt of NONE => FEMPTY | SOME c => c
End

(* is_copy_opcode is in passSharedDefs *)

(* Context for copy elision analysis, carrying alias + DFG + base ptr info *)
Datatype:
  copy_elision_ctx = <|
    ce_aliases : alias_sets;
    ce_bp : bp_result;
    ce_dfg : dfg_analysis
  |>
End

(* Invalidate copy facts that may alias with the given write location.
   Python: _invalidate removes entries where either key (dest) or
   source (for mcopy only) may_alias the write location.
   If write_loc is not fixed, clear all copies (Python: copies.clear()). *)
Definition copy_fact_invalidate_def:
  copy_fact_invalidate (aliases : alias_sets) (bp : bp_result)
                       (cfl : copy_fact_lattice_raw) (write_loc : mem_loc) =
    if ~ml_is_fixed write_loc then FEMPTY  (* unknown loc: kill all *)
    else DRESTRICT cfl
      { k | (* Keep if dest doesn't alias the write *)
            ~ma_may_alias aliases k write_loc /\
            (* Source aliasing only matters for MCOPY: its source is in
               memory, so a memory write could clobber it.  Non-MCOPY
               copy opcodes (CALLDATACOPY, DLOADBYTES, CODECOPY,
               RETURNDATACOPY) read from a different address space, so
               a memory write cannot affect their source — keep entry. *)
            (case FLOOKUP cfl k of
               SOME cf =>
                 if cf.cf_opcode = MCOPY then
                   let src_loc = ce_memloc_from_ops bp cf.cf_source cf.cf_size in
                   ~ma_may_alias aliases src_loc write_loc
                 else T
             | NONE => T) }
End

(* For MCOPY, follow the source's existing copy fact to achieve transitive
   forwarding in one pass (matching Python's in-place mutation behavior).
   Non-MCOPY copy opcodes are "origin" instructions — recorded as-is.
   Lookup is by source read location (mem_loc key). *)
Definition copy_fact_resolve_def:
  copy_fact_resolve (bp : bp_result) dfg (cfl : copy_fact_lattice_raw)
                    inst_opcode src sz =
    if inst_opcode = MCOPY then
      let read_loc = ce_memloc_from_ops bp src sz in
      case FLOOKUP cfl read_loc of
        SOME src_cf =>
          (* Size match is guaranteed by MemoryLocation key equality —
             Python L215-216: "MemoryLocation includes size as part of
             its identity, and only fixed-size copies are tracked."
             No explicit size check needed. *)
          let norm_src =
            normalize_operand dfg [] src_cf.cf_source in
          (src_cf.cf_opcode, norm_src)
      | NONE => (inst_opcode, src)
    else (inst_opcode, src)
End

(* Check if an operand references any variable in a killed set *)
Definition operand_var_killed_def:
  operand_var_killed killed (Var v) = (v IN killed) /\
  operand_var_killed killed _ = F
End

(* Prune entries whose normalized source operand references a killed variable.
   Used in Case 4 of copy_fact_transfer: non-memory instructions may write
   variables that appear in lattice source operands. *)
Definition copy_fact_prune_vars_def:
  copy_fact_prune_vars dfg killed (cfl : copy_fact_lattice_raw) =
    DRESTRICT cfl
      (FDOM cfl DIFF
        {ml | ?cf. FLOOKUP cfl ml = SOME cf /\
              operand_var_killed killed
                (normalize_operand dfg [] cf.cf_source)})
End

(* Transfer: update copy facts after an instruction.
   Copy instructions compute write MemoryLocation, store only if fixed.
   Non-copy memory writes invalidate by alias; volatile clears all.
   Unwraps OPTION, applies raw transfer, wraps back.
   NONE (⊤) → treat as FEMPTY (entry has no known facts). *)
Definition copy_fact_transfer_def:
  copy_fact_transfer (ctx : copy_elision_ctx) inst
                     (cfl_opt : copy_fact_lattice) =
    let cfl = unwrap_copy_facts cfl_opt in
    SOME (
    if is_copy_opcode inst.inst_opcode then
      (* EVM operand order: [dst; src; sz] *)
      case inst.inst_operands of
        [dst; src; sz] =>
          (* Compute write location as MemoryLocation *)
          let write_loc = ce_memloc_from_ops ctx.ce_bp dst sz in
          (* Check if this MCOPY is redundant: dest already has same data.
             Python: _try_elide_redundant_copy → continue (skip invalidation).
             If redundant, state is unchanged — no invalidation needed. *)
          if inst.inst_opcode = MCOPY /\
             (case FLOOKUP cfl write_loc of
                SOME cf => cf.cf_opcode = MCOPY /\
                           operand_equiv ctx.ce_dfg
                             cf.cf_source src /\
                           operand_equiv ctx.ce_dfg
                             cf.cf_size sz
              | NONE => F)
          then cfl  (* redundant: skip entirely *)
          else
          (* Resolve transitive source before invalidation *)
          let (final_op, final_src) =
            copy_fact_resolve ctx.ce_bp ctx.ce_dfg
              cfl inst.inst_opcode src sz in
          (* Invalidate facts aliasing the write destination *)
          let cfl' = copy_fact_invalidate ctx.ce_aliases ctx.ce_bp
                       cfl write_loc in
          (* Only track if write location is fixed and source is not
             a Label.  Python's _traverse_assign_chain always returns
             an IRVariable, never an IRLabel; our normalize_operand
             is more permissive so we guard here. *)
          if ml_is_fixed write_loc ∧ (∀l. final_src ≠ Label l) ∧
             (final_op = MCOPY ⇒
                ml_is_fixed (ce_memloc_from_ops ctx.ce_bp final_src sz) ∧
                ¬ma_may_alias ctx.ce_aliases write_loc
                  (ce_memloc_from_ops ctx.ce_bp final_src sz))
          then
            cfl' |+ (write_loc, <| cf_opcode := final_op;
                                    cf_source := final_src;
                                    cf_size := sz |>)
          else cfl'
      (* Malformed copy operands: conservatively clear all facts.
         Python's get_write_location returns unfixed → copies.clear(). *)
      | _ => FEMPTY
    else if inst.inst_opcode = MSTORE then
      (* MSTORE writes to memory — alias-based invalidation *)
      let write_loc = bp_get_write_location ctx.ce_bp inst AddrSp_Memory in
      copy_fact_invalidate ctx.ce_aliases ctx.ce_bp cfl write_loc
    else if Eff_MEMORY IN write_effects inst.inst_opcode \/
            is_alloca_op inst.inst_opcode \/
            is_ext_call_op inst.inst_opcode then
      (* Volatile memory writer (CALL, CREATE, etc.) or ALLOCA/ext-call:
         clear all. Matches Python _volatile_memory → copies.clear(). *)
      FEMPTY
    else
      (* No memory effect: prune entries whose normalized source operand
         references a variable written by this instruction.
         In SSA this never triggers, but pruning makes transfer_sound
         provable without requiring an SSA precondition. *)
      let killed = set (inst_defs inst) in
      copy_fact_prune_vars ctx.ce_dfg killed cfl)
End

(* Edge transfer: identity *)
Definition copy_fact_edge_transfer_def:
  copy_fact_edge_transfer (ctx : copy_elision_ctx) src dst
    (cfl : copy_fact_lattice) = cfl
End

(* Top-level analysis.
   bottom = NONE (⊤, identity for meet). Unreached blocks get NONE.
   entry_val = SOME (entry_lbl, SOME FEMPTY): the entry block starts
   with no known facts (SOME FEMPTY), not ⊤. *)
Definition copy_fact_analyze_def:
  copy_fact_analyze ctx fn =
    let entry_val = OPTION_MAP (\lbl. (lbl, SOME FEMPTY))
                      (fn_entry_label fn) in
    df_analyze Forward NONE (copy_fact_join ctx.ce_dfg)
      copy_fact_transfer copy_fact_edge_transfer ctx entry_val fn
End

(* ===== Per-instruction transform ===== *)

(* Elide redundant copies or forward through intermediate buffers.
   Lookups use MemoryLocation keys computed from operands + base ptr.

   Python: _try_elide_redundant_copy — opcode + source + size match → NOP.
   Python: _try_elide_copy — source was copied → forward with resolved
           opcode/source, canonicalized via _traverse_assign_chain.
   Comparisons use operand_equiv (assign chain normalization). *)
Definition copy_elision_inst_def:
  copy_elision_inst bp dfg (cfl_opt : copy_fact_lattice) inst =
    let cfl = unwrap_copy_facts cfl_opt in
    let equiv = operand_equiv dfg in
    let norm = normalize_operand dfg [] in
    if inst.inst_opcode = INVOKE then inst
    else if inst.inst_opcode = MCOPY then
      case inst.inst_operands of
        [dst; src; sz] =>
          let write_loc = ce_memloc_from_ops bp dst sz in
          let read_loc = ce_memloc_from_ops bp src sz in
          (* 1. Redundant copy: dest already has same data.
             Matches Python _try_elide_redundant_copy +
             _copies_equivalent using operand_equiv. *)
          (case FLOOKUP cfl write_loc of
             SOME cf =>
               if cf.cf_opcode = MCOPY /\ equiv cf.cf_source src /\
                  equiv cf.cf_size sz
               then mk_nop_inst inst
               else
               (* 2. Copy forwarding: source was copied from somewhere.
                  Canonicalize source via _traverse_assign_chain.
                  Size match guaranteed by MemoryLocation key (Python L215).
                  Guard: only forward if stored opcode is a copy opcode.
                  The analysis invariant guarantees this, but the guard
                  makes inst_transform_structural provable unconditionally. *)
               (case FLOOKUP cfl read_loc of
                  SOME src_cf =>
                    if is_copy_opcode src_cf.cf_opcode then
                      inst with <| inst_opcode := src_cf.cf_opcode;
                                   inst_operands :=
                                     [dst; norm src_cf.cf_source; sz] |>
                    else inst
                | NONE => inst)
           | NONE =>
               (case FLOOKUP cfl read_loc of
                  SOME src_cf =>
                    if is_copy_opcode src_cf.cf_opcode then
                      inst with <| inst_opcode := src_cf.cf_opcode;
                                   inst_operands :=
                                     [dst; norm src_cf.cf_source; sz] |>
                    else inst
                | NONE => inst))
      | _ => inst
    else inst
End

(* ===== Use-count computation ===== *)

(* Count how many distinct instructions use a variable.
   Python: len(dfg.get_uses(load_inst.output)) — returns a SET of
   instructions, so each instruction counts once even if the variable
   appears in multiple operand slots. *)
Definition inst_uses_var_def:
  inst_uses_var v inst =
    EXISTS (\op. op = Var v) inst.inst_operands
End

Definition count_var_uses_def:
  count_var_uses v fn =
    SUM (MAP (\bb.
      LENGTH (FILTER (inst_uses_var v) bb.bb_instructions))
      fn.fn_blocks)
End

(* ===== Load-store elision (per-BB) ===== *)

(* Track loads within a block. Maps variable name → (MemoryLocation, opcode).
   When a store writes variable V back to the same MemoryLocation, and V was
   loaded from there within this block, NOP the store.
   Python: _try_elide_load_store in _process_bb. *)

(* Load opcodes that create load facts *)
Definition is_load_fact_opcode_def:
  is_load_fact_opcode MLOAD = T /\
  is_load_fact_opcode SLOAD = T /\
  is_load_fact_opcode TLOAD = T /\
  is_load_fact_opcode _ = F
End

(* Check load/store opcode compatibility (same address space).
   mload↔mstore, sload↔sstore, tload↔tstore *)
Definition load_store_compatible_def:
  load_store_compatible MLOAD MSTORE = T /\
  load_store_compatible SLOAD SSTORE = T /\
  load_store_compatible TLOAD TSTORE = T /\
  load_store_compatible _ _ = F
End

(* load_opcode_addr_space, store_opcode_addr_space are in passSharedDefs *)

(* Load facts include the MemoryLocation and load opcode *)
Datatype:
  load_fact = <|
    lf_memloc : mem_loc;
    lf_opcode : opcode
  |>
End

(* Invalidate load facts in a specific address space that may alias a write.
   Python: _invalidate uses may_alias, only on self.loads[eff].
   If write_loc is not fixed, clear all entries in that space.
   Entries in other address spaces are preserved. *)
Definition invalidate_loads_def:
  invalidate_loads (aliases : alias_sets) (lf : (string, load_fact) fmap)
                   (write_loc : mem_loc) (space : addr_space) =
    if ~ml_is_fixed write_loc then
      (* Unknown write: clear all loads in this space *)
      DRESTRICT lf
        { v | !lfact. FLOOKUP lf v = SOME lfact ==>
              load_opcode_addr_space lfact.lf_opcode <> space }
    else
      DRESTRICT lf
        { v | !lfact. FLOOKUP lf v = SOME lfact ==>
              load_opcode_addr_space lfact.lf_opcode <> space \/
              ~ma_may_alias aliases lfact.lf_memloc write_loc }
End

(* Process one instruction for load-store elision.
   Threads alias analysis + base pointer info for proper invalidation.

   Python _process_bb handles:
   1. Loads → record load fact
   2. Stores → try elide + alias-invalidate in store's space
   3. Copy opcodes → alias-invalidate MEMORY loads only
   4. Volatile memory → clear MEMORY loads only (not storage/transient)

   Elision: compares write_loc == load_loc (equality, not alias).
   Invalidation: uses may_alias, scoped to matching address space. *)
Definition load_store_step_def:
  load_store_step (aliases : alias_sets) (bp : bp_result)
                  (use_counts : string -> num)
                  (lf : (string, load_fact) fmap, inst) =
    (* 1. Record loads *)
    if is_load_fact_opcode inst.inst_opcode then
      (case (inst.inst_operands, inst.inst_outputs) of
         ([addr], [out]) =>
           let read_loc = bp_get_read_location bp inst
                            (load_opcode_addr_space inst.inst_opcode) in
           if ml_is_fixed read_loc then
             (lf |+ (out, <| lf_memloc := read_loc;
                              lf_opcode := inst.inst_opcode |>), inst)
           else (lf, inst)
       | _ => (lf, inst))
    (* 2. Stores: try elide + invalidate in store's address space *)
    else if is_store_opcode inst.inst_opcode then
      let store_space = store_opcode_addr_space inst.inst_opcode in
      let write_loc = bp_get_write_location bp inst store_space in
      (* Try elide: only for Var values *)
      let result =
        (case inst.inst_operands of
           [addr; Var val_name] =>
             (case FLOOKUP lf val_name of
                SOME lfact =>
                  if lfact.lf_memloc = write_loc /\
                     load_store_compatible lfact.lf_opcode inst.inst_opcode /\
                     use_counts val_name < 2
                  then mk_nop_inst inst
                  else inst
              | NONE => inst)
         | _ => inst) in
      (* Always invalidate, even for non-Var values.
         Python: _invalidate always runs regardless of value operand type. *)
      let lf' = invalidate_loads aliases lf write_loc store_space in
      (lf', result)
    (* 3. Copy opcodes: alias-invalidate MEMORY loads only *)
    else if is_copy_opcode inst.inst_opcode then
      let write_loc = bp_get_write_location bp inst AddrSp_Memory in
      let lf' = invalidate_loads aliases lf write_loc AddrSp_Memory in
      (lf', inst)
    (* 4. Volatile memory writers: clear MEMORY loads only.
       Python: _volatile_memory → self.loads[Effects.MEMORY].clear()
       Storage and transient load facts survive. *)
    else if Eff_MEMORY IN write_effects inst.inst_opcode then
      let lf' = DRESTRICT lf
        { v | !lfact. FLOOKUP lf v = SOME lfact ==>
              load_opcode_addr_space lfact.lf_opcode <> AddrSp_Memory } in
      (lf', inst)
    else (lf, inst)
End

Definition load_store_elim_block_def:
  load_store_elim_block (aliases : alias_sets) (bp : bp_result)
                        (uc : string -> num) bb =
    let (_, new_insts) =
      FOLDL (\(lf, acc) inst.
        let (lf', inst') = load_store_step aliases bp uc (lf, inst) in
        (lf', acc ++ [inst']))
      (FEMPTY, []) bb.bb_instructions in
    bb with bb_instructions := new_insts
End

(* ===== Function-level transform ===== *)

Definition copy_elision_function_def:
  copy_elision_function fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let bp = bp_analyze cfg fn in
    let aliases = memory_alias_analyze bp fn in
    let ctx = <| ce_aliases := aliases; ce_bp := bp;
                 ce_dfg := dfg |> in
    let result = copy_fact_analyze ctx fn in
    let fn1 = analysis_function_transform NONE result
                (\v inst. [copy_elision_inst bp dfg v inst]) fn in
    (* Run load-store elision as a second pass (per-BB, no cross-BB state).
       Use counts from fn1 (post-copy-elision): phase 1 may NOP copies
       that reference a loaded variable, reducing its use count and
       enabling load-store elision that Python would also perform. *)
    let uc = (\v. count_var_uses v fn1) in
    clear_nops_function
      (function_map_transform (load_store_elim_block aliases bp uc) fn1)
End
