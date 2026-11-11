(*
 * Dead Store Elimination — Definitions
 *
 * Ports vyper/venom/passes/dead_store_elimination.py to HOL4.
 *
 * Eliminates memory/storage/transient stores that are dead: no
 * subsequent read before the location is overwritten or the
 * function terminates.
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Framework: analysis_inst_simulates + custom lifting.
 * Uses memory SSA analysis (memSSADefs) to identify dead stores.
 *
 * The Python checks:
 *   1. Location is not volatile
 *   2. Location is fixed (known offset and size)
 *   3. Instruction output is not used
 *   4. No non-related effects
 *   5. Memory def is not live (no read before clobber)
 *
 * We model this as: given a set of dead store instruction IDs
 * (computed by the analysis), NOP those instructions.
 *
 * TOP-LEVEL:
 *   is_dead_store         — predicate for dead store identification
 *   dse_inst              — per-instruction transform
 *   dse_function          — function-level transform
 *)

Theory deadStoreElimDefs
Ancestors
   passTransform passSharedDefs venomEffects memSSADefs
  memAliasDefs memLocDefs basePtrDefs cfgDefs While

(* is_store_opcode (in passSharedDefs) covers MSTORE/SSTORE/TSTORE.
   DSE operates on all non-terminating memory definitions identified by
   memSSA.  Terminators must be excluded because dse_inst replaces eligible
   instructions with NOP. *)
Definition is_memory_def_opcode_def:
  is_memory_def_opcode (space : addr_space) op <=>
    ~is_terminator op /\
    (case space of
       AddrSp_Memory => Eff_MEMORY IN write_effects op
     | AddrSp_Storage => Eff_STORAGE IN write_effects op
     | AddrSp_Transient => Eff_TRANSIENT IN write_effects op
     | _ => F)
End

(* ===== Memory store liveness ===== *)

(* Check if an instruction reads a location that may alias the query.
   Uses the base pointer analysis to compute read locations.
   No fixedness check on read_loc: unfixed locations conservatively
   may-alias everything, matching Python's may_overlap behavior
   for unknown offsets (e.g., INVOKE reads). *)
Definition dse_inst_reads_alias_def:
  dse_inst_reads_alias (aliases : alias_sets) (bp : bp_result)
                       (space : addr_space) store_loc inst =
    let read_loc = bp_get_read_location bp inst space in
    ma_may_alias aliases read_loc store_loc
End

(* Check if an instruction completely clobbers the query location.
   Python: write_loc.completely_contains(query_loc). *)
Definition dse_inst_clobbers_def:
  dse_inst_clobbers (bp : bp_result) (space : addr_space)
                    store_loc inst =
    let write_loc = bp_get_write_location bp inst space in
    ml_is_fixed write_loc /\ completely_contains write_loc store_loc
End

(* A store is "live" if some reachable read may alias its write location
   without an intervening complete clobber. This models Python's
   _is_memory_def_live: a CFG walk from the store checking for reads
   before clobbers.

   Semantic property (used as precondition, established by memSSA):
   - Starting from the instruction after the store in its block,
     and continuing through all reachable blocks via CFG successors,
   - If any instruction reads a location that may_alias the store's
     write location, the store is live.
   - If an instruction completely_contains-clobbers the store's location,
     that path is dead (no further search needed on that path).

   We state this as a negated existential for the precondition. *)
(* A block contains no complete clobber of store_loc *)
Definition block_no_full_clobber_def:
  block_no_full_clobber bp space store_loc fn lbl <=>
    !bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl ==>
         EVERY (\inst. ~dse_inst_clobbers bp space store_loc inst)
               bb.bb_instructions
End

(* A block has a read aliasing store_loc before any clobber *)
Definition block_has_unclobbered_read_def:
  block_has_unclobbered_read (aliases : alias_sets) bp space
                             store_loc fn lbl <=>
    ?bb j.
      MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
      j < LENGTH bb.bb_instructions /\
      (* No clobber before position j *)
      (!k. k < j ==>
           ~dse_inst_clobbers bp space store_loc
             (EL k bb.bb_instructions)) /\
      dse_inst_reads_alias aliases bp space store_loc
        (EL j bb.bb_instructions)
End

(* A store is "live" if some reachable read may alias its write location
   without an intervening complete clobber. Models Python's
   _is_memory_def_live: walks CFG from the store, tracking whether the
   location has been completely clobbered.

   The path consists of:
   1. Remaining instructions in the store's block (after store)
   2. Any block reachable through clobber-free intermediate blocks

   Intermediate blocks: no complete clobber anywhere in the block.
   Final block: read before any clobber (partial block check). *)
Definition dse_mem_def_live_def:
  dse_mem_def_live (cfg : cfg_analysis) (aliases : alias_sets)
                   (bp : bp_result) store_loc (space : addr_space)
                   fn bb inst_idx <=>
    (* Case 1: read in same block after store, before any clobber *)
    (?j. j > inst_idx /\
         j < LENGTH bb.bb_instructions /\
         (!k. inst_idx < k /\ k < j ==>
              ~dse_inst_clobbers bp space store_loc
                (EL k bb.bb_instructions)) /\
         dse_inst_reads_alias aliases bp space store_loc
           (EL j bb.bb_instructions)) \/
    (* Case 2: read in a successor block reachable through
       clobber-free blocks *)
    (?succ_lbl target_lbl.
       (* No clobber in rest of this block *)
       (!k. inst_idx < k /\ k < LENGTH bb.bb_instructions ==>
            ~dse_inst_clobbers bp space store_loc
              (EL k bb.bb_instructions)) /\
       (* succ_lbl is a direct successor *)
       MEM succ_lbl (cfg_succs_of cfg bb.bb_label) /\
       (* target_lbl reachable from succ_lbl through clobber-free blocks *)
       RTC (\a b. MEM b (cfg_succs_of cfg a) /\
                  block_no_full_clobber bp space store_loc fn a)
         succ_lbl target_lbl /\
       (* target block has a read before any clobber *)
       block_has_unclobbered_read aliases bp space store_loc fn
         target_lbl)
End

(* ===== Dead store precondition ===== *)

(* Instruction outputs are unused: no other instruction references them *)
Definition outputs_unused_def:
  outputs_unused inst fn <=>
    EVERY (\out.
      !bb' i'. MEM bb' fn.fn_blocks /\
               MEM i' bb'.bb_instructions /\
               i'.inst_id <> inst.inst_id ==>
               ~MEM (Var out) i'.inst_operands)
    inst.inst_outputs
End

(* Instruction's effects are confined to the given address space.
   Storage/Transient only allow their space. *)
Definition effects_in_space_def:
  effects_in_space (space : addr_space) inst <=>
    let space_eff = case space of
                      AddrSp_Memory => Eff_MEMORY
                    | AddrSp_Storage => Eff_STORAGE
                    | AddrSp_Transient => Eff_TRANSIENT
                    | AddrSp_Calldata => Eff_MEMORY
                    | AddrSp_Code => Eff_MEMORY
                    | AddrSp_Returndata => Eff_MEMORY in
    (write_effects inst.inst_opcode UNION read_effects inst.inst_opcode)
      SUBSET {space_eff}
End

(* Precondition: dead_ids only contains IDs of store instructions in fn
   whose stored values are provably dead. Matches Python's _is_dead_store.

   The inst.inst_outputs = [] condition restricts dead stores to
   instructions that have no output variables (MSTORE, SSTORE, TSTORE).
   This is necessary because mk_nop_inst removes the instruction's
   outputs, and dse_equiv checks ALL variables including unused ones.
   If a dead store had non-empty outputs (e.g., DLOAD which writes
   to memory AND produces an output variable), NOP'ing it would
   change the output variable's value, violating dse_equiv.

   In the Python DSE, DLOAD with unused outputs CAN be eliminated
   (Python doesn't check variable mappings, only EVM-observable
   effects). But in HOL4, dse_equiv checks !v. lookup_var v s1 =
   lookup_var v s2, so we must require empty outputs.

   This is the tightest sufficient fix: it precisely matches the
   set of instructions DSE eliminates in practice (actual stores)
   while being formally correct for the dse_equiv relation.

   Zero-size writes are excluded: a zero-size location never aliases a
   read, but the Venom semantics still expands memory for it
   (write_memory_with_expansion), which MEMTOP observes. *)
Definition all_dead_stores_def:
  all_dead_stores dead_ids cfg aliases bp (space : addr_space) fn <=>
    !id. id IN dead_ids ==>
      ?bb inst inst_idx.
        MEM bb fn.fn_blocks /\
        inst_idx < LENGTH bb.bb_instructions /\
        EL inst_idx bb.bb_instructions = inst /\
        inst.inst_id = id /\
        is_memory_def_opcode space inst.inst_opcode /\
        inst.inst_outputs = [] /\
        ~(bp_get_write_location bp inst space).ml_volatile /\
        ml_is_fixed (bp_get_write_location bp inst space) /\
        (bp_get_write_location bp inst space).ml_size <> SOME 0 /\
        outputs_unused inst fn /\
        effects_in_space space inst /\
        ~dse_mem_def_live cfg aliases bp
          (bp_get_write_location bp inst space)
          space fn bb inst_idx
End

(* ===== Accesses stay in their own alloca ===== *)

(* The access operands that bp_get_write_location and bp_get_read_location
   build a location from with bp_segment_from_ops, in space sp.  Storage
   and transient are word-addressed, so their accesses are one slot wide. *)
Definition bp_access_ops_def:
  bp_access_ops sp inst ops <=>
    case sp of
      AddrSp_Memory =>
        mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops
    | AddrSp_Storage =>
        (?dst v. inst.inst_opcode = SSTORE /\ inst.inst_operands = [dst; v] /\
                 ops = <| iao_ofst := dst; iao_size := SOME (Lit 1w);
                          iao_max_size := SOME (Lit 1w) |>) \/
        (?ofst. inst.inst_opcode = SLOAD /\ inst.inst_operands = [ofst] /\
                ops = <| iao_ofst := ofst; iao_size := SOME (Lit 1w);
                         iao_max_size := SOME (Lit 1w) |>)
    | AddrSp_Transient =>
        (?dst v. inst.inst_opcode = TSTORE /\ inst.inst_operands = [dst; v] /\
                 ops = <| iao_ofst := dst; iao_size := SOME (Lit 1w);
                          iao_max_size := SOME (Lit 1w) |>) \/
        (?ofst. inst.inst_opcode = TLOAD /\ inst.inst_operands = [ofst] /\
                ops = <| iao_ofst := ofst; iao_size := SOME (Lit 1w);
                         iao_max_size := SOME (Lit 1w) |>)
    | _ => F
End

(* Every non-empty access of inst through a pointer the base-pointer
   analysis places in alloca aid stays within aid's region in state s, and
   sits at the offset the analysis computed when it knows one (the analysis
   adds offsets without wrapping, the runtime wraps them mod 2^256).
   may_overlap treats locations in different allocas as disjoint, as
   upstream Vyper does; this is the invariant that makes that sound.
   bp_ptrs_bounded only covers memory accesses at a known offset. *)
Definition bp_accesses_in_own_alloca_def:
  bp_accesses_in_own_alloca bp inst s <=>
    !sp ops aid off base sz w size_op n.
      bp_access_ops sp inst ops /\
      bp_ptr_from_op bp ops.iao_ofst = SOME (Ptr (Allocation aid) off) /\
      FLOOKUP s.vs_allocas aid = SOME (base, sz) /\
      eval_operand ops.iao_ofst s = SOME w /\
      ops.iao_max_size = SOME size_op /\
      eval_operand size_op s = SOME n /\ n <> 0w ==>
      base <= w2n w /\ w2n w + w2n n <= base + sz /\
      (!k. off = SOME k ==> w2n w = base + k)
End

(* ===== Per-instruction transform ===== *)

(* Transform given a set of instruction IDs identified as dead stores.
   If the instruction's ID is in the dead set, NOP it.
   The dead set is computed by memSSA analysis externally. *)
(* Python: run_pass takes addr_space. The pass runs once per space. *)
Definition dse_inst_def:
  dse_inst (dead_ids : num set) (space : addr_space) inst =
    if inst.inst_id IN dead_ids /\ is_memory_def_opcode space inst.inst_opcode
    then mk_nop_inst inst
    else inst
End

(* ===== Function-level transform ===== *)

(* Single-pass: apply dead store elimination for given dead_ids. *)
Definition dse_single_pass_def:
  dse_single_pass dead_ids space fn =
    function_map_transform
      (block_map_transform (dse_inst dead_ids space)) fn
End

(* Python runs DSE in a loop: analyze → remove → re-analyze → ...
   until no more dead stores are found.
   The analysis_fn parameter computes dead store IDs for a given function.
   OWHILE terminates because each iteration removes at least one dead
   store, strictly decreasing the count of memory-writing instructions. *)
Definition dse_iterate_def:
  dse_iterate analysis_fn space fn =
    OWHILE (\fn. analysis_fn fn <> {})
         (\fn. dse_single_pass (analysis_fn fn) space fn) fn
End

(* Run DSE for one address space. Python: run_pass(addr_space). *)
Definition dse_function_space_def:
  dse_function_space analysis_fn space fn =
    case dse_iterate (analysis_fn space) space fn of
      SOME fn' => clear_nops_function fn'
    | NONE => clear_nops_function fn
End

(* Run DSE for all three address spaces (Python pipeline calls
   run_pass for each space in sequence). *)
Definition dse_function_def:
  dse_function analysis_fn fn =
    let fn1 = dse_function_space analysis_fn AddrSp_Memory fn in
    let fn2 = dse_function_space analysis_fn AddrSp_Storage fn1 in
    dse_function_space analysis_fn AddrSp_Transient fn2
End
