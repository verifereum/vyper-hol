(*
 * Memory Alias Analysis — Definitions
 *
 * Ported from vyper/venom/analysis/mem_alias.py.
 * Coarse memory alias analysis: determines which memory locations may alias.
 * For each instruction, computes read/write locations via base pointer analysis,
 * then builds pairwise alias sets using may_overlap.
 *
 * TOP-LEVEL:
 *   alias_sets (type), wf_alias_sets,
 *   ma_analyze_inst, ma_analyze_block, ma_analyze,
 *   ma_may_alias, ma_mark_volatile,
 *   memory_alias_analyze, storage_alias_analyze, transient_alias_analyze
 *
 * Helper:
 *   ma_add_location, ma_analyze_blocks
 *
 * Divergences from Python:
 *   - alias_sets is (mem_loc, mem_loc list) fmap instead of dict[MemoryLocation, OrderedSet]
 *   - Three instantiations (Memory/Storage/Transient) via addr_space parameter
 *   - ma_may_alias is pure (Python version lazily mutates alias_sets for unknown locs)
 *)

Theory memAliasDefs
Ancestors
  basePtrDefs

(* ===== Alias Set Type ===== *)

(* Map from memory locations to lists of potentially aliasing locations.
 * Each location maps to the set of known locations that may_overlap with it. *)
Type alias_sets = ``:(mem_loc, mem_loc list) fmap``

(* ===== Well-Formedness Invariant ===== *)

(* An alias set is well-formed when:
 *   1. Correctness: every entry in an alias list actually overlaps its key
 *   2. Completeness: if two tracked locations overlap, each appears in the
 *      other's alias list
 * Symmetry of alias lists follows from (1) + (2). *)
Definition wf_alias_sets_def:
  wf_alias_sets (sets : alias_sets) ⇔
    (* Correctness: listed aliases actually overlap *)
    (∀loc als a.
       FLOOKUP sets loc = SOME als ∧ MEM a als ⇒
       may_overlap loc a) ∧
    (* Completeness: overlapping tracked locations are cross-listed *)
    (∀l1 l2 als1.
       FLOOKUP sets l1 = SOME als1 ∧ l2 ∈ FDOM sets ∧ may_overlap l1 l2 ⇒
       MEM l2 als1)
End

(* ===== Core: Add a Location to Alias Sets ===== *)

(* Add a memory location to alias sets, updating pairwise relationships.
 * For each existing location that may_overlap with loc, add loc to its alias
 * list and add it to loc's alias list.
 * Matches Python _analyze_mem_location. *)
Definition ma_add_location_def:
  ma_add_location (sets : alias_sets) loc =
    let current = case FLOOKUP sets loc of SOME l => l | NONE => [] in
    (* Find all existing locations that overlap with loc *)
    let keys = MAP FST (fmap_to_alist sets) in
    let overlapping = FILTER (λk. may_overlap loc k) keys in
    (* Add loc as alias of each overlapping location *)
    let sets1 = FOLDL (λs k.
      let old = case FLOOKUP s k of SOME l => l | NONE => [] in
      if MEM loc old then s else s |+ (k, loc :: old)) sets overlapping in
    (* Set loc's alias list to all overlapping locations *)
    sets1 |+ (loc, overlapping ++ current)
End

(* ===== Instruction-Level Analysis ===== *)

(* Analyze one instruction: add its read and write locations to alias sets.
 * Matches Python _analyze_instruction. *)
Definition ma_analyze_inst_def:
  ma_analyze_inst bp_result addr_sp (sets : alias_sets) inst =
    let rloc = bp_get_read_location bp_result inst addr_sp in
    let wloc = bp_get_write_location bp_result inst addr_sp in
    let sets1 = if rloc = ml_empty ∨ rloc = ml_undefined then sets
                else ma_add_location sets rloc in
    let sets2 = if wloc = ml_empty ∨ wloc = ml_undefined then sets1
                else ma_add_location sets1 wloc in
    sets2
End

(* ===== Block-Level Analysis ===== *)

(* Process all instructions in a block. *)
Definition ma_analyze_block_def:
  ma_analyze_block bp_result addr_sp sets [] = sets ∧
  ma_analyze_block bp_result addr_sp sets (inst::insts) =
    ma_analyze_block bp_result addr_sp
      (ma_analyze_inst bp_result addr_sp sets inst) insts
End

(* ===== Function-Level Analysis ===== *)

(* Analyze all blocks in a function.
 * Matches Python analyze. *)
Definition ma_analyze_blocks_def:
  ma_analyze_blocks bp_result addr_sp sets [] = sets ∧
  ma_analyze_blocks bp_result addr_sp sets (bb::bbs) =
    ma_analyze_blocks bp_result addr_sp
      (ma_analyze_block bp_result addr_sp sets bb.bb_instructions) bbs
End

(* Top-level entry point.
 * bp_result comes from bp_analyze (base pointer analysis). *)
Definition ma_analyze_def:
  ma_analyze bp_result fn addr_sp =
    ma_analyze_blocks bp_result addr_sp FEMPTY fn.fn_blocks
End

(* ===== Query: May-Alias ===== *)

(* Check if two locations may alias according to the analysis result.
 * Volatile locations fall through to direct may_overlap check.
 * For non-volatile, checks the precomputed alias sets.
 * Falls back to may_overlap if location was not seen during analysis.
 * Matches Python may_alias. *)
Definition ma_may_alias_def:
  ma_may_alias (sets : alias_sets) loc1 loc2 =
    if loc1.ml_volatile ∨ loc2.ml_volatile then
      may_overlap loc1 loc2
    else
      case (FLOOKUP sets loc1, FLOOKUP sets loc2) of
        (SOME aliases1, SOME _) => MEM loc2 aliases1
      | _ => may_overlap loc1 loc2
End

(* ===== Mark Volatile ===== *)

(* Mark a location as volatile and propagate alias info.
 * Volatile locations conservatively alias with everything that overlaps.
 * Matches Python mark_volatile. *)
Definition ma_mark_volatile_def:
  ma_mark_volatile (sets : alias_sets) loc =
    let vloc = mk_volatile loc in
    case FLOOKUP sets loc of
      NONE => (vloc, sets)
    | SOME aliases =>
        (* vloc aliases itself, loc, and everything loc aliases *)
        let vloc_aliases = vloc :: loc :: FILTER (λa. a ≠ loc ∧ a ≠ vloc) aliases in
        let sets1 = sets |+ (vloc, vloc_aliases) in
        (* Add vloc to loc's alias list *)
        let sets2 = sets1 |+ (loc, vloc :: aliases) in
        (* Add vloc to all of loc's existing aliases *)
        let sets3 = FOLDL (λs a.
          if a = loc ∨ a = vloc then s
          else case FLOOKUP s a of
                 SOME alist => s |+ (a, vloc :: alist)
               | NONE => s) sets2 (FILTER (λa. a ≠ loc ∧ a ≠ vloc) aliases) in
        (vloc, sets3)
End

(* ===== Three Address-Space Instantiations ===== *)

Definition memory_alias_analyze_def:
  memory_alias_analyze bp_result fn = ma_analyze bp_result fn AddrSp_Memory
End

Definition storage_alias_analyze_def:
  storage_alias_analyze bp_result fn = ma_analyze bp_result fn AddrSp_Storage
End

Definition transient_alias_analyze_def:
  transient_alias_analyze bp_result fn = ma_analyze bp_result fn AddrSp_Transient
End

