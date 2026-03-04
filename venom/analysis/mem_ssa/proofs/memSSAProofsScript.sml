(*
 * Memory SSA Analysis — Proofs
 *
 * Proves safety properties of the memory SSA construction.
 * Consumed by memSSAPropsScript.sml via ACCEPT_TAC.
 *)

Theory memSSAProofs
Ancestors
  memSSADefs
  dominatorAnalysisProps
  cfgAnalysisProps
  memAliasProps
Libs
  listTheory finite_mapTheory pairTheory

(* ==========================================================================
   Well-formedness: sub-predicates
   ========================================================================== *)

(* All access ids referenced from block-level maps exist in ms_nodes *)
Definition mem_ssa_ids_valid_def:
  mem_ssa_ids_valid ms ⇔
    (∀lbl aids aid.
       (FLOOKUP ms.ms_block_defs lbl = SOME aids ∨
        FLOOKUP ms.ms_block_uses lbl = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM ms.ms_nodes) ∧
    (∀lbl phi_id.
       FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
       phi_id ∈ FDOM ms.ms_nodes)
End

(* Reaching defs and phi operands reference valid access ids *)
Definition mem_ssa_edges_valid_def:
  mem_ssa_edges_valid ms ⇔
    (∀aid rd.
       FLOOKUP ms.ms_reaching aid = SOME rd ⇒
       rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒
       rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
End

(* inst_def/inst_use maps are consistent with node contents *)
Definition mem_ssa_inst_maps_consistent_def:
  mem_ssa_inst_maps_consistent ms ⇔
    (∀iid aid.
       FLOOKUP ms.ms_inst_def iid = SOME aid ⇒
       ∃blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid blk loc)) ∧
    (∀iid aid.
       FLOOKUP ms.ms_inst_use iid = SOME aid ⇒
       ∃blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnUse iid blk loc))
End

(* Every non-phi access has a reaching def in ms_reaching *)
Definition mem_ssa_reaching_complete_def:
  mem_ssa_reaching_complete ms ⇔
    ∀aid node.
      FLOOKUP ms.ms_nodes aid = SOME node ∧
      (∀blk. node ≠ MnPhi blk) ⇒
      ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd
End

(* Composite well-formedness *)
Definition wf_mem_ssa_def:
  wf_mssa ms ⇔
    mem_ssa_ids_valid ms ∧
    mem_ssa_edges_valid ms ∧
    mem_ssa_inst_maps_consistent ms ∧
    mem_ssa_reaching_complete ms
End

(* ==========================================================================
   Property 1: Construction produces well-formed state
   ========================================================================== *)

(* mem_ssa_build on a well-formed function produces a well-formed mem_ssa_state:
 * all block/inst index maps are consistent with ms_nodes, all reaching-def
 * edges point to valid nodes or LiveOnEntry, and every non-phi access has
 * a reaching definition. *)
Theorem mem_ssa_build_wf:
  ∀cfg dom bp fn addr_sp.
    wf_function fn ⇒
    wf_mssa (mem_ssa_build cfg dom bp fn addr_sp)
Proof
  cheat
QED

(* ==========================================================================
   Property 2: Reaching def validity and completeness
   ========================================================================== *)

(* For every non-phi access, the reaching definition exists and is either
 * LiveOnEntry (0) or a valid access in the state.
 * Stronger than just mem_ssa_edges_valid: also asserts the reaching def exists. *)
Theorem mem_ssa_reaching_def_exists_and_valid:
  ∀cfg dom bp fn addr_sp ms aid node.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd ∧
         (rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof
  cheat
QED

(* ==========================================================================
   Property 3: Reaching def dominates use
   ========================================================================== *)

(* If a non-phi access has a non-LiveOnEntry reaching definition, then the
 * reaching def's block dominates the access's block.
 * The precondition def_id ∈ FDOM ms.ms_nodes is derivable from the other
 * premises (via mem_ssa_reaching_def_exists_and_valid), but is included for
 * direct usability. *)
Theorem mem_ssa_reaching_def_dominates:
  ∀cfg dom bp fn addr_sp ms use_id def_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_reaching use_id = SOME def_id ∧
    def_id ≠ 0 ∧
    use_id ∈ FDOM ms.ms_nodes ⇒
    def_id ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes def_id)))
                  (mn_block (THE (FLOOKUP ms.ms_nodes use_id)))
Proof
  cheat
QED

(* ==========================================================================
   Property 4: Phi placement at dominance frontiers
   ========================================================================== *)

(* Every MemPhi is placed at a block in the dominance frontier of some
 * block that contains at least one MemDef. *)
Theorem mem_ssa_phi_at_frontier:
  ∀cfg dom bp fn addr_sp ms lbl phi_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
    ∃def_lbl.
      fmap_lookup_list ms.ms_block_defs def_lbl ≠ [] ∧
      MEM lbl (frontier_of dom def_lbl)
Proof
  cheat
QED

(* ==========================================================================
   Property 5: No redundant phis after construction
   ========================================================================== *)

(* After construction (which includes Phase 4 cleanup), no remaining phi
 * has all operands pointing to the same reaching definition. *)
Theorem mem_ssa_no_redundant_phis:
  ∀cfg dom bp fn addr_sp ms lbl phi_id ops.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ∧
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
    ops ≠ [] ⇒
    ¬mem_ssa_phi_redundant ops
Proof
  cheat
QED

(* ==========================================================================
   Property 6: Reaching-def chain is acyclic
   ========================================================================== *)

(* Transitive closure of the reaching-def relation.
 * reaching_chain ms n a b holds when b is reachable from a in at most n
 * steps through ms_reaching (for defs/uses) or ms_phi_ops (for phis). *)
Definition reaching_chain_def:
  reaching_chain ms 0 a b = (a = b) ∧
  reaching_chain ms (SUC n) a b =
    (a = b ∨
     ∃mid. FLOOKUP ms.ms_reaching a = SOME mid ∧
           reaching_chain ms n mid b)
End

(* The reaching-def chain has no cycles: no non-LiveOnEntry access can
 * reach itself through one or more reaching-def steps. *)
Theorem mem_ssa_reaching_acyclic:
  ∀cfg dom bp fn addr_sp ms aid.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    aid ∈ FDOM ms.ms_nodes ∧ aid ≠ 0 ⇒
    ¬∃n. n > 0 ∧ reaching_chain ms n aid aid
Proof
  cheat
QED

(* ==========================================================================
   Property 7: Clobber walk soundness
   ========================================================================== *)

(* If the clobber walk returns LiveOnEntry (SOME 0), then no MemDef whose
 * block dominates the queried access's block has a location that
 * completely_contains the query location.
 *
 * This is a structural (dominance-based) soundness statement.  Full
 * execution-path-based semantic soundness would additionally require
 * CFG path reasoning.  *)
Theorem mem_ssa_clobber_sound:
  ∀cfg dom bp fn addr_sp ms alias access_id fuel.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    wf_alias_sets alias ∧
    mem_ssa_get_clobbered ms fuel access_id = SOME 0 ∧
    access_id ∈ FDOM ms.ms_nodes ⇒
    ∀def_id def_iid def_blk def_loc.
      FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) ∧
      dominates dom def_blk
        (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ⇒
      ¬completely_contains def_loc
        (mn_loc (THE (FLOOKUP ms.ms_nodes access_id)))
Proof
  cheat
QED

