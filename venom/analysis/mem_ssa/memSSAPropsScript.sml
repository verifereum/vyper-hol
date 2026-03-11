(*
 * Memory SSA Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors memSSAProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   mem_ssa_build_wf                    — construction output satisfies wf_mssa
 *   mem_ssa_reaching_def_exists_and_valid — non-phi accesses have valid reaching defs
 *   mem_ssa_reaching_def_dominates      — reaching def's block dominates use's block
 *   mem_ssa_phi_at_frontier             — phis placed at dominance frontiers of def blocks
 *   mem_ssa_no_redundant_phis           — no remaining phi has all-identical operands
 *   mem_ssa_reaching_acyclic            — reaching-def chain has no cycles
 *   mem_ssa_clobber_sound               — clobber walk structural soundness
 *)

Theory memSSAProps
Ancestors
  memSSADefs memSSAProofs

(* ===== Core well-formedness ===== *)

(* mem_ssa_build on a well-formed function produces a well-formed mem_ssa_state:
 * all index maps consistent, all edges valid, reaching defs complete. *)
Theorem mem_ssa_build_wf:
  ∀cfg dom bp fn addr_sp.
    wf_function fn ⇒
    wf_mssa (mem_ssa_build cfg dom bp fn addr_sp)
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_build_wf
QED

(* ===== Reaching definition properties ===== *)

(* For every non-phi access, the reaching definition exists and is either
 * LiveOnEntry (0) or a valid access in the state. *)
Theorem mem_ssa_reaching_def_exists_and_valid:
  ∀cfg dom bp fn addr_sp ms aid node.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd ∧
         (rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_reaching_def_exists_and_valid
QED

(* If a non-phi access has a non-LiveOnEntry reaching definition, the
 * reaching def's block dominates the access's block.  Also derives
 * def_id ∈ FDOM ms.ms_nodes from the other premises. *)
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
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_reaching_def_dominates
QED

(* ===== Phi placement ===== *)

(* Every MemPhi is at a block in the dominance frontier of some block
 * that contains at least one MemDef or MemPhi (iterated DF placement).
 * Phase 2 worklist propagates from phi-containing blocks too, so
 * the source block may have only a phi (no defs). *)
Theorem mem_ssa_phi_at_frontier:
  ∀cfg dom bp fn addr_sp ms lbl phi_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
    ∃src_lbl.
      (fmap_lookup_list ms.ms_block_defs src_lbl ≠ [] ∨
       src_lbl ∈ FDOM ms.ms_block_phis) ∧
      MEM lbl (frontier_of dom src_lbl)
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_phi_at_frontier
QED

(* After Phase 4 cleanup, no remaining phi has all-identical operands. *)
Theorem mem_ssa_no_redundant_phis:
  ∀cfg dom bp fn addr_sp ms lbl phi_id ops.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ∧
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
    ops ≠ [] ⇒
    ¬mem_ssa_phi_redundant ops
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_no_redundant_phis
QED

(* ===== Structural properties ===== *)

(* The reaching-def chain has no cycles: no non-LiveOnEntry access can
 * reach itself through one or more reaching-def steps. *)
Theorem mem_ssa_reaching_acyclic:
  ∀cfg dom bp fn addr_sp ms aid.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    aid ∈ FDOM ms.ms_nodes ∧ aid ≠ 0 ⇒
    ¬∃n. n > 0 ∧ reaching_chain ms n aid aid
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_reaching_acyclic
QED

(* ===== Clobber soundness ===== *)

(* If the clobber walk returns LiveOnEntry (SOME 0), then no MemDef whose
 * block dominates the queried access's block has a location that
 * completely_contains the query location.
 * Fuel must be sufficient to traverse the entire reaching chain. *)
Theorem mem_ssa_clobber_sound:
  ∀cfg dom bp fn addr_sp ms alias access_id fuel.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    wf_alias_sets alias ∧
    fuel ≥ CARD (FDOM ms.ms_nodes) ∧
    mem_ssa_get_clobbered ms fuel access_id = SOME 0 ∧
    access_id ∈ FDOM ms.ms_nodes ⇒
    ∀def_id def_iid def_blk def_loc.
      FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) ∧
      dominates dom def_blk
        (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ⇒
      ¬completely_contains def_loc
        (mn_loc (THE (FLOOKUP ms.ms_nodes access_id)))
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_clobber_sound
QED

