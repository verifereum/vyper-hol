(*
 * Memory SSA Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors memSSAProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   mssa_build_wf                    — construction output satisfies wf_mssa
 *   mssa_reaching_def_exists_and_valid — non-phi accesses have valid reaching defs
 *   mssa_reaching_def_dominates      — reaching def's block dominates use's block
 *   mssa_phi_at_frontier             — phis placed at dominance frontiers of def blocks
 *   mssa_no_redundant_phis           — no remaining phi has all-identical operands
 *   mssa_reaching_acyclic            — reaching-def chain has no cycles
 *   mssa_clobber_sound               — clobber walk structural soundness
 *)

Theory memSSAProps
Ancestors
  memSSADefs memSSAProofs

(* ===== Core well-formedness ===== *)

(* mssa_build on a well-formed function produces a well-formed mssa_state:
 * all index maps consistent, all edges valid, reaching defs complete. *)
Theorem mssa_build_wf:
  ∀cfg dom bp fn addr_sp.
    wf_function fn ⇒
    wf_mssa (mssa_build cfg dom bp fn addr_sp)
Proof ACCEPT_TAC memSSAProofsTheory.mssa_build_wf
QED

(* ===== Reaching definition properties ===== *)

(* For every non-phi access, the reaching definition exists and is either
 * LiveOnEntry (0) or a valid access in the state. *)
Theorem mssa_reaching_def_exists_and_valid:
  ∀cfg dom bp fn addr_sp ms aid node.
    wf_function fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd ∧
         (rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof ACCEPT_TAC memSSAProofsTheory.mssa_reaching_def_exists_and_valid
QED

(* If a non-phi access has a non-LiveOnEntry reaching definition, the
 * reaching def's block dominates the access's block.  Also derives
 * def_id ∈ FDOM ms.ms_nodes from the other premises. *)
Theorem mssa_reaching_def_dominates:
  ∀cfg dom bp fn addr_sp ms use_id def_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_reaching use_id = SOME def_id ∧
    def_id ≠ 0 ∧
    use_id ∈ FDOM ms.ms_nodes ⇒
    def_id ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes def_id)))
                  (mn_block (THE (FLOOKUP ms.ms_nodes use_id)))
Proof ACCEPT_TAC memSSAProofsTheory.mssa_reaching_def_dominates
QED

(* ===== Phi placement ===== *)

(* Every MemPhi is at a block in the dominance frontier of some block
 * that contains at least one MemDef. *)
Theorem mssa_phi_at_frontier:
  ∀cfg dom bp fn addr_sp ms lbl phi_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
    ∃def_lbl.
      fmap_lookup_list ms.ms_block_defs def_lbl ≠ [] ∧
      MEM lbl (frontier_of dom def_lbl)
Proof ACCEPT_TAC memSSAProofsTheory.mssa_phi_at_frontier
QED

(* After Phase 4 cleanup, no remaining phi has all-identical operands. *)
Theorem mssa_no_redundant_phis:
  ∀cfg dom bp fn addr_sp ms lbl phi_id ops.
    wf_function fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ∧
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
    ops ≠ [] ⇒
    ¬mssa_phi_redundant ops
Proof ACCEPT_TAC memSSAProofsTheory.mssa_no_redundant_phis
QED

(* ===== Structural properties ===== *)

(* The reaching-def chain has no cycles: no non-LiveOnEntry access can
 * reach itself through one or more reaching-def steps. *)
Theorem mssa_reaching_acyclic:
  ∀cfg dom bp fn addr_sp ms aid.
    wf_function fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    aid ∈ FDOM ms.ms_nodes ∧ aid ≠ 0 ⇒
    ¬∃n. n > 0 ∧ reaching_chain ms n aid aid
Proof ACCEPT_TAC memSSAProofsTheory.mssa_reaching_acyclic
QED

(* ===== Clobber soundness ===== *)

(* If the clobber walk returns LiveOnEntry (SOME 0), then no MemDef whose
 * block dominates the queried access's block has a location that
 * completely_contains the query location. *)
Theorem mssa_clobber_sound:
  ∀cfg dom bp fn addr_sp ms alias access_id fuel.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    wf_alias_sets alias ∧
    mssa_get_clobbered ms fuel access_id = SOME 0 ∧
    access_id ∈ FDOM ms.ms_nodes ⇒
    ∀def_id def_iid def_blk def_loc.
      FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) ∧
      dominates dom def_blk
        (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ⇒
      ¬completely_contains def_loc
        (mn_loc (THE (FLOOKUP ms.ms_nodes access_id)))
Proof ACCEPT_TAC memSSAProofsTheory.mssa_clobber_sound
QED

