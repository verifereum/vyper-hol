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
 *   mem_ssa_no_redundant_phis           — no remaining phi has all-identical operands
 *   mem_ssa_reaching_acyclic            — reaching-def chain has no cycles
 *
 *   mem_ssa_clobber_sound               — clobber walk soundness (strict dominance)
 *
 * REMOVED (FALSE — see proofs/memSSACexScript.sml):
 *   mem_ssa_phi_at_frontier  — Phase 4 removes redundant src phi (no consumer)
 *)

Theory memSSAProps
Ancestors
  memSSADefs memSSAProofs

(* ===== Core well-formedness ===== *)

Theorem mem_ssa_build_wf:
  ∀cfg dom bp fn addr_sp.
    wf_function fn ⇒
    wf_mssa (mem_ssa_build cfg dom bp fn addr_sp)
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_build_wf
QED

(* ===== Reaching definition properties ===== *)

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

(* ===== Phi properties ===== *)

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

Theorem mem_ssa_reaching_acyclic:
  ∀fn bp addr_sp ms aid.
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    aid ∈ FDOM ms.ms_nodes ∧ aid ≠ 0 ⇒
    ¬∃n. n > 0 ∧ reaching_chain ms n aid aid
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_reaching_acyclic
QED

(* ===== Clobber soundness ===== *)

(* If the clobber walk returns LiveOnEntry (SOME 0), no MnDef in a
   strictly dominating block completely_contains the access location.
   Uses strict_dominates (not dominates): same-block defs after the
   access are not on the reaching chain. *)
Theorem mem_ssa_clobber_sound:
  ∀cfg dom bp fn addr_sp ms access_id fuel.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    fuel ≥ CARD (FDOM ms.ms_nodes) ∧
    mem_ssa_get_clobbered ms fuel access_id = SOME 0 ∧
    access_id ∈ FDOM ms.ms_nodes ∧
    (∀blk. THE (FLOOKUP ms.ms_nodes access_id) ≠ MnPhi blk) ⇒
    ∀def_id def_iid def_blk def_loc.
      FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) ∧
      strict_dominates dom def_blk
        (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ⇒
      ¬completely_contains def_loc
        (mn_loc (THE (FLOOKUP ms.ms_nodes access_id)))
Proof ACCEPT_TAC memSSAProofsTheory.mem_ssa_clobber_sound
QED
