(*
 * Simplify CFG Pass — Correctness Statement
 *
 * Proof in proofs/simplifyCfgProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory simplifyCfgCorrectness
Ancestors
  simplifyCfgProof simplifyCfgPhi2 simplifyCfgSsaform simplifyCfgWffn simplifyCfgJnzdist
  simplifyCfgReach simplifyCfgReachuses simplifyCfgWfssa simplifyCfgDefs cfgWf unitShapeDefs
  venomInst

Theorem simplify_cfg_pass_correct:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_bisim fn (simplify_cfg_fn fn)
Proof
  ACCEPT_TAC simplify_cfg_fn_correct
QED

(* ===== Obligations ===== *)

Theorem simplify_cfg_establishes_all_reachable:
  ∀func. wf_function func ⇒ all_reachable (simplify_cfg_fn func)
Proof
  rpt strip_tac >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  irule simplify_cfg_iter_with_labels_reachable >>
  simp[] >> strip_tac >> gvs[all_reachable_def]
QED

Theorem simplify_cfg_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (simplify_cfg_fn func)
Proof
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def,
       simplify_cfg_iter_with_labels_ssa]
QED

Theorem simplify_cfg_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (simplify_cfg_fn func)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_def,
       simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def,
       simplify_cfg_iter_with_labels_wf]
QED

(* Run 5 of the O1 walk runs after MakeSSA and before passes that need
   wf_ssa (SingleUseExpansion, DFT), so it must keep it.  A merged block's
   uses are dominated through its sole predecessor; a bypass replaces a
   PHI's label b by b's sole predecessor a (or drops it when a is already
   there, with the same value), and a dominates b.  fn_shape_ok rules out
   a JNZ whose condition is a label: the CFG counts that label as an edge,
   and canonicalizing the JNZ drops the edge without repairing the target's
   PHI, so a later merge can leave two PHI pairs from one predecessor.
   simplify_cfg_fn_ok includes the entry block having no PHI. *)
Theorem simplify_cfg_preserves_wf_ssa:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  first_block_no_preds fn /\ simplify_cfg_fn_ok fn ==>
  wf_ssa (simplify_cfg_fn fn)
Proof
  strip_tac >> irule simplify_cfg_fn_ssa_invariant >>
  fs[simplifyCfgPhiRepairTheory.simplify_cfg_fn_ok_phi_safe,
     fn_shape_ok_def, inst_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

(* The pre-walk run feeds MakeSSA, which needs its input's uses defined on
   every path. *)
Theorem simplify_cfg_preserves_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_defs_reach_uses (simplify_cfg_fn fn)
Proof
  strip_tac >>
  `scfg_reachuses_inv fn` by
    (fs[simplifyCfgPhiRepairTheory.simplify_cfg_fn_ok_phi_safe, scfg_reachuses_inv_def] >>
     metis_tac[fn_shape_ok_jnz_condition_ok]) >>
  drule (simplify_cfg_iter_reachuses_inv |> SPEC_ALL) >>
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_def,
    simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def, scfg_reachuses_inv_def]
QED

(* ===== Output shape ===== *)

(* fix_phi_inst turns a PHI left with fewer than two inputs into a NOP or
   an ASSIGN. *)
Theorem simplify_cfg_phi_two_pairs:
  wf_function fn /\ fn_inst_wf fn ==>
  !inst. MEM inst (fn_insts (simplify_cfg_fn fn)) /\ inst.inst_opcode = PHI ==>
         2 <= LENGTH (phi_pairs inst.inst_operands)
Proof
  strip_tac >> match_mp_tac simplify_cfg_fn_phi_arity >> simp[]
QED

(* A bypass that makes a JNZ's targets meet turns it into a JMP
   (canon_jnz_inst); no other step changes a kept JNZ's targets. *)
Theorem simplify_cfg_jnz_targets_distinct:
  wf_function fn /\ fn_shape_ok fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
          ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) ==>
  !inst. MEM inst (fn_insts (simplify_cfg_fn fn)) /\ inst.inst_opcode = JNZ ==>
         ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  strip_tac >>
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_def,
       simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def] >>
  qspecl_then [`LENGTH fn.fn_blocks`, `fn`] mp_tac
    simplify_cfg_iter_with_labels_jnz_distinct >> simp[]
QED
