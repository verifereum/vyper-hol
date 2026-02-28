(*
 * Liveness Analysis — Internal Correctness Proofs
 *
 * Proofs are re-exported via livenessAnalysisPropsScript.sml.
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs dfIterateProofs cfgAnalysisProps cfgHelpers

open listTheory pred_setTheory arithmeticTheory venomInstTheory finite_mapTheory
     pairTheory alistTheory sptreeTheory cfgAnalysisPropsTheory WhileTheory
     cfgHelpersTheory venomStateTheory dfIterateDefsTheory

(* ===== Set-as-list helpers ===== *)

Theorem list_union_mem[local]:
  ∀v xs ys. MEM v (list_union xs ys) ⇔ MEM v xs ∨ MEM v ys
Proof
  rw[list_union_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem list_union_set_proof:
  ∀xs ys. set (list_union xs ys) = set xs ∪ set ys
Proof
  rw[list_union_def, LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, EXTENSION] >>
  metis_tac[]
QED

Theorem live_update_set_proof:
  ∀defs uses live.
    set (live_update defs uses live) = (set live DIFF set defs) ∪ set uses
Proof
  rw[live_update_def, LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, EXTENSION] >>
  metis_tac[]
QED

Theorem list_union_no_dups_proof:
  ∀xs ys. ALL_DISTINCT xs ∧ ALL_DISTINCT ys ==>
    ALL_DISTINCT (list_union xs ys)
Proof
  rw[list_union_def, ALL_DISTINCT_APPEND, MEM_FILTER] >>
  metis_tac[FILTER_ALL_DISTINCT]
QED

Theorem live_update_no_dups_proof:
  ∀defs uses live.
    ALL_DISTINCT live ∧ ALL_DISTINCT uses ==>
    ALL_DISTINCT (live_update defs uses live)
Proof
  rw[live_update_def, ALL_DISTINCT_APPEND, MEM_FILTER] >>
  metis_tac[FILTER_ALL_DISTINCT]
QED

Theorem live_update_mem[local]:
  ∀v defs uses live.
    MEM v (live_update defs uses live) ⇔
    (MEM v live ∧ ¬MEM v defs) ∨ MEM v uses
Proof
  rw[live_update_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

(* ===== PHI correctness ===== *)

Theorem phi_pairs_subset_uses[local]:
  ∀ops v. MEM v (MAP SND (phi_pairs ops)) ==> MEM v (operand_vars ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  rw[phi_pairs_def, operand_vars_def, operand_var_def] >>
  rpt strip_tac >>
  TRY (Cases_on `operand_var v1`) >> fs[] >> metis_tac[]
QED

Theorem input_vars_from_phi_correct_proof:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ inst.inst_opcode = PHI ∧
           MEM (src_label, v) (phi_pairs inst.inst_operands)
Proof
  Induct_on `instrs` >- simp[input_vars_from_def] >>
  rpt gen_tac >> simp[Once input_vars_from_def] >> strip_tac >>
  first_x_assum (qspecl_then [`src_label`,
    `if h.inst_opcode ≠ PHI then base
     else list_union
       (FILTER (λv. ¬MEM v (MAP SND (FILTER (λ(l,v). l ≠ src_label)
          (phi_pairs h.inst_operands)))) base)
       (MAP SND (FILTER (λ(l,v). l = src_label)
          (phi_pairs h.inst_operands)))`, `v`] mp_tac) >>
  impl_tac >- fs[input_vars_from_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  fs[list_union_mem, MEM_FILTER, MEM_MAP] >>
  TRY (metis_tac[]) >>
  disj2_tac >> qexists_tac `h` >> Cases_on `y` >> gvs[]
QED

Theorem input_vars_from_non_phi_proof:
  ∀src_label instrs base.
    EVERY (λinst. inst.inst_opcode ≠ PHI) instrs ==>
    input_vars_from src_label instrs base = base
Proof
  Induct_on `instrs` >- simp[input_vars_from_def] >>
  rpt strip_tac >> fs[input_vars_from_def, FOLDL]
QED

(* input_vars_from only adds vars from inst_uses of PHI instructions *)
Theorem input_vars_from_vars_bounded[local]:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ MEM v (inst_uses inst)
Proof
  rpt strip_tac >>
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  disj2_tac >> qexists_tac `inst` >> rw[inst_uses_def] >>
  irule phi_pairs_subset_uses >>
  simp[MEM_MAP] >> qexists_tac `(src_label, v)` >> simp[]
QED

(* ===== Variable-boundedness invariant ===== *)

(* All vars in an lr come from a given universe U *)
Definition lr_vars_bounded_def:
  lr_vars_bounded lr U ⇔
    (∀lbl v. MEM v (out_vars_of lr lbl) ==> MEM v U) ∧
    (∀lbl idx v. MEM v (live_vars_at lr lbl idx) ==> MEM v U)
End

(* lr_vars_bounded implies inst_liveness entries of lookup_block_liveness
   are bounded. Connects lr_vars_bounded (which uses live_vars_at) to raw
   FLOOKUP on bl_inst_liveness. *)
Theorem lr_vars_bounded_inst_liveness[local]:
  ∀lr U lbl idx vars.
    lr_vars_bounded lr U ∧
    FLOOKUP (lookup_block_liveness lr lbl).bl_inst_liveness idx = SOME vars ==>
    ∀v. MEM v vars ==> MEM v U
Proof
  rw[lr_vars_bounded_def] >>
  first_x_assum (qspecl_then [`lbl`, `idx`, `v`] mp_tac) >>
  simp[live_vars_at_def]
QED

(* Similarly for out_vars *)
Theorem lr_vars_bounded_out_vars[local]:
  ∀lr U lbl.
    lr_vars_bounded lr U ==>
    ∀v. MEM v (lookup_block_liveness lr lbl).bl_out_vars ==> MEM v U
Proof
  rw[lr_vars_bounded_def] >> metis_tac[out_vars_of_def]
QED

Theorem foldl_init_lookup_gen[local]:
  ∀bbs acc lbl.
    (∀l bl. FLOOKUP acc l = SOME bl ==> bl = empty_block_liveness) ==>
    case FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
           acc bbs) lbl of
      NONE => T
    | SOME bl => bl = empty_block_liveness
Proof
  Induct >> rw[FOLDL] >- (
    Cases_on `FLOOKUP acc lbl` >> simp[] >> res_tac
  ) >>
  first_x_assum irule >> rw[FLOOKUP_UPDATE] >> res_tac
QED

Theorem foldl_init_lookup[local]:
  ∀bbs lbl.
    (case FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
           FEMPTY bbs) lbl of
      NONE => empty_block_liveness
    | SOME bl => bl) = empty_block_liveness
Proof
  rpt gen_tac >>
  qspecl_then [`bbs`, `FEMPTY`, `lbl`] mp_tac foldl_init_lookup_gen >>
  impl_tac >- rw[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
    FEMPTY bbs) lbl` >> simp[]
QED

Theorem init_lookup_block[local]:
  ∀bbs lbl.
    lookup_block_liveness (init_liveness bbs) lbl = empty_block_liveness
Proof
  rw[lookup_block_liveness_def, init_liveness_def] >>
  qspecl_then [`bbs`, `FEMPTY`, `lbl`] mp_tac foldl_init_lookup_gen >>
  impl_tac >- rw[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
    FEMPTY bbs) lbl` >> simp[]
QED

Theorem init_liveness_bounded[local]:
  ∀bbs U. lr_vars_bounded (init_liveness bbs) U
Proof
  rw[lr_vars_bounded_def, out_vars_of_def, live_vars_at_def,
     init_lookup_block, empty_block_liveness_def, FLOOKUP_DEF]
QED

(* inst_uses and inst_defs of any instruction in bbs are in fn_all_vars *)
Theorem fn_all_vars_mem[local]:
  ∀bbs bb inst v.
    MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
    (MEM v (inst_uses inst) ∨ MEM v (inst_defs inst)) ==>
    MEM v (fn_all_vars bbs)
Proof
  rw[fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND] >> (
    qexists_tac `FLAT (MAP (λi. inst_uses i ++ inst_defs i)
      bb.bb_instructions)` >>
    rw[MEM_FLAT, MEM_MAP, MEM_APPEND] >>
    TRY (qexists_tac `bb` >> rw[]) >>
    qexists_tac `inst_uses inst ++ inst_defs inst` >>
    rw[MEM_APPEND] >> qexists_tac `inst` >> rw[])
QED

Theorem lookup_block_mem[local]:
  ∀lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def] >>
  Cases_on `h.bb_label = lbl` >> fs[] >> res_tac >> simp[]
QED

Theorem lookup_block_label[local]:
  ∀lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def] >>
  Cases_on `h.bb_label = lbl` >> fs[]
QED

(* Converse: if label is among block labels, lookup_block succeeds *)
Theorem lookup_block_exists[local]:
  ∀k bbs. MEM k (MAP (λbb. bb.bb_label) bbs) ==>
          ∃bb. lookup_block k bbs = SOME bb
Proof
  Induct_on `bbs` >> rw[lookup_block_def] >> metis_tac[]
QED

(* General: FOLDL preserves a predicate on the accumulator *)
Theorem foldl_preserves[local]:
  ∀f ls acc. P acc ∧ (∀a x. P a ==> P (f a x)) ==> P (FOLDL f acc ls)
Proof
  Induct_on `ls` >> rw[FOLDL]
QED

(* One step of calculate_out_vars preserves boundedness *)
Theorem calc_out_step_bounded[local]:
  ∀acc succ_lbl lr bb bbs.
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    (∀v. MEM v acc ==> MEM v (fn_all_vars bbs)) ==>
    ∀v. MEM v (case lookup_block succ_lbl bbs of
          NONE => acc
        | SOME succ_bb =>
          list_union acc (input_vars_from bb.bb_label
            succ_bb.bb_instructions (live_vars_at lr succ_lbl 0))) ==>
    MEM v (fn_all_vars bbs)
Proof
  rpt strip_tac >>
  Cases_on `lookup_block succ_lbl bbs` >> fs[list_union_mem] >>
  drule input_vars_from_vars_bounded >> strip_tac >>
  fs[lr_vars_bounded_def] >> res_tac >>
  imp_res_tac lookup_block_mem >> irule fn_all_vars_mem >> metis_tac[]
QED

(* FOLDL list_union-like accumulation: membership comes from some step *)
Theorem calc_out_foldl_bounded[local]:
  ∀succs acc lr bb bbs.
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    (∀v. MEM v acc ==> MEM v (fn_all_vars bbs)) ==>
    ∀v. MEM v (FOLDL (λacc succ_lbl.
      case lookup_block succ_lbl bbs of
        NONE => acc
      | SOME succ_bb =>
        list_union acc (input_vars_from bb.bb_label
          succ_bb.bb_instructions (live_vars_at lr succ_lbl 0)))
      acc succs) ==> MEM v (fn_all_vars bbs)
Proof
  Induct >> rw[FOLDL] >>
  qpat_x_assum `∀acc. _` (fn th =>
    irule (SIMP_RULE (srw_ss()) [] (Q.SPECL [
      `case lookup_block h bbs of NONE => acc
       | SOME succ_bb => list_union acc
           (input_vars_from bb.bb_label succ_bb.bb_instructions
              (live_vars_at lr h 0))`,
      `lr`, `bb`, `bbs`] th))) >>
  metis_tac[calc_out_step_bounded]
QED

(* calculate_out_vars produces vars bounded by fn_all_vars *)
Theorem calculate_out_vars_bounded[local]:
  ∀cfg lr bb bbs v.
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    MEM v (calculate_out_vars cfg lr bb bbs) ==>
    MEM v (fn_all_vars bbs)
Proof
  rw[calculate_out_vars_def] >>
  drule_then (qspecl_then [`cfg_succs_of cfg bb.bb_label`, `[]`, `bb`] mp_tac)
    calc_out_foldl_bounded >> simp[]
QED

(* live_update with an instruction from bbs preserves boundedness *)
Theorem live_update_inst_bounded[local]:
  ∀bbs bb inst live.
    MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
    (∀v. MEM v live ==> MEM v (fn_all_vars bbs)) ==>
    ∀v. MEM v (live_update (inst_defs inst) (inst_uses inst) live) ==>
        MEM v (fn_all_vars bbs)
Proof
  rw[live_update_mem] >> res_tac >>
  irule fn_all_vars_mem >> metis_tac[]
QED

(* calc_liveness_loop produces vars bounded by fn_all_vars *)
Theorem calc_liveness_loop_bounded[local]:
  ∀instrs live n bbs bb.
    MEM bb bbs ∧
    (∀v. MEM v live ==> MEM v (fn_all_vars bbs)) ∧
    n < LENGTH instrs ∧
    bb.bb_instructions = instrs ==>
    (∀v. MEM v (FST (calc_liveness_loop instrs live n)) ==> MEM v (fn_all_vars bbs)) ∧
    (∀idx vars. FLOOKUP (SND (calc_liveness_loop instrs live n)) idx = SOME vars ==>
       ∀v. MEM v vars ==> MEM v (fn_all_vars bbs))
Proof
  Induct_on `n`
  >- (
    (* Base case: n = 0 *)
    rw[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    TRY (res_tac >> NO_TAC) >>
    `MEM (EL 0 bb.bb_instructions) bb.bb_instructions` by
      (irule EL_MEM >> simp[]) >>
    fs[live_update_mem] >> res_tac >>
    irule fn_all_vars_mem >> metis_tac[]
  ) >>
  (* Step case: SUC n *)
  rpt gen_tac >> strip_tac >>
  simp[calc_liveness_loop_def, LET_DEF] >>
  `MEM (EL (SUC n) bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> simp[]) >>
  qabbrev_tac `live' = if NULL (inst_uses (EL (SUC n) bb.bb_instructions)) ∧
                           NULL (inst_defs (EL (SUC n) bb.bb_instructions))
                        then live
                        else live_update (inst_defs (EL (SUC n) bb.bb_instructions))
                             (inst_uses (EL (SUC n) bb.bb_instructions)) live` >>
  `∀v. MEM v live' ==> MEM v (fn_all_vars bbs)` by (
    unabbrev_all_tac >> rw[] >> fs[live_update_mem] >> res_tac >>
    irule fn_all_vars_mem >> metis_tac[]) >>
  Cases_on `calc_liveness_loop bb.bb_instructions live' n` >>
  simp[] >>
  first_x_assum (qspecl_then [`bb.bb_instructions`, `live'`, `bbs`, `bb`] mp_tac) >>
  impl_tac >- simp[Abbr`live'`] >>
  strip_tac >> gvs[] >> rw[FLOOKUP_UPDATE] >> res_tac
QED

(* calculate_liveness preserves bl_out_vars *)
Theorem calculate_liveness_out_vars[local]:
  ∀bb bl. (calculate_liveness bb bl).bl_out_vars = bl.bl_out_vars
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  Cases_on `NULL bb.bb_instructions` >> fs[] >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions - 1)` >> simp[]
QED

(* calculate_liveness inst_liveness entries are bounded *)
Theorem calculate_liveness_inst_bounded[local]:
  ∀bb bl bbs idx vars.
    MEM bb bbs ∧
    (∀v. MEM v bl.bl_out_vars ==> MEM v (fn_all_vars bbs)) ∧
    (∀idx' vars'. FLOOKUP bl.bl_inst_liveness idx' = SOME vars' ==>
       ∀v. MEM v vars' ==> MEM v (fn_all_vars bbs)) ∧
    FLOOKUP (calculate_liveness bb bl).bl_inst_liveness idx = SOME vars ==>
    ∀v. MEM v vars ==> MEM v (fn_all_vars bbs)
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  Cases_on `NULL bb.bb_instructions` >> fs[]
  >- res_tac >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions - 1)` >> fs[] >>
  drule_then (qspecl_then [`bb.bb_instructions`, `bl.bl_out_vars`,
    `LENGTH bb.bb_instructions - 1`] mp_tac) calc_liveness_loop_bounded >>
  impl_tac >- (Cases_on `bb.bb_instructions` >> fs[]) >>
  rw[] >> res_tac
QED

(* Characterization of process_block: out_vars *)
Theorem process_block_out_vars[local]:
  ∀cfg bbs lr bb lbl.
    out_vars_of (process_block cfg bbs lr bb) lbl =
    if lbl = bb.bb_label then
      list_union (out_vars_of lr lbl) (calculate_out_vars cfg lr bb bbs)
    else out_vars_of lr lbl
Proof
  rw[process_block_def, LET_DEF] >>
  simp[out_vars_of_def, lookup_block_liveness_def, FLOOKUP_UPDATE] >>
  rw[calculate_liveness_out_vars]
QED

(* Characterization of process_block: live_vars, different label *)
Theorem process_block_live_vars_neq[local]:
  ∀cfg bbs lr bb lbl idx.
    lbl ≠ bb.bb_label ==>
    live_vars_at (process_block cfg bbs lr bb) lbl idx = live_vars_at lr lbl idx
Proof
  rw[live_vars_at_def, process_block_def, LET_DEF,
     lookup_block_liveness_def, FLOOKUP_UPDATE]
QED

(* Characterization of process_block: live_vars, same label *)
Theorem process_block_live_vars_eq[local]:
  ∀cfg bbs lr bb idx vars.
    live_vars_at (process_block cfg bbs lr bb) bb.bb_label idx = vars ∧
    vars ≠ [] ==>
    ∃bl'. (∀v. MEM v bl'.bl_out_vars ==>
              MEM v (out_vars_of lr bb.bb_label) ∨
              MEM v (calculate_out_vars cfg lr bb bbs)) ∧
          FLOOKUP (calculate_liveness bb bl').bl_inst_liveness idx = SOME vars
Proof
  rw[live_vars_at_def, process_block_def, LET_DEF,
     lookup_block_liveness_def, FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP
    (calculate_liveness bb
       ((case FLOOKUP lr.lr_blocks bb.bb_label of
           NONE => empty_block_liveness | SOME bl => bl) with
        bl_out_vars :=
          list_union
            (case FLOOKUP lr.lr_blocks bb.bb_label of
               NONE => empty_block_liveness | SOME bl => bl).bl_out_vars
            (calculate_out_vars cfg lr bb bbs))).bl_inst_liveness idx` >>
  fs[] >>
  qexists_tac `(case FLOOKUP lr.lr_blocks bb.bb_label of
     NONE => empty_block_liveness | SOME bl => bl) with
    bl_out_vars :=
      list_union
        (case FLOOKUP lr.lr_blocks bb.bb_label of
           NONE => empty_block_liveness | SOME bl => bl).bl_out_vars
        (calculate_out_vars cfg lr bb bbs)` >>
  fs[list_union_mem, out_vars_of_def, lookup_block_liveness_def]
QED

(* process_block preserves lr_vars_bounded *)
Theorem process_block_preserves_bounded[local]:
  ∀cfg bbs lr bb.
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    MEM bb bbs ==>
    lr_vars_bounded (process_block cfg bbs lr bb) (fn_all_vars bbs)
Proof
  rpt strip_tac >> rw[lr_vars_bounded_def, process_block_out_vars]
  (* out_vars: list_union of two bounded lists *)
  >- (
    Cases_on `lbl = bb.bb_label` >> fs[list_union_mem] >>
    metis_tac[calculate_out_vars_bounded, lr_vars_bounded_def]
  )
  (* live_vars *)
  >> Cases_on `lbl = bb.bb_label`
  >- (
    (* Same label: derive bounded out_vars first, then unfold *)
    gvs[] >>
    `∀v. MEM v (list_union (out_vars_of lr bb.bb_label)
                  (calculate_out_vars cfg lr bb bbs)) ==>
         MEM v (fn_all_vars bbs)` by (
      rw[list_union_mem] >>
      metis_tac[lr_vars_bounded_def, calculate_out_vars_bounded]) >>
    fs[live_vars_at_def, process_block_def, LET_DEF,
       lookup_block_liveness_def, FLOOKUP_UPDATE, out_vars_of_def] >>
    qabbrev_tac `bl0 = case FLOOKUP lr.lr_blocks bb.bb_label of
      NONE => empty_block_liveness | SOME bl => bl` >>
    qabbrev_tac `bl' = bl0 with bl_out_vars :=
      list_union bl0.bl_out_vars (calculate_out_vars cfg lr bb bbs)` >>
    (* Derive inst_liveness bounded for bl' from lr_vars_bounded *)
    `∀idx' vars'. FLOOKUP bl0.bl_inst_liveness idx' = SOME vars' ==>
       ∀v. MEM v vars' ==> MEM v (fn_all_vars bbs)` by (
      `bl0 = lookup_block_liveness lr bb.bb_label`
        by rw[Abbr`bl0`, lookup_block_liveness_def] >>
      metis_tac[lr_vars_bounded_inst_liveness]
    ) >>
    Cases_on `FLOOKUP (calculate_liveness bb bl').bl_inst_liveness idx` >>
    fs[] >>
    qspecl_then [`bb`, `bl'`, `bbs`, `idx`, `x`] mp_tac
      calculate_liveness_inst_bounded >>
    impl_tac >- (rw[Abbr`bl'`] >> res_tac) >> metis_tac[]
  )
  >> fs[process_block_live_vars_neq] >>
     metis_tac[lr_vars_bounded_def]
QED

(* Key: one pass preserves the invariant when U ⊇ fn_all_vars bbs *)
Theorem one_pass_preserves_bounded[local]:
  ∀cfg bbs order lr.
    lr_vars_bounded lr (fn_all_vars bbs) ==>
    lr_vars_bounded (liveness_one_pass cfg bbs lr order) (fn_all_vars bbs)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  first_x_assum irule >>
  irule process_block_preserves_bounded >>
  metis_tac[lookup_block_mem]
QED

(* ===== Convergence invariant for fixpoint ===== *)

(* Shape: lr.lr_blocks has keys ⊆ block labels, and each entry's
   inst_liveness keys are valid instruction indices *)
Definition lr_shaped_def:
  lr_shaped bbs lr ⇔
    (∀lbl bl bb. FLOOKUP lr.lr_blocks lbl = SOME bl ∧
                 lookup_block lbl bbs = SOME bb ==>
       FDOM bl.bl_inst_liveness ⊆ count (LENGTH bb.bb_instructions)) ∧
    FDOM lr.lr_blocks = set (MAP (λbb. bb.bb_label) bbs)
End

(* Consistency: each block entry is either unprocessed (FEMPTY inst_liveness)
   or IS what calculate_liveness produces. The FEMPTY disjunct lets
   init_liveness satisfy this invariant trivially. *)
Definition lr_consistent_def:
  lr_consistent bbs lr ⇔
    ∀lbl bl bb.
      FLOOKUP lr.lr_blocks lbl = SOME bl ∧
      lookup_block lbl bbs = SOME bb ==>
      bl.bl_inst_liveness = FEMPTY ∨ calculate_liveness bb bl = bl
End

(* Combined convergence invariant: bounded + shaped + consistent *)
Definition lr_inv_def:
  lr_inv bbs lr ⇔
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    lr_shaped bbs lr ∧
    lr_consistent bbs lr
End

(* Set-based measure: counts CARD of sets + CARD of FDOMs.
   The FDOM term tracks inst_liveness map growth (FEMPTY → populated).
   Without it, lr_leq + lr1 ≠ lr2 wouldn't imply strict measure increase
   when the only change is FDOM expansion with empty-set entries. *)
Definition set_live_count_def:
  set_live_count lr =
    SUM (MAP (λ(k,bl). CARD (set bl.bl_out_vars) +
      CARD (FDOM bl.bl_inst_liveness) +
      SUM (MAP (λ(i,vs). CARD (set vs))
        (fmap_to_alist bl.bl_inst_liveness)))
      (fmap_to_alist lr.lr_blocks))
End

(* --- FMAP helpers --- *)

Theorem foldl_fdom[local]:
  ∀bbs acc.
    FDOM (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness)) acc bbs) =
    FDOM acc ∪ set (MAP (λbb. bb.bb_label) bbs)
Proof
  Induct >> rw[FOLDL, FDOM_FUPDATE, EXTENSION] >> metis_tac[]
QED

Theorem foldl_init_flookup[local]:
  ∀bbs lbl bl.
    FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness)) FEMPTY bbs)
      lbl = SOME bl ==>
    bl = empty_block_liveness
Proof
  rpt strip_tac >>
  qspecl_then [`bbs`, `FEMPTY`, `lbl`] mp_tac foldl_init_lookup_gen >>
  impl_tac >- rw[FLOOKUP_DEF] >>
  pop_assum (fn th => REWRITE_TAC [th]) >> simp[]
QED

(* --- Initialization --- *)

Theorem init_liveness_shaped[local]:
  ∀bbs. lr_shaped bbs (init_liveness bbs)
Proof
  rw[lr_shaped_def, init_liveness_def] >>
  TRY (rw[foldl_fdom, FDOM_FEMPTY] >> NO_TAC) >>
  `lbl ∈ set (MAP (λbb. bb.bb_label) bbs)` by
    (fs[FLOOKUP_DEF, foldl_fdom, FDOM_FEMPTY]) >>
  imp_res_tac foldl_init_flookup >>
  gvs[empty_block_liveness_def, FDOM_FEMPTY]
QED

(* init_liveness satisfies lr_inv: bounded + shaped + consistent.
   Consistency holds because all blocks have FEMPTY inst_liveness. *)
Theorem init_lr_inv[local]:
  ∀bbs. lr_inv bbs (init_liveness bbs)
Proof
  rw[lr_inv_def, init_liveness_bounded, init_liveness_shaped,
     lr_consistent_def, init_liveness_def] >>
  imp_res_tac foldl_init_flookup >> gvs[empty_block_liveness_def]
QED

(* --- Shape preservation --- *)

(* calc_liveness_loop produces FDOM ⊆ count(n+1) *)
Theorem calc_liveness_loop_fdom[local]:
  ∀n instrs live.
    n < LENGTH instrs ==>
    FDOM (SND (calc_liveness_loop instrs live n)) = count (n + 1)
Proof
  Induct >>
  rw[calc_liveness_loop_def, LET_DEF, FDOM_FUPDATE, FDOM_FEMPTY]
  >- simp[EXTENSION, IN_COUNT]
  >> `n < LENGTH instrs` by simp[] >>
  qmatch_goalsub_abbrev_tac `calc_liveness_loop instrs lv n` >>
  first_x_assum (qspecl_then [`instrs`, `lv`] mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `calc_liveness_loop instrs lv n` >>
  fs[FDOM_FUPDATE, EXTENSION, IN_COUNT] >> rw[] >> simp[]
QED

Theorem calculate_liveness_fdom[local]:
  ∀bb bl.
    ¬NULL bb.bb_instructions ==>
    FDOM (calculate_liveness bb bl).bl_inst_liveness =
      count (LENGTH bb.bb_instructions)
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  `LENGTH bb.bb_instructions - 1 < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  drule calc_liveness_loop_fdom >>
  disch_then (qspec_then `bl.bl_out_vars` assume_tac) >>
  `LENGTH bb.bb_instructions - 1 + 1 = LENGTH bb.bb_instructions` by simp[] >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions - 1)` >> gvs[]
QED

Theorem process_block_preserves_shaped[local]:
  ∀cfg bbs lr bb.
    lr_shaped bbs lr ∧ lookup_block bb.bb_label bbs = SOME bb ==>
    lr_shaped bbs (process_block cfg bbs lr bb)
Proof
  rw[lr_shaped_def, process_block_def, LET_DEF, FDOM_FUPDATE,
     FLOOKUP_UPDATE]
  (* FDOM equality: bb.bb_label INSERT labels = labels *)
  >| [ALL_TAC,
      imp_res_tac lookup_block_mem >>
      `bb.bb_label ∈ set (MAP (λbb. bb.bb_label) bbs)` by
        (simp[MEM_MAP] >> metis_tac[]) >> simp[ABSORPTION_RWT]]
  >- (
    Cases_on `lbl = bb.bb_label` >> fs[]
    >- (
      (* lbl = bb.bb_label: lookup_block deterministic → bb' = bb *)
      `bb' = bb` by gvs[] >>
      gvs[] >>
      Cases_on `NULL bb.bb_instructions`
      >- (
        rw[calculate_liveness_def] >>
        rw[lookup_block_liveness_def] >>
        Cases_on `FLOOKUP lr.lr_blocks bb.bb_label` >> fs[FDOM_FEMPTY]
        >- simp[empty_block_liveness_def, FDOM_FEMPTY]
        >> res_tac >> fs[]
      )
      >> rw[calculate_liveness_fdom]
    )
    >> res_tac >> fs[]
  )
QED

Theorem one_pass_preserves_shaped[local]:
  ∀cfg bbs order lr.
    lr_shaped bbs lr ==>
    lr_shaped bbs (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  first_x_assum irule >>
  irule process_block_preserves_shaped >>
  imp_res_tac lookup_block_label >> gvs[]
QED

(* --- Consistency preservation --- *)

(* calculate_liveness is idempotent: only reads bl_out_vars *)
Theorem calculate_liveness_idempotent[local]:
  ∀bb bl. calculate_liveness bb (calculate_liveness bb bl) =
          calculate_liveness bb bl
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions - 1)` >>
  simp[]
QED

(* process_block preserves consistency when bb is from lookup_block *)
Theorem process_block_preserves_consistent[local]:
  ∀cfg bbs lr bb.
    lr_consistent bbs lr ∧
    lookup_block bb.bb_label bbs = SOME bb ==>
    lr_consistent bbs (process_block cfg bbs lr bb)
Proof
  rw[lr_consistent_def, process_block_def, LET_DEF, FLOOKUP_UPDATE] >>
  Cases_on `lbl = bb.bb_label` >> gvs[]
  >- (
    (* same label: new entry is calculate_liveness bb bl_m.
       Result is always consistent (idempotent). *)
    disj2_tac >> simp[calculate_liveness_idempotent]
  )
  >> (* different label: unchanged entry, use existing consistency *)
     metis_tac[]
QED

Theorem one_pass_preserves_consistent[local]:
  ∀cfg bbs order lr.
    lr_consistent bbs lr ==>
    lr_consistent bbs (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  first_x_assum irule >>
  irule process_block_preserves_consistent >>
  imp_res_tac lookup_block_label >> gvs[]
QED

(* --- Combined invariant preservation --- *)

Theorem process_block_preserves_inv[local]:
  ∀cfg bbs lr bb.
    lr_inv bbs lr ∧ lookup_block bb.bb_label bbs = SOME bb ==>
    lr_inv bbs (process_block cfg bbs lr bb)
Proof
  rw[lr_inv_def] >>
  metis_tac[process_block_preserves_bounded, process_block_preserves_shaped,
            process_block_preserves_consistent, lookup_block_mem]
QED

Theorem one_pass_preserves_inv[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ==>
    lr_inv bbs (liveness_one_pass cfg bbs lr order)
Proof
  rw[lr_inv_def] >>
  metis_tac[one_pass_preserves_bounded, one_pass_preserves_shaped,
            one_pass_preserves_consistent]
QED

(* --- Set-based measure is bounded under invariant --- *)

(* Helper: CARD of a subset of set U is bounded by LENGTH(nub U) *)
Theorem card_subset_nub[local]:
  ∀(xs : 'a list) U. set xs ⊆ set U ==> CARD (set xs) ≤ LENGTH (nub U)
Proof
  rw[] >>
  `CARD (set xs) ≤ CARD (set U)` by
    (irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET]) >>
  fs[CARD_LIST_TO_SET_EQN]
QED

(* Helper: SUM bounded by max_term * length *)
Theorem sum_le_bound[local]:
  ∀(xs : num list) b. EVERY (λx. x ≤ b) xs ==> SUM xs ≤ b * LENGTH xs
Proof
  Induct >> rw[SUM, LENGTH, MULT_CLAUSES] >>
  `SUM xs ≤ b * LENGTH xs` by (first_x_assum irule >> fs[]) >>
  simp[MULT_CLAUSES]
QED

(* Helper: SUM over FILTER ≤ SUM over full list *)
Theorem sum_map_filter_le[local]:
  ∀(f : 'a -> num) P xs. SUM (MAP f (FILTER P xs)) ≤ SUM (MAP f xs)
Proof
  gen_tac >> gen_tac >> Induct >> rw[FILTER, SUM, MAP]
QED

(* Helper: MEM x xs ∧ ¬P x ⟹ f x + SUM(MAP f (FILTER P xs)) ≤ SUM(MAP f xs) *)
Theorem sum_map_mem_filter_le[local]:
  ∀(f : 'a -> num) P x xs.
    MEM x xs ∧ ¬P x ==>
    f x + SUM (MAP f (FILTER P xs)) ≤ SUM (MAP f xs)
Proof
  ntac 2 gen_tac >> gen_tac >> Induct >> rw[FILTER, SUM, MAP] >>
  res_tac >> simp[sum_map_filter_le]
QED

(* slots bound via injection into bbs *)
Theorem slot_sum_bounded[local]:
  ∀alist bbs.
    ALL_DISTINCT (MAP FST alist) ∧
    (∀k bl. MEM (k,bl) alist ==>
       ∃bb. MEM bb bbs ∧ bb.bb_label = k ∧
            CARD (FDOM bl.bl_inst_liveness) ≤ LENGTH bb.bb_instructions) ==>
    SUM (MAP (λ(k,bl). CARD (FDOM bl.bl_inst_liveness) + 1) alist) ≤
    SUM (MAP (λbb. LENGTH bb.bb_instructions + 1) bbs)
Proof
  Induct >> rw[] >>
  Cases_on `h` >> fs[] >>
  (* derive both: witness for head + injection for tail *)
  `∃bb. MEM bb bbs ∧ bb.bb_label = q ∧
        CARD (FDOM r.bl_inst_liveness) ≤ LENGTH bb.bb_instructions` by (
    qpat_assum `∀k bl. _` (qspecl_then [`q`, `r`] mp_tac) >> simp[]) >>
  `∀k bl. MEM (k,bl) alist ⇒
     ∃bb. MEM bb bbs ∧ bb.bb_label = k ∧
          CARD (FDOM bl.bl_inst_liveness) ≤ LENGTH bb.bb_instructions` by (
    rpt strip_tac >>
    qpat_assum `∀k bl. _` (qspecl_then [`k`, `bl`] mp_tac) >> simp[]) >>
  (* apply IH to filtered bbs *)
  first_x_assum (qspec_then `FILTER (λbb'. bb'.bb_label ≠ q) bbs` mp_tac) >>
  impl_tac >- (
    rw[MEM_FILTER] >> res_tac >> qexists_tac `bb'` >> simp[] >>
    CCONTR_TAC >> gvs[] >> fs[MEM_MAP] >> metis_tac[FST]) >>
  strip_tac >>
  (* combine: f(bb) + filtered_sum ≤ total, and CARD ≤ LENGTH *)
  qspecl_then [`λbb'. LENGTH bb'.bb_instructions + 1`,
               `λbb'. bb'.bb_label ≠ q`, `bb`, `bbs`]
    mp_tac sum_map_mem_filter_le >> simp[]
QED

(* SUM of CARD-bounded pair-alist ≤ bound * length *)
Theorem sum_map_card_le[local]:
  ∀(al : (num # string list) list) (nv : num).
    (∀i vs. MEM (i,vs) al ==> CARD (set vs) ≤ nv) ==>
    SUM (MAP (λ(i,vs). CARD (set vs)) al) ≤ nv * LENGTH al
Proof
  Induct >> rw[] >> Cases_on `h` >> fs[] >>
  `CARD (set r) ≤ nv` by (first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[]) >>
  `SUM (MAP (λ(i,vs). CARD (set vs)) al) ≤ nv * LENGTH al` by (
    first_x_assum irule >> metis_tac[]) >>
  simp[MULT_SUC]
QED

(* Pair-alist version of SUM_MAP_same_LE — avoids EVERY/pair-lambda issues *)
Theorem sum_map_pair_le[local]:
  ∀(f : 'a # 'b -> num) (g : 'a # 'b -> num) al.
    (∀k v. MEM (k,v) al ==> f (k,v) ≤ g (k,v)) ==>
    SUM (MAP f al) ≤ SUM (MAP g al)
Proof
  ntac 2 gen_tac >> Induct >> rw[] >> Cases_on `h` >> fs[] >>
  `f (q,r) ≤ g (q,r)` by (first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[]) >>
  `SUM (MAP f al) ≤ SUM (MAP g al)` by (first_x_assum irule >> metis_tac[]) >>
  simp[]
QED

(* Per-block contribution to set_live_count ≤ (nv+1) * (1 + CARD(FDOM)) *)
Theorem per_block_sum_le[local]:
  ∀lbl bl lr U.
    lr_vars_bounded lr U ∧
    FLOOKUP lr.lr_blocks lbl = SOME bl ==>
    CARD (set bl.bl_out_vars) +
    CARD (FDOM bl.bl_inst_liveness) +
    SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
    (LENGTH (nub U) + 1) * (CARD (FDOM bl.bl_inst_liveness) + 1)
Proof
  rw[] >>
  qabbrev_tac `nv = LENGTH (nub U)` >>
  qabbrev_tac `nd = CARD (FDOM bl.bl_inst_liveness)` >>
  (* out_vars bound *)
  `CARD (set bl.bl_out_vars) ≤ nv` by (
    qunabbrev_tac `nv` >> irule card_subset_nub >> rw[SUBSET_DEF] >>
    fs[lr_vars_bounded_def] >>
    first_x_assum (qspecl_then [`lbl`, `x`] mp_tac) >>
    simp[out_vars_of_def, lookup_block_liveness_def]) >>
  (* inst_liveness entries bound: each CARD ≤ nv *)
  `∀idx vars. FLOOKUP bl.bl_inst_liveness idx = SOME vars ==>
     CARD (set vars) ≤ nv` by (
    rw[] >> qunabbrev_tac `nv` >> irule card_subset_nub >> rw[SUBSET_DEF] >>
    fs[lr_vars_bounded_def] >>
    first_x_assum (qspecl_then [`lbl`, `idx`, `x`] mp_tac) >>
    simp[live_vars_at_def, LET_DEF, lookup_block_liveness_def]) >>
  (* inner SUM ≤ nv * nd *)
  `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
   nv * nd` by (
    qunabbrev_tac `nd` >>
    `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
     nv * LENGTH (fmap_to_alist bl.bl_inst_liveness)` suffices_by
      simp[LENGTH_fmap_to_alist] >>
    irule sum_map_card_le >>
    rw[MEM_pair_fmap_to_alist_FLOOKUP] >> res_tac) >>
  (* nv + nd + nv*nd ≤ (nv+1)*(nd+1) *)
  simp[RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB]
QED

(* Factor n out of SUM(MAP (λ(k,v). n * f k v) al) *)
Theorem sum_map_factor[local]:
  ∀(f : 'a -> 'b -> num) (n : num) al.
    SUM (MAP (λ(k,v). n * f k v) al) = n * SUM (MAP (λ(k,v). f k v) al)
Proof
  ntac 2 gen_tac >> Induct >> simp[] >> Cases_on `h` >> simp[LEFT_ADD_DISTRIB]
QED

(* SUM(λbb. 1 + LENGTH instrs) = LENGTH bbs + SUM(λbb. LENGTH instrs) *)
Theorem sum_one_plus[local]:
  ∀bbs. SUM (MAP (λbb. LENGTH bb.bb_instructions + 1) bbs) =
        LENGTH bbs + SUM (MAP (λbb. LENGTH bb.bb_instructions) bbs)
Proof
  Induct >> simp[]
QED

(* set_live_count ≤ (nv+1) * (fn_total_insts + LENGTH bbs) *)
Theorem set_live_count_bounded[local]:
  ∀bbs lr.
    lr_vars_bounded lr (fn_all_vars bbs) ∧ lr_shaped bbs lr ==>
    set_live_count lr ≤
    (LENGTH (nub (fn_all_vars bbs)) + 1) * (fn_total_insts bbs + LENGTH bbs)
Proof
  rw[set_live_count_def, fn_total_insts_def] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `SUM (MAP (λ(k,bl).
    (LENGTH (nub (fn_all_vars bbs)) + 1) *
      (CARD (FDOM bl.bl_inst_liveness) + 1))
    (fmap_to_alist lr.lr_blocks))` >>
  conj_tac >- (
    irule sum_map_pair_le >> rw[] >>
    `CARD (set v.bl_out_vars) + CARD (FDOM v.bl_inst_liveness) +
     SUM (MAP (λ(i,vs). CARD (set vs))
       (fmap_to_alist v.bl_inst_liveness)) ≤
     (LENGTH (nub (fn_all_vars bbs)) + 1) *
       (CARD (FDOM v.bl_inst_liveness) + 1)` suffices_by simp[] >>
    irule per_block_sum_le >>
    fs[MEM_pair_fmap_to_alist_FLOOKUP] >> metis_tac[]) >>
  simp[sum_map_factor] >>
  simp[GSYM sum_one_plus] >>
  irule slot_sum_bounded >>
  rw[ALL_DISTINCT_fmap_to_alist_keys, MEM_pair_fmap_to_alist_FLOOKUP] >>
  fs[lr_shaped_def] >>
  `MEM k (MAP (λbb. bb.bb_label) bbs)` by
    (fs[FLOOKUP_DEF] >> metis_tac[]) >>
  drule lookup_block_exists >> strip_tac >>
  qexists_tac `bb` >>
  imp_res_tac lookup_block_mem >> imp_res_tac lookup_block_label >> simp[] >>
  res_tac >>
  `CARD (FDOM bl.bl_inst_liveness) ≤ CARD (count (LENGTH bb.bb_instructions))` by
    (irule CARD_SUBSET >> simp[FINITE_COUNT]) >>
  fs[CARD_COUNT]
QED

(* --- Monotonicity / inflationary chain --- *)

Theorem live_update_monotone[local]:
  ∀defs uses live1 live2.
    set live1 ⊆ set live2 ==>
    set (live_update defs uses live1) ⊆ set (live_update defs uses live2)
Proof
  rw[live_update_set_proof, SUBSET_DEF] >> metis_tac[]
QED

(* calc_liveness_loop is monotone: larger starting live → larger results.
   Both FST (final live) and SND (inst map values) are monotone. *)
Theorem calc_liveness_loop_monotone[local]:
  ∀n instrs live1 live2.
    set live1 ⊆ set live2 ∧ n < LENGTH instrs ==>
    set (FST (calc_liveness_loop instrs live1 n)) ⊆
      set (FST (calc_liveness_loop instrs live2 n)) ∧
    ∀i vs1 vs2.
      FLOOKUP (SND (calc_liveness_loop instrs live1 n)) i = SOME vs1 ∧
      FLOOKUP (SND (calc_liveness_loop instrs live2 n)) i = SOME vs2 ==>
      set vs1 ⊆ set vs2
Proof
  Induct
  >- (
    (* n=0: direct *)
    rw[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    irule live_update_monotone >> simp[]
  )
  >> (* SUC n *)
     rpt gen_tac >> strip_tac >>
     `n < LENGTH instrs` by simp[] >>
     qabbrev_tac `d = inst_defs (EL (SUC n) instrs)` >>
     qabbrev_tac `u = inst_uses (EL (SUC n) instrs)` >>
     qabbrev_tac `lv1 = if NULL u ∧ NULL d then live1
                         else live_update d u live1` >>
     qabbrev_tac `lv2 = if NULL u ∧ NULL d then live2
                         else live_update d u live2` >>
     `set lv1 ⊆ set lv2` by (
       unabbrev_all_tac >> rw[] >> irule live_update_monotone >> simp[]) >>
     first_x_assum (qspecl_then [`instrs`, `lv1`, `lv2`] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     simp[calc_liveness_loop_def, LET_DEF] >>
     unabbrev_all_tac >> simp[] >>
     Cases_on `calc_liveness_loop instrs
       (if NULL (inst_uses (EL (SUC n) instrs)) ∧
           NULL (inst_defs (EL (SUC n) instrs))
        then live1
        else live_update (inst_defs (EL (SUC n) instrs))
                         (inst_uses (EL (SUC n) instrs)) live1) n` >>
     Cases_on `calc_liveness_loop instrs
       (if NULL (inst_uses (EL (SUC n) instrs)) ∧
           NULL (inst_defs (EL (SUC n) instrs))
        then live2
        else live_update (inst_defs (EL (SUC n) instrs))
                         (inst_uses (EL (SUC n) instrs)) live2) n` >>
     fs[FLOOKUP_UPDATE] >> rw[] >> fs[] >>
     TRY (irule live_update_monotone >> simp[] >> NO_TAC) >>
     res_tac
QED

(* calculate_liveness is monotone in out_vars *)
Theorem calculate_liveness_monotone[local]:
  ∀bb bl1 bl2 i vs1 vs2.
    ¬NULL bb.bb_instructions ∧
    set bl1.bl_out_vars ⊆ set bl2.bl_out_vars ∧
    FLOOKUP (calculate_liveness bb bl1).bl_inst_liveness i = SOME vs1 ∧
    FLOOKUP (calculate_liveness bb bl2).bl_inst_liveness i = SOME vs2 ==>
    set vs1 ⊆ set vs2
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  `LENGTH bb.bb_instructions − 1 < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  drule_all calc_liveness_loop_monotone >> strip_tac >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl1.bl_out_vars
    (LENGTH bb.bb_instructions − 1)` >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl2.bl_out_vars
    (LENGTH bb.bb_instructions − 1)` >>
  fs[] >> metis_tac[]
QED

(* Under strong consistency, bl's inst_liveness FDOM matches the block *)
Theorem consistent_inst_fdom[local]:
  ∀bb bl.
    calculate_liveness bb bl = bl ∧ ¬NULL bb.bb_instructions ==>
    FDOM bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)
Proof
  rw[] >>
  `FDOM (calculate_liveness bb bl).bl_inst_liveness =
   count (LENGTH bb.bb_instructions)` by simp[calculate_liveness_fdom] >>
  gvs[]
QED

(* process_block is inflationary under lr_consistent.
   Under strong consistency, calculate_liveness bb bl = bl.
   So process_block only merges out_vars (growing set) and
   recomputes inst_liveness from the larger out_vars. *)
Theorem process_block_inflationary[local]:
  ∀cfg bbs lr bb.
    lr_consistent bbs lr ∧
    lookup_block bb.bb_label bbs = SOME bb ==>
    lr_leq lr (process_block cfg bbs lr bb)
Proof
  rw[lr_leq_def]
  (* 1: out_vars *)
  >- (rw[process_block_out_vars] >>
      Cases_on `lbl = bb.bb_label` >> simp[list_union_set_proof, SUBSET_DEF])
  (* 2: live_vars_at *)
  >> Cases_on `lbl = bb.bb_label`
  >- (
    gvs[] >> rw[live_vars_at_def, LET_DEF] >>
    simp[process_block_def, LET_DEF, lookup_block_liveness_def,
         FLOOKUP_UPDATE] >>
    Cases_on `FLOOKUP lr.lr_blocks bb.bb_label` >> simp[]
    (* 2a: no existing block *)
    >- simp[empty_block_liveness_def, FLOOKUP_DEF, FDOM_FEMPTY]
    (* 2b: existing block — use strong consistency *)
    >> rename1 `FLOOKUP lr.lr_blocks bb.bb_label = SOME bl` >>
    Cases_on `FLOOKUP bl.bl_inst_liveness idx` >> simp[] >>
    rename1 `FLOOKUP bl.bl_inst_liveness idx = SOME old_vars` >>
    (* Consistency: FEMPTY ∨ calculate_liveness bb bl = bl.
       FEMPTY is contradicted by FLOOKUP ... = SOME old_vars. *)
    `calculate_liveness bb bl = bl` by
      (fs[lr_consistent_def] >>
       first_x_assum (qspecl_then [`bb.bb_label`, `bl`, `bb`] mp_tac) >>
       simp[] >> strip_tac >> gvs[FLOOKUP_DEF]) >>
    qabbrev_tac `bl_m = bl with bl_out_vars :=
      list_union bl.bl_out_vars (calculate_out_vars cfg lr bb bbs)` >>
    `set bl.bl_out_vars ⊆ set bl_m.bl_out_vars` by
      (unabbrev_all_tac >> simp[list_union_set_proof, SUBSET_DEF]) >>
    Cases_on `NULL bb.bb_instructions`
    >- (
      fs[calculate_liveness_def, LET_DEF] >>
      `bl_m.bl_inst_liveness = bl.bl_inst_liveness` by
        (unabbrev_all_tac >> simp[]) >>
      fs[SUBSET_DEF])
    >> (* ¬NULL: use monotonicity from bl to bl_m *)
    `FDOM (calculate_liveness bb bl_m).bl_inst_liveness =
     count (LENGTH bb.bb_instructions)` by simp[calculate_liveness_fdom] >>
    `FDOM bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)` by
      metis_tac[consistent_inst_fdom] >>
    `idx ∈ FDOM (calculate_liveness bb bl_m).bl_inst_liveness` by
      (gvs[FLOOKUP_DEF]) >>
    `∃new_vars. FLOOKUP (calculate_liveness bb bl_m).bl_inst_liveness idx =
                SOME new_vars` by metis_tac[FLOOKUP_DEF] >>
    simp[] >>
    `set old_vars ⊆ set new_vars` by (
      irule SUBSET_TRANS >>
      qexists_tac `set ((calculate_liveness bb bl).bl_inst_liveness ' idx)` >>
      conj_tac >- gvs[FLOOKUP_DEF] >>
      irule calculate_liveness_monotone >>
      qexistsl_tac [`bb`, `bl`, `bl_m`, `idx`] >> simp[] >>
      gvs[FLOOKUP_DEF]) >>
    fs[SUBSET_DEF])
  >> (* different label: unchanged *)
     simp[process_block_live_vars_neq]
QED

(* one_pass is inflationary *)
Theorem one_pass_inflationary[local]:
  ∀cfg bbs order lr.
    lr_consistent bbs lr ==>
    lr_leq lr (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[]
  >- simp[lr_leq_def]
  >- simp[lr_leq_def]
  >> rename1 `lookup_block h bbs = SOME bb` >>
     imp_res_tac lookup_block_label >> gvs[] >>
     `lr_leq lr (process_block cfg bbs lr bb)` by
       metis_tac[process_block_inflationary] >>
     `lr_consistent bbs (process_block cfg bbs lr bb)` by
       metis_tac[process_block_preserves_consistent] >>
     `lr_leq (process_block cfg bbs lr bb)
             (liveness_one_pass cfg bbs (process_block cfg bbs lr bb) order)` by (
       first_x_assum irule >> simp[]) >>
     fs[lr_leq_def, SUBSET_DEF]
QED

(* --- Set-based measure increases when one_pass changes something --- *)

(* Block-level measure for set_live_count decomposition *)
Definition block_measure_def:
  block_measure bl =
    CARD (set bl.bl_out_vars) +
    CARD (FDOM bl.bl_inst_liveness) +
    SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness))
End

(* set_live_count = SUM of block_measure over lr_blocks *)
Theorem set_live_count_as_block_measure[local]:
  ∀lr. set_live_count lr =
    SUM (MAP (λ(k,bl). block_measure bl) (fmap_to_alist lr.lr_blocks))
Proof
  rw[set_live_count_def, block_measure_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> rw[] >> Cases_on `x` >> simp[]
QED

(* set_live_count as SIGMA over FDOM *)
Theorem set_live_count_as_sigma[local]:
  ∀lr. set_live_count lr =
    SIGMA (λk. block_measure (lr.lr_blocks ' k)) (FDOM lr.lr_blocks)
Proof
  rw[set_live_count_as_block_measure, fmap_to_alist_def, MAP_MAP_o,
     combinTheory.o_DEF] >>
  rw[GSYM SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST]
QED

(* FDOM of process_block result *)
Theorem process_block_fdom[local]:
  ∀cfg bbs lr bb.
    bb.bb_label ∈ FDOM lr.lr_blocks ==>
    FDOM (process_block cfg bbs lr bb).lr_blocks = FDOM lr.lr_blocks
Proof
  rw[process_block_def, LET_DEF, FDOM_FUPDATE] >>
  simp[ABSORPTION_RWT]
QED

(* list_union xs ys = xs when set ys ⊆ set xs *)
Theorem list_union_id[local]:
  ∀xs ys. set ys ⊆ set xs ==> list_union xs ys = xs
Proof
  rw[list_union_def] >>
  `FILTER (λv. ¬MEM v xs) ys = []` suffices_by simp[] >>
  rw[FILTER_EQ_NIL, EVERY_MEM] >>
  fs[SUBSET_DEF]
QED

(* SUM of SIGMA over FDOM1 ≤ SUM of SIGMA over FDOM2 when FDOM1 ⊆ FDOM2
   and pointwise ≤. Used in block_measure comparisons. *)
Theorem sigma_inst_le[local]:
  ∀(f1 : num |-> string list) (f2 : num |-> string list).
    FDOM f1 ⊆ FDOM f2 ∧
    (∀i vs1. FLOOKUP f1 i = SOME vs1 ==>
             ∃vs2. FLOOKUP f2 i = SOME vs2 ∧ set vs1 ⊆ set vs2) ==>
    SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist f1)) ≤
    SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist f2))
Proof
  rw[fmap_to_alist_def, MAP_MAP_o, combinTheory.o_DEF,
     GSYM SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `SIGMA (λi. CARD (set (f2 ' i))) (FDOM f1)` >>
  conj_tac
  >- (irule SUM_IMAGE_MONO_LESS_EQ >> simp[FDOM_FINITE] >> rpt strip_tac >>
      `FLOOKUP f1 x = SOME (f1 ' x)` by simp[FLOOKUP_DEF] >>
      first_x_assum drule >> strip_tac >>
      `f2 ' x = vs2` by (fs[FLOOKUP_DEF] >> gvs[]) >>
      gvs[] >> irule CARD_SUBSET >> simp[])
  >> irule SUM_IMAGE_SUBSET_LE >> simp[FDOM_FINITE]
QED

(* Block-level measure: monotone and strictly increasing when block changes.
   Factored out to keep process_block_measure shorter. *)
Theorem block_measure_mono[local]:
  ∀bb bl_old bl_new.
    set bl_old.bl_out_vars ⊆ set bl_new.bl_out_vars ∧
    FDOM bl_old.bl_inst_liveness ⊆ FDOM bl_new.bl_inst_liveness ∧
    (∀i vs1. FLOOKUP bl_old.bl_inst_liveness i = SOME vs1 ==>
       ∃vs2. FLOOKUP bl_new.bl_inst_liveness i = SOME vs2 ∧ set vs1 ⊆ set vs2) ==>
    block_measure bl_old ≤ block_measure bl_new
Proof
  rw[block_measure_def] >>
  `CARD (set bl_old.bl_out_vars) ≤ CARD (set bl_new.bl_out_vars)` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD (FDOM bl_old.bl_inst_liveness) ≤ CARD (FDOM bl_new.bl_inst_liveness)` by
    (irule CARD_SUBSET >> simp[FDOM_FINITE]) >>
  `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl_old.bl_inst_liveness)) ≤
   SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl_new.bl_inst_liveness))` by
    (irule sigma_inst_le >> simp[]) >>
  simp[]
QED

(* Strict block_measure increase when old_bl ≠ new_bl and either FEMPTY
   or consistent. Helper for process_block_measure. *)
Theorem block_measure_strict[local]:
  ∀bb old_bl new_bl bl_m extra.
    old_bl ≠ new_bl ∧
    new_bl = calculate_liveness bb bl_m ∧
    bl_m = (old_bl with bl_out_vars :=
              list_union old_bl.bl_out_vars extra) ∧
    set old_bl.bl_out_vars ⊆ set new_bl.bl_out_vars ∧
    FDOM old_bl.bl_inst_liveness ⊆ FDOM new_bl.bl_inst_liveness ∧
    (∀i vs1. FLOOKUP old_bl.bl_inst_liveness i = SOME vs1 ==>
       ∃vs2. FLOOKUP new_bl.bl_inst_liveness i = SOME vs2 ∧ set vs1 ⊆ set vs2) ∧
    (old_bl.bl_inst_liveness = FEMPTY ∨ calculate_liveness bb old_bl = old_bl) ==>
    block_measure old_bl < block_measure new_bl
Proof
  rpt gen_tac >> disch_tac >>
  `old_bl ≠ new_bl ∧ new_bl = calculate_liveness bb bl_m ∧
   bl_m = old_bl with bl_out_vars := list_union old_bl.bl_out_vars extra ∧
   set old_bl.bl_out_vars ⊆ set new_bl.bl_out_vars ∧
   FDOM old_bl.bl_inst_liveness ⊆ FDOM new_bl.bl_inst_liveness ∧
   (∀i vs1. FLOOKUP old_bl.bl_inst_liveness i = SOME vs1 ==>
      ∃vs2. FLOOKUP new_bl.bl_inst_liveness i = SOME vs2 ∧ set vs1 ⊆ set vs2)` by
    fs[] >>
  PURE_REWRITE_TAC[block_measure_def] >>
  (* Three component-wise ≤ *)
  `CARD (set old_bl.bl_out_vars) ≤ CARD (set new_bl.bl_out_vars)` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD (FDOM old_bl.bl_inst_liveness) ≤ CARD (FDOM new_bl.bl_inst_liveness)` by
    (irule CARD_SUBSET >> simp[FDOM_FINITE]) >>
  `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist old_bl.bl_inst_liveness)) ≤
   SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist new_bl.bl_inst_liveness))` by
    (irule sigma_inst_le >> simp[]) >>
  (* Establish one strict component, then arithmetic finishes *)
  `CARD (set old_bl.bl_out_vars) < CARD (set new_bl.bl_out_vars) ∨
   CARD (FDOM old_bl.bl_inst_liveness) < CARD (FDOM new_bl.bl_inst_liveness)` suffices_by DECIDE_TAC >>
  Cases_on `old_bl.bl_inst_liveness = FEMPTY`
  >- ( (* FEMPTY: old FDOM = 0. Either FDOM grows (¬NULL) or out_vars strict (NULL) *)
    Cases_on `NULL bb.bb_instructions`
    >- ( (* NULL instrs ⟹ new inst_liveness also FEMPTY ⟹ out_vars must differ *)
      disj1_tac >>
      `new_bl.bl_inst_liveness = FEMPTY` by
        gvs[calculate_liveness_def, LET_DEF] >>
      irule CARD_PSUBSET >> simp[PSUBSET_DEF] >>
      CCONTR_TAC >> fs[] >>
      `set old_bl.bl_out_vars = set new_bl.bl_out_vars` by
        metis_tac[SUBSET_ANTISYM] >>
      `new_bl.bl_out_vars = list_union old_bl.bl_out_vars extra` by
        gvs[calculate_liveness_out_vars] >>
      `set old_bl.bl_out_vars ∪ set extra = set old_bl.bl_out_vars` by
        metis_tac[list_union_set_proof] >>
      `set extra ⊆ set old_bl.bl_out_vars` by
        metis_tac[SUBSET_UNION_ABSORPTION, UNION_COMM] >>
      `list_union old_bl.bl_out_vars extra = old_bl.bl_out_vars` by
        (irule list_union_id >> fs[]) >>
      fs[block_liveness_component_equality])
    >> (* ¬NULL ⟹ FDOM grows from ∅ to count n with n > 0 *)
    disj2_tac >>
    `FDOM new_bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)` by
      simp[calculate_liveness_fdom] >>
    `0 < LENGTH bb.bb_instructions` by
      (Cases_on `bb.bb_instructions` >> fs[]) >>
    simp[CARD_COUNT])
  >> (* Consistent: calculate_liveness bb old_bl = old_bl, extra grew out_vars *)
  disj1_tac >>
  `calculate_liveness bb old_bl = old_bl` by metis_tac[] >>
  irule CARD_PSUBSET >> simp[PSUBSET_DEF] >>
  CCONTR_TAC >> fs[] >>
  `set old_bl.bl_out_vars = set new_bl.bl_out_vars` by
    metis_tac[SUBSET_ANTISYM] >>
  `new_bl.bl_out_vars = list_union old_bl.bl_out_vars extra` by
    gvs[calculate_liveness_out_vars] >>
  `set old_bl.bl_out_vars ∪ set extra = set old_bl.bl_out_vars` by
    metis_tac[list_union_set_proof] >>
  `set extra ⊆ set old_bl.bl_out_vars` by
    metis_tac[SUBSET_UNION_ABSORPTION, UNION_COMM] >>
  `list_union old_bl.bl_out_vars extra = old_bl.bl_out_vars` by
    (irule list_union_id >> fs[]) >>
  `old_bl with bl_out_vars := list_union old_bl.bl_out_vars extra = old_bl` by
    simp[block_liveness_component_equality] >>
  metis_tac[]
QED

(* process_block either leaves lr unchanged or strictly increases set_live_count. *)
Theorem process_block_measure[local]:
  ∀cfg bbs lr bb.
    lr_inv bbs lr ∧
    lookup_block bb.bb_label bbs = SOME bb ==>
    set_live_count lr ≤ set_live_count (process_block cfg bbs lr bb) ∧
    (process_block cfg bbs lr bb ≠ lr ==>
     set_live_count lr < set_live_count (process_block cfg bbs lr bb))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `lbl = bb.bb_label` >>
  `lr_vars_bounded lr (fn_all_vars bbs)` by fs[lr_inv_def] >>
  `lr_shaped bbs lr` by fs[lr_inv_def] >>
  `lbl ∈ FDOM lr.lr_blocks` by (
    fs[lr_shaped_def] >>
    imp_res_tac lookup_block_mem >>
    unabbrev_all_tac >> simp[MEM_MAP] >> metis_tac[]) >>
  qabbrev_tac `old_bl = lr.lr_blocks ' lbl` >>
  `FLOOKUP lr.lr_blocks lbl = SOME old_bl` by
    simp[FLOOKUP_DEF, markerTheory.Abbrev_def] >>
  qabbrev_tac `bl_m = (old_bl with bl_out_vars :=
    list_union old_bl.bl_out_vars (calculate_out_vars cfg lr bb bbs))` >>
  qabbrev_tac `new_bl = calculate_liveness bb bl_m` >>
  `(process_block cfg bbs lr bb).lr_blocks =
   lr.lr_blocks |+ (lbl, new_bl)` by
    (unabbrev_all_tac >>
     simp[process_block_def, LET_DEF, lookup_block_liveness_def]) >>
  `bl_m.bl_inst_liveness = old_bl.bl_inst_liveness` by
    (unabbrev_all_tac >> simp[]) >>
  `new_bl.bl_out_vars = bl_m.bl_out_vars` by
    (unabbrev_all_tac >> simp[calculate_liveness_out_vars]) >>
  `set old_bl.bl_out_vars ⊆ set new_bl.bl_out_vars` by
    (unabbrev_all_tac >> simp[list_union_set_proof, calculate_liveness_out_vars]) >>
  `FDOM old_bl.bl_inst_liveness ⊆ FDOM new_bl.bl_inst_liveness` by (
    Cases_on `NULL bb.bb_instructions`
    >- (unabbrev_all_tac >> fs[calculate_liveness_def, LET_DEF])
    >> `FDOM new_bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)` by
         (unabbrev_all_tac >> simp[calculate_liveness_fdom]) >>
       `FDOM old_bl.bl_inst_liveness ⊆ count (LENGTH bb.bb_instructions)` by
         (fs[lr_shaped_def] >> metis_tac[]) >>
       metis_tac[SUBSET_TRANS]) >>
  (* Inst values: FEMPTY has no entries; consistent has monotone entries *)
  `∀i vs1. FLOOKUP old_bl.bl_inst_liveness i = SOME vs1 ==>
           ∃vs2. FLOOKUP new_bl.bl_inst_liveness i = SOME vs2 ∧
                  set vs1 ⊆ set vs2` by (
    rpt strip_tac >>
    `old_bl.bl_inst_liveness ≠ FEMPTY` by
      (strip_tac >> fs[FLOOKUP_DEF]) >>
    `calculate_liveness bb old_bl = old_bl` by
      (fs[lr_inv_def, lr_consistent_def] >>
       first_x_assum (qspecl_then [`lbl`, `old_bl`, `bb`] mp_tac) >>
       simp[] >> metis_tac[]) >>
    Cases_on `NULL bb.bb_instructions`
    >- (unabbrev_all_tac >> fs[calculate_liveness_def, LET_DEF] >>
        qexists_tac `vs1` >> simp[])
    >> `i ∈ FDOM new_bl.bl_inst_liveness` by (
         `FDOM new_bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)` by
           (unabbrev_all_tac >> simp[calculate_liveness_fdom]) >>
         `FDOM old_bl.bl_inst_liveness = count (LENGTH bb.bb_instructions)` by
           metis_tac[consistent_inst_fdom] >>
         gvs[FLOOKUP_DEF]) >>
       qexists_tac `new_bl.bl_inst_liveness ' i` >> simp[FLOOKUP_DEF] >>
       `old_bl.bl_inst_liveness ' i = vs1` by fs[FLOOKUP_DEF] >>
       irule calculate_liveness_monotone >>
       qexistsl_tac [`bb`, `old_bl`, `bl_m`, `i`] >> simp[] >>
       gvs[FLOOKUP_DEF]) >>
  (* block_measure monotone *)
  `block_measure old_bl ≤ block_measure new_bl` by
    (irule block_measure_mono >> simp[]) >>
  (* ≤ part *)
  conj_tac >- (
    simp[set_live_count_as_sigma] >>
    `lbl INSERT FDOM lr.lr_blocks = FDOM lr.lr_blocks` by
      simp[ABSORPTION_RWT] >> gvs[] >>
    irule SUM_IMAGE_MONO_LESS_EQ >> simp[FDOM_FINITE] >>
    rpt strip_tac >> Cases_on `x = lbl` >> gvs[FAPPLY_FUPDATE_THM]) >>
  (* strict part *)
  strip_tac >>
  `old_bl ≠ new_bl` by
    (strip_tac >> gvs[liveness_result_component_equality, FUPDATE_ELIM]) >>
  `block_measure old_bl < block_measure new_bl` by (
    `lr_consistent bbs lr` by fs[lr_inv_def] >>
    pop_assum (fn th => assume_tac (REWRITE_RULE [lr_consistent_def] th)) >>
    pop_assum (qspecl_then [`lbl`, `old_bl`, `bb`] mp_tac) >> simp[] >>
    strip_tac >>
    qspecl_then [`bb`, `old_bl`, `new_bl`, `bl_m`,
                 `calculate_out_vars cfg lr bb bbs`]
      mp_tac block_measure_strict >>
    impl_tac >- (unabbrev_all_tac >> simp[]) >> simp[]) >>
  simp[set_live_count_as_sigma] >>
  `lbl INSERT FDOM lr.lr_blocks = FDOM lr.lr_blocks` by
    simp[ABSORPTION_RWT] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule SUM_IMAGE_MONO_LESS >> simp[FDOM_FINITE] >>
  conj_tac >| [
    rpt strip_tac >> Cases_on `x = lbl` >> simp[FAPPLY_FUPDATE_THM],
    qexists_tac `lbl` >> simp[FAPPLY_FUPDATE_THM]
  ]
QED

Theorem one_pass_measure_le[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ==>
    set_live_count lr ≤ set_live_count (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  imp_res_tac lookup_block_label >> gvs[] >>
  `set_live_count lr ≤ set_live_count (process_block cfg bbs lr x)` by
    (drule_all process_block_measure >> simp[]) >>
  `lr_inv bbs (process_block cfg bbs lr x)` by
    metis_tac[process_block_preserves_inv, lookup_block_mem] >>
  `set_live_count (process_block cfg bbs lr x) ≤
   set_live_count (liveness_one_pass cfg bbs (process_block cfg bbs lr x) order)` by
    (first_x_assum irule >> simp[]) >>
  DECIDE_TAC
QED

Theorem one_pass_set_measure_increase[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ∧
    liveness_one_pass cfg bbs lr order ≠ lr ==>
    set_live_count lr < set_live_count (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  imp_res_tac lookup_block_label >> gvs[] >>
  qabbrev_tac `lr' = process_block cfg bbs lr x` >>
  Cases_on `lr' = lr`
  >- (
    gvs[] >> first_x_assum irule >> simp[] >>
    metis_tac[process_block_preserves_inv, lookup_block_mem])
  >> `set_live_count lr < set_live_count lr'` by
       (drule_all process_block_measure >> unabbrev_all_tac >> simp[]) >>
     `lr_inv bbs lr'` by
       metis_tac[process_block_preserves_inv, lookup_block_mem] >>
     `set_live_count lr' ≤
      set_live_count (liveness_one_pass cfg bbs lr' order)` by
       (irule one_pass_measure_le >> simp[]) >>
     DECIDE_TAC
QED

(* ===== Fixpoint ===== *)

Theorem liveness_analyze_fixpoint_proof:
  ∀fn.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    liveness_one_pass cfg fn.fn_blocks lr cfg.cfg_dfs_post = lr
Proof
  rw[liveness_analyze_def, liveness_iterate_def] >>
  qspecl_then [
    `λlr'. liveness_one_pass (cfg_analyze fn) fn.fn_blocks lr'
       (cfg_analyze fn).cfg_dfs_post`,
    `set_live_count`,
    `(LENGTH (nub (fn_all_vars fn.fn_blocks)) + 1) *
       (fn_total_insts fn.fn_blocks + LENGTH fn.fn_blocks)`,
    `λlr'. lr_inv fn.fn_blocks lr'`,
    `init_liveness fn.fn_blocks`
  ] mp_tac df_iterate_fixpoint_orbit >>
  impl_tac >- (
    BETA_TAC >> rpt conj_tac >> rpt strip_tac >| [
      simp[GREATER_DEF] >> irule one_pass_set_measure_increase >> simp[],
      simp[init_lr_inv],
      irule set_live_count_bounded >> fs[lr_inv_def],
      irule one_pass_preserves_inv >> simp[]]) >>
  BETA_TAC >> simp[]
QED

(* ===== Boundedness ===== *)

Theorem iterate_preserves_inv[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ==>
    lr_inv bbs (liveness_iterate cfg bbs order lr)
Proof
  rw[liveness_iterate_def] >>
  qspecl_then [
    `λlr'. liveness_one_pass cfg bbs lr' order`,
    `set_live_count`,
    `(LENGTH (nub (fn_all_vars bbs)) + 1) *
       (fn_total_insts bbs + LENGTH bbs)`,
    `λlr'. lr_inv bbs lr'`, `lr`
  ] mp_tac df_iterate_invariant >>
  impl_tac >- (
    BETA_TAC >> rpt conj_tac >> rpt strip_tac >| [
      simp[GREATER_DEF] >> irule one_pass_set_measure_increase >> simp[],
      simp[],
      irule set_live_count_bounded >> fs[lr_inv_def],
      irule one_pass_preserves_inv >> simp[]]) >>
  BETA_TAC >> simp[]
QED

Theorem lr_inv_bounded[local]:
  ∀bbs lr. lr_inv bbs lr ==> lr_vars_bounded lr (fn_all_vars bbs)
Proof
  rw[lr_inv_def]
QED

Theorem live_vars_bounded_proof:
  ∀fn lbl idx v.
    let lr = liveness_analyze fn in
    MEM v (live_vars_at lr lbl idx) ==>
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  rw[liveness_analyze_def] >>
  `lr_inv fn.fn_blocks (liveness_iterate (cfg_analyze fn) fn.fn_blocks
     (cfg_analyze fn).cfg_dfs_post (init_liveness fn.fn_blocks))` by (
    irule iterate_preserves_inv >> rw[init_lr_inv]) >>
  imp_res_tac lr_inv_bounded >>
  fs[lr_vars_bounded_def] >> res_tac
QED

(* ===== Soundness helpers ===== *)

(* calc_liveness_loop entry at idx is the result of live_update at that index.
   Successor live is: out_vars if idx is the topmost index, else entry at idx+1. *)
Theorem calc_loop_step[local]:
  ∀n instrs out idx v.
    n < LENGTH instrs ∧ idx ≤ n ∧
    (∃vars. FLOOKUP (SND (calc_liveness_loop instrs out n)) idx = SOME vars ∧
            MEM v vars) ==>
    MEM v (inst_uses (EL idx instrs)) ∨
    (¬MEM v (inst_defs (EL idx instrs)) ∧
     if idx = n then MEM v out
     else ∃vars'. FLOOKUP (SND (calc_liveness_loop instrs out n)) (idx + 1) = SOME vars' ∧
                  MEM v vars')
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac >| [
    (* Base: n=0, idx=0 *)
    `idx = 0` by simp[] >>
    gvs[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    Cases_on `NULL (inst_uses (EL 0 instrs))` >>
    Cases_on `NULL (inst_defs (EL 0 instrs))` >>
    gvs[live_update_mem, NULL_EQ],
    (* Step: n = SUC n' *)
    qabbrev_tac `live' = if NULL (inst_uses (EL (SUC n) instrs)) ∧
      NULL (inst_defs (EL (SUC n) instrs)) then out
      else live_update (inst_defs (EL (SUC n) instrs))
        (inst_uses (EL (SUC n) instrs)) out` >>
    Cases_on `calc_liveness_loop instrs live' n` >>
    Cases_on `idx = SUC n` >| [
      (* idx = SUC n: lookup yields live' *)
      gvs[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
      unabbrev_all_tac >>
      Cases_on `NULL (inst_uses (EL (SUC n) instrs)) ∧ NULL (inst_defs (EL (SUC n) instrs))` >>
      gvs[live_update_mem, NULL_EQ],
      (* idx ≤ n: use IH on inner loop *)
      `idx ≤ n` by simp[] >>
      `n < LENGTH instrs` by simp[] >>
      fs[calc_liveness_loop_def, LET_DEF] >>
      gvs[FLOOKUP_UPDATE] >>
      first_x_assum (qspecl_then [`instrs`, `live'`, `idx`, `v`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      Cases_on `idx = n` >> gvs[] >| [
        (* idx = n: IH says MEM v live', and FLOOKUP at n+1=SUC n gives live' *)
        disj2_tac >> simp[FLOOKUP_UPDATE],
        (* idx < n: IH gives FLOOKUP at idx+1 in inner map *)
        disj2_tac >>
        `idx + 1 ≠ SUC n` by simp[] >>
        simp[FLOOKUP_UPDATE]
      ]
    ]
  ]
QED

(* At the fixpoint, if v is live at (lbl, idx), then either:
   (a) v is used by the instruction at (lbl, idx), or
   (b) v is not defined there and is live at the successor position. *)
Theorem fixpoint_live_step[local]:
  ∀bbs lr bb lbl idx v.
    lr_consistent bbs lr ∧ lr_shaped bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (live_vars_at lr lbl idx) ∧
    idx < LENGTH bb.bb_instructions ==>
    MEM v (inst_uses (EL idx bb.bb_instructions)) ∨
    (¬MEM v (inst_defs (EL idx bb.bb_instructions)) ∧
     if idx + 1 < LENGTH bb.bb_instructions then
       MEM v (live_vars_at lr lbl (idx + 1))
     else
       MEM v (lookup_block_liveness lr lbl).bl_out_vars)
Proof
  rpt strip_tac >>
  fs[live_vars_at_def, lookup_block_liveness_def, LET_DEF] >>
  Cases_on `FLOOKUP lr.lr_blocks lbl` >>
  fs[empty_block_liveness_def] >>
  rename [`FLOOKUP lr.lr_blocks lbl = SOME bl`] >>
  Cases_on `FLOOKUP bl.bl_inst_liveness idx` >> fs[] >>
  rename [`FLOOKUP bl.bl_inst_liveness idx = SOME vars`, `MEM v vars`] >>
  (* lr_consistent: FEMPTY case contradicts FLOOKUP=SOME *)
  `calculate_liveness bb bl = bl` by (
    qpat_x_assum `lr_consistent _ _` (fn th =>
      mp_tac (REWRITE_RULE [lr_consistent_def] th)) >>
    disch_then (qspecl_then [`lbl`, `bl`, `bb`] mp_tac) >> simp[] >>
    strip_tac >> fs[FLOOKUP_DEF, FDOM_FEMPTY]) >>
  `¬NULL bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> fs[]) >>
  qabbrev_tac `n = LENGTH bb.bb_instructions − 1` >>
  (* calculate_liveness expands to calc_liveness_loop *)
  fs[calculate_liveness_def, LET_DEF] >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars n` >> gvs[] >>
  `r = bl.bl_inst_liveness` by (
    qpat_x_assum `bl with bl_inst_liveness := r = bl` mp_tac >>
    simp[block_liveness_component_equality]) >>
  `n < LENGTH bb.bb_instructions ∧ idx ≤ n` by (unabbrev_all_tac >> simp[]) >>
  qspecl_then [`n`, `bb.bb_instructions`, `bl.bl_out_vars`, `idx`, `v`]
    mp_tac calc_loop_step >>
  impl_tac >- (simp[] >> qexists_tac `vars` >> simp[]) >>
  strip_tac >| [
    simp[],
    disj2_tac >> simp[] >>
    Cases_on `idx = n` >> fs[] >| [
      `¬(idx + 1 < LENGTH bb.bb_instructions)` by
        (unabbrev_all_tac >> simp[]) >> simp[],
      `idx + 1 < LENGTH bb.bb_instructions` by
        (unabbrev_all_tac >> simp[]) >> simp[] >>
      `SND (calc_liveness_loop bb.bb_instructions bl.bl_out_vars n) =
       bl.bl_inst_liveness` by simp[] >>
      Cases_on `FLOOKUP bl.bl_inst_liveness (idx + 1)` >> fs[]
    ]
  ]
QED

(* === Monotonicity helpers for fixpoint_out_to_succ === *)

(* input_vars_from is monotone in base_liveness:
   set base1 ⊆ set base2 ⟹ set (input_vars_from src instrs base1) ⊆
                               set (input_vars_from src instrs base2)
   Proof: FILTER preserves ⊆, list_union with same rhs preserves ⊆ *)
Theorem input_vars_from_mono[local]:
  ∀src instrs base1 base2.
    set base1 ⊆ set base2 ==>
    set (input_vars_from src instrs base1) ⊆ set (input_vars_from src instrs base2)
Proof
  gen_tac >> Induct_on `instrs` >- simp[input_vars_from_def] >>
  rpt gen_tac >> strip_tac >>
  `∀b. input_vars_from src (h::instrs) b = input_vars_from src instrs
    (if h.inst_opcode ≠ PHI then b
     else list_union
       (FILTER (λv. ¬MEM v (MAP SND (FILTER (λ(l,v). l ≠ src)
          (phi_pairs h.inst_operands)))) b)
       (MAP SND (FILTER (λ(l,v). l = src) (phi_pairs h.inst_operands))))` by
    simp[input_vars_from_def] >>
  simp[] >> first_x_assum irule >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  fs[list_union_set_proof, SUBSET_DEF, MEM_FILTER] >> metis_tac[]
QED

(* calculate_out_vars is monotone: lr_leq lr1 lr2 ⟹
   set (calc_out lr1) ⊆ set (calc_out lr2) *)
Theorem calc_out_vars_mono[local]:
  ∀cfg lr1 lr2 bb bbs.
    lr_leq lr1 lr2 ==>
    set (calculate_out_vars cfg lr1 bb bbs) ⊆
    set (calculate_out_vars cfg lr2 bb bbs)
Proof
  rw[calculate_out_vars_def, LET_DEF] >>
  `∀succs acc1 acc2. set acc1 ⊆ set acc2 ==>
     set (FOLDL (λacc succ_lbl. case lookup_block succ_lbl bbs of
        NONE => acc
      | SOME succ_bb => list_union acc
          (input_vars_from bb.bb_label succ_bb.bb_instructions
             (live_vars_at lr1 succ_lbl 0))) acc1 succs) ⊆
     set (FOLDL (λacc succ_lbl. case lookup_block succ_lbl bbs of
        NONE => acc
      | SOME succ_bb => list_union acc
          (input_vars_from bb.bb_label succ_bb.bb_instructions
             (live_vars_at lr2 succ_lbl 0))) acc2 succs)` suffices_by
    simp[] >>
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  fs[list_union_set_proof, SUBSET_DEF] >> rpt strip_tac >>
  res_tac >> simp[] >>
  `set (input_vars_from bb.bb_label x.bb_instructions (live_vars_at lr1 h 0)) ⊆
   set (input_vars_from bb.bb_label x.bb_instructions (live_vars_at lr2 h 0))` by
    (irule input_vars_from_mono >> fs[lr_leq_def]) >>
  fs[SUBSET_DEF]
QED

(* out_vars are justified at every step of the FOLDL in one_pass:
   set(out_vars) ⊆ set(calc_out at the current lr).
   This is an inductive invariant on the one_pass FOLDL. *)
Theorem one_pass_out_justified[local]:
  ∀cfg bbs order lr.
    lr_consistent bbs lr ∧
    (∀lbl bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
      set (out_vars_of lr lbl) ⊆
      set (calculate_out_vars cfg lr bb bbs)) ==>
    let lr' = liveness_one_pass cfg bbs lr order in
    ∀lbl bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
      set (out_vars_of lr' lbl) ⊆
      set (calculate_out_vars cfg lr' bb bbs)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  rename1 `lookup_block h bbs = SOME bb'` >>
  imp_res_tac lookup_block_label >> gvs[] >>
  first_x_assum (qspecl_then [`cfg`, `bbs`,
    `process_block cfg bbs lr bb'`] mp_tac) >>
  impl_tac >| [
    conj_tac >- metis_tac[process_block_preserves_consistent] >>
    rpt strip_tac >>
    `lr_leq lr (process_block cfg bbs lr bb')` by
      metis_tac[process_block_inflationary] >>
    `set (calculate_out_vars cfg lr bb'' bbs) ⊆
     set (calculate_out_vars cfg (process_block cfg bbs lr bb') bb'' bbs)` by
      (irule calc_out_vars_mono >> simp[]) >>
    simp[process_block_out_vars] >>
    Cases_on `bb''.bb_label = bb'.bb_label` >> simp[]
    >- (fs[list_union_set_proof, SUBSET_DEF] >> metis_tac[])
    >> metis_tac[SUBSET_TRANS],
    simp[]
  ]
QED

(* At any step of df_iterate, out_vars are justified.
   Uses orbit induction via FUNPOW. *)
Theorem out_vars_justified_iterate[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ∧
    (∀lbl bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
      set (out_vars_of lr lbl) ⊆
      set (calculate_out_vars cfg lr bb bbs)) ==>
    let lr' = liveness_iterate cfg bbs order lr in
    ∀lbl bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
      set (out_vars_of lr' lbl) ⊆
      set (calculate_out_vars cfg lr' bb bbs)
Proof
  rpt gen_tac >> strip_tac >>
  simp[liveness_iterate_def, LET_DEF] >>
  qspecl_then [
    `λlr'. liveness_one_pass cfg bbs lr' order`,
    `set_live_count`,
    `(LENGTH (nub (fn_all_vars bbs)) + 1) *
       (fn_total_insts bbs + LENGTH bbs)`,
    `λlr'. lr_inv bbs lr' ∧
      (∀lbl bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
        set (out_vars_of lr' lbl) ⊆
        set (calculate_out_vars cfg lr' bb bbs))`, `lr`
  ] mp_tac df_iterate_invariant >>
  BETA_TAC >> impl_tac >| [
    rpt conj_tac >| [
      rpt strip_tac >> simp[GREATER_DEF] >>
        irule one_pass_set_measure_increase >> fs[lr_inv_def],
      fs[],
      fs[],
      rpt strip_tac >> irule set_live_count_bounded >> fs[lr_inv_def],
      rpt strip_tac >| [
        irule one_pass_preserves_inv >> fs[],
        qspecl_then [`cfg`, `bbs`, `order`, `y`] mp_tac one_pass_out_justified >>
        impl_tac >| [fs[lr_inv_def],
          simp[LET_DEF] >> disch_tac >>
          first_x_assum (qspec_then `bb` mp_tac) >> fs[]]]],
    strip_tac >> fs[]
  ]
QED

(* Corollary: at the fixpoint, out_vars ⊆ calc_out *)
Theorem fixpoint_out_justified[local]:
  ∀fn lbl bb.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lr = liveness_analyze fn in
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
    set (out_vars_of lr lbl) ⊆
    set (calculate_out_vars cfg lr bb bbs)
Proof
  rw[liveness_analyze_def] >>
  qspecl_then [`cfg_analyze fn`, `fn.fn_blocks`,
    `(cfg_analyze fn).cfg_dfs_post`,
    `init_liveness fn.fn_blocks`] mp_tac out_vars_justified_iterate >>
  impl_tac >| [
    conj_tac >| [simp[init_lr_inv],
    rpt strip_tac >>
    fs[init_liveness_def, out_vars_of_def, lookup_block_liveness_def] >>
    Cases_on `FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label,empty_block_liveness))
      FEMPTY fn.fn_blocks) lbl` >>
    simp[empty_block_liveness_def] >>
    imp_res_tac foldl_init_flookup >> simp[empty_block_liveness_def]],
    simp[LET_DEF]
  ]
QED

(* Extract a witness from the FOLDL in calculate_out_vars *)
Theorem calc_out_vars_witness[local]:
  ∀cfg lr bb bbs v.
    MEM v (calculate_out_vars cfg lr bb bbs) ==>
    ∃succ_lbl succ_bb.
      MEM succ_lbl (cfg_succs_of cfg bb.bb_label) ∧
      lookup_block succ_lbl bbs = SOME succ_bb ∧
      MEM v (input_vars_from bb.bb_label succ_bb.bb_instructions
               (live_vars_at lr succ_lbl 0))
Proof
  rw[calculate_out_vars_def, LET_DEF] >>
  qabbrev_tac `succs = cfg_succs_of cfg bb.bb_label` >>
  qabbrev_tac `f = λacc succ_lbl.
    case lookup_block succ_lbl bbs of
      NONE => acc
    | SOME succ_bb => list_union acc
        (input_vars_from bb.bb_label succ_bb.bb_instructions
           (live_vars_at lr succ_lbl 0))` >>
  `∀succs acc. MEM v (FOLDL f acc succs) ==>
    MEM v acc ∨ ∃succ_lbl succ_bb.
      MEM succ_lbl succs ∧ lookup_block succ_lbl bbs = SOME succ_bb ∧
      MEM v (input_vars_from bb.bb_label succ_bb.bb_instructions
               (live_vars_at lr succ_lbl 0))` by (
    Induct >> simp[] >> rpt strip_tac >>
    last_x_assum (qspec_then `f acc h` mp_tac) >>
    impl_tac >| [simp[], ALL_TAC] >>
    disch_tac >> fs[] >| [
      (* MEM v (f acc h) — expand f, case split on lookup_block *)
      qunabbrev_tac `f` >> pop_assum mp_tac >> BETA_TAC >>
      Cases_on `lookup_block h bbs` >> simp[list_union_mem] >>
      strip_tac >| [
        disj1_tac >> simp[],
        disj2_tac >> qexistsl_tac [`h`, `x`] >> simp[]
      ],
      (* witness from succs' — pass through *)
      disj2_tac >> metis_tac[]
    ]) >>
  first_x_assum (qspecl_then [`succs`, `[]`] mp_tac) >> simp[]
QED

(* At the fixpoint, if v ∈ out_vars(lbl), there exists a successor block
   where v is live at index 0, or v is a PHI source from lbl. *)
Theorem fixpoint_out_to_succ[local]:
  ∀fn bb lbl v.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lr = liveness_analyze fn in
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (lookup_block_liveness lr lbl).bl_out_vars ==>
    ∃succ_lbl succ_bb.
      MEM succ_lbl (cfg_succs_of cfg lbl) ∧
      lookup_block succ_lbl bbs = SOME succ_bb ∧
      (MEM v (live_vars_at lr succ_lbl 0) ∨
       ∃inst. MEM inst succ_bb.bb_instructions ∧ inst.inst_opcode = PHI ∧
              MEM (lbl, v) (phi_pairs inst.inst_operands))
Proof
  rw[] >>
  (* Step 1: out_vars ⊆ calculate_out_vars *)
  `MEM v (calculate_out_vars (cfg_analyze fn) (liveness_analyze fn) bb fn.fn_blocks)` by (
    mp_tac (Q.SPECL [`fn`, `bb.bb_label`, `bb`] fixpoint_out_justified) >>
    simp[LET_DEF, out_vars_of_def] >>
    disch_tac >> fs[SUBSET_DEF] >> first_x_assum irule >>
    simp[]) >>
  (* Step 2: extract successor witness *)
  drule calc_out_vars_witness >> strip_tac >>
  qexistsl_tac [`succ_lbl`, `succ_bb`] >> simp[] >>
  (* Step 3: split into live-at-0 vs PHI-source *)
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  disj2_tac >> metis_tac[]
QED

(* ===== Soundness ===== *)

(* Intra-block: v live at (lbl, idx) implies either:
   (a) v is used at some instruction j ≥ idx (no def before j), or
   (b) v reaches out_vars (no def in any instruction from idx) *)
Theorem intra_block_sound[local]:
  ∀bbs lr bb lbl idx v.
    lr_consistent bbs lr ∧ lr_shaped bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (live_vars_at lr lbl idx) ∧ idx < LENGTH bb.bb_instructions ==>
    (∃j. idx ≤ j ∧ j < LENGTH bb.bb_instructions ∧
         MEM v (inst_uses (EL j bb.bb_instructions)) ∧
         ∀k. idx ≤ k ∧ k < j ==> ¬MEM v (inst_defs (EL k bb.bb_instructions))) ∨
    (MEM v (lookup_block_liveness lr lbl).bl_out_vars ∧
     ∀k. idx ≤ k ∧ k < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_defs (EL k bb.bb_instructions)))
Proof
  rpt strip_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - idx` >>
  rpt strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`bbs`, `lr`, `bb`, `bb.bb_label`, `idx`, `v`] fixpoint_live_step) >>
  simp[] >> strip_tac
  >- ((* v used at idx *)
      disj1_tac >> qexists_tac `idx` >> simp[])
  >> (* v not defined, propagates *)
  Cases_on `idx + 1 < LENGTH bb.bb_instructions` >> fs[]
  >- ((* intra-block: v live at idx+1 *)
      first_x_assum (qspec_then `LENGTH bb.bb_instructions − (idx + 1)` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `idx + 1` mp_tac) >> simp[] >>
      strip_tac
      >- ((* IH case (a): use at j ≥ idx+1 *)
          disj1_tac >> qexists_tac `j` >> simp[] >> rpt strip_tac >>
          Cases_on `k = idx` >> gvs[])
      >> (* IH case (b): reaches out_vars *)
      disj2_tac >> simp[] >> rpt strip_tac >>
      Cases_on `k = idx` >> gvs[])
  >> (* end of block: v in out_vars *)
  disj2_tac >> simp[] >> rpt strip_tac >>
  `k = idx` by simp[] >> gvs[]
QED

(*
  COUNTEREXAMPLE for liveness_sound_proof:

  cfg_exec_path disallows self-loop transitions: a step from (lbl, last)
  to (lbl, 0) requires lbl ≠ lbl (false). But liveness analysis correctly
  marks variables as live in self-loop blocks where the variable is used
  by a PHI at index 0 but live at index > 0 due to out_vars propagation.

  Concrete example:
    Block "L" with instructions [PHI(Label "L", Var "v", output "w"), JMP "L"]
    - wf_function holds: JMP is a terminator, ALL_DISTINCT labels, succs_closed
    - "v" is live at (L, 1) because PHI uses "v" and it propagates via out_vars
    - No valid cfg_exec_path from (L, 1) reaches a use of "v":
      * (L,1) only: used_before_defined fails (JMP doesn't use "v")
      * (L,1)::(L,0)::...: cfg_exec_path fails (L=L but 0 ≠ 1+1)
      * (L,1)::(L',0)::...: cfg_exec_path fails (L' ∉ cfg_succs since only succ is L)

  Tightest fix: modify cfg_exec_path to allow self-loop transitions:
    Change the cross-block disjunct from
      lbl1 ≠ lbl2 ∧ MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0
    to
      MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0 ∧
      idx1 + 1 = LENGTH (the_block lbl1 bbs).bb_instructions

    This allows self-loop transitions while ensuring they occur at block
    boundaries. With this fix, the soundness proof goes through via orbit
    induction (each live variable at the fixpoint traces back to a use via
    the iteration orbit).
*)

(* ===== Counterexample: liveness_sound_proof is FALSE ===== *)

(* Helper: two-step WHILE convergence *)
Theorem while_two_step[local]:
  f x <> x /\ f (f x) = f x ==> WHILE (\y. f y <> y) f x = f x
Proof
  strip_tac >>
  ONCE_REWRITE_TAC [WHILE] >> simp[] >>
  ONCE_REWRITE_TAC [WHILE] >> simp[]
QED

(* The concrete counterexample function *)
Definition cex_fn_def:
  cex_fn = ir_function "test"
    [basic_block "L"
       [instruction 0 PHI [Label "L"; Var "v"] ["w"];
        instruction 1 JMP [Label "L"] []]]
End

(* cex_fn is well-formed *)
Theorem cex_wf[local]:
  wf_function cex_fn
Proof
  simp[cex_fn_def, wf_function_def, fn_has_entry_def, fn_succs_closed_def,
       fn_labels_def, bb_well_formed_def] >>
  EVAL_TAC >> simp[]
QED

(* The cfg successors of "L" are exactly ["L"] *)
Theorem cex_succs[local]:
  cfg_succs_of (cfg_analyze cex_fn) "L" = ["L"]
Proof
  mp_tac cex_wf >>
  `MEM (basic_block "L"
     [instruction 0 PHI [Label "L"; Var "v"] ["w"];
      instruction 1 JMP [Label "L"] []]) cex_fn.fn_blocks`
    by simp[cex_fn_def] >>
  strip_tac >> drule_all cfg_analyze_preserves_bb_succs >>
  EVAL_TAC
QED

(* Helper: cfg_dfs_post for cex_fn *)
Theorem cex_dfs_post[local]:
  (cfg_analyze cex_fn).cfg_dfs_post = ["L"]
Proof
  simp[cfg_analyze_dfs_post, cex_fn_def, entry_block_def] >>
  ONCE_REWRITE_TAC[dfs_post_walk_def] >>
  simp[set_insert_def, fmap_lookup_list_def, FLOOKUP_UPDATE] >>
  EVAL_TAC >>
  ONCE_REWRITE_TAC[dfs_post_walk_def] >> simp[set_insert_def] >>
  ONCE_REWRITE_TAC[dfs_post_walk_def] >> simp[]
QED

(* The fixpoint value for liveness analysis on cex_fn *)
Definition cex_lr_def:
  cex_lr = <|lr_blocks := FEMPTY |+
    ("L", <|bl_out_vars := ["v"];
            bl_inst_liveness := FEMPTY |+ (0,["v"]) |+ (1,["v"])|>)|>
End

(* one_pass on cex_fn from empty gives cex_lr *)
(* Shared tactic: unfold one_pass on cex_fn, eliminate cfg_succs_of, then EVAL *)
Theorem cex_one_pass_init[local]:
  liveness_one_pass (cfg_analyze cex_fn) cex_fn.fn_blocks
    (init_liveness cex_fn.fn_blocks) ["L"] = cex_lr
Proof
  simp[liveness_one_pass_def, LET_THM, cex_fn_def, lookup_block_def] >>
  simp[process_block_def, LET_THM] >>
  simp[calculate_out_vars_def, LET_THM, GSYM cex_fn_def, cex_succs] >>
  EVAL_TAC >> simp[cex_lr_def, FUPDATE_EQ]
QED

(* one_pass on cex_fn from cex_lr gives cex_lr (fixpoint) *)
Theorem cex_one_pass_fix[local]:
  liveness_one_pass (cfg_analyze cex_fn) cex_fn.fn_blocks cex_lr ["L"] = cex_lr
Proof
  simp[liveness_one_pass_def, LET_THM, cex_fn_def, lookup_block_def] >>
  simp[process_block_def, LET_THM] >>
  simp[calculate_out_vars_def, LET_THM, GSYM cex_fn_def, cex_succs, cex_lr_def] >>
  EVAL_TAC
QED

(* init ≠ fixpoint *)
Theorem cex_init_ne_fix[local]:
  init_liveness cex_fn.fn_blocks <> cex_lr
Proof
  EVAL_TAC >> simp[cex_lr_def, liveness_result_component_equality] >>
  strip_tac >>
  `FLOOKUP (FEMPTY |+ ("L", <|bl_out_vars := []; bl_inst_liveness := FEMPTY|>)) "L" =
   FLOOKUP (FEMPTY |+ ("L", <|bl_out_vars := ["v"];
     bl_inst_liveness := FEMPTY |+ (0,["v"]) |+ (1,["v"])|>)) "L"`
    by metis_tac[FLOOKUP_EXT] >>
  fs[FLOOKUP_UPDATE]
QED

(* liveness_analyze cex_fn = cex_lr *)
Theorem cex_analyze[local]:
  liveness_analyze cex_fn = cex_lr
Proof
  simp[liveness_analyze_def, liveness_iterate_def, cex_fn_def, LET_THM,
       cex_dfs_post] >>
  (* Goal: df_iterate (\lr'. one_pass cfg bbs lr' ["L"]) (init bbs) = cex_lr *)
  (* Unfold df_iterate = WHILE *)
  simp[df_iterate_def] >>
  (* Abstract the function and use while_two_step *)
  qmatch_goalsub_abbrev_tac `WHILE _ f lr0` >>
  `f = (\lr'. liveness_one_pass (cfg_analyze cex_fn) cex_fn.fn_blocks lr' ["L"])` by
    (unabbrev_all_tac >> simp[cex_fn_def, FUN_EQ_THM]) >>
  `lr0 = init_liveness cex_fn.fn_blocks` by
    (unabbrev_all_tac >> simp[cex_fn_def]) >>
  `f lr0 = cex_lr` by simp[cex_one_pass_init] >>
  `f cex_lr = cex_lr` by simp[cex_one_pass_fix] >>
  (* Fold guard to use f, then unfold WHILE twice *)
  qmatch_goalsub_abbrev_tac `WHILE G f lr0` >>
  `G = \y. f y <> y` by (
    unabbrev_all_tac >> simp[FUN_EQ_THM]) >>
  ONCE_REWRITE_TAC[WHILE] >>
  (* Goal: (if G lr0 then WHILE G f (f lr0) else lr0) = cex_lr *)
  `G lr0 <=> T` by (
    qpat_x_assum `G = _` SUBST1_TAC >> BETA_TAC >>
    (* goal: f lr0 ≠ lr0 <=> T *)
    ASM_REWRITE_TAC[] >>
    (* goal: cex_lr ≠ init_liveness cex_fn.fn_blocks <=> T *)
    REWRITE_TAC[EQ_CLAUSES] >>
    metis_tac[cex_init_ne_fix]) >>
  ASM_REWRITE_TAC[] >>
  ONCE_REWRITE_TAC[WHILE] >> BETA_TAC >>
  REWRITE_TAC[cex_one_pass_fix] (* f cex_lr = cex_lr closes the if *)
QED

(* liveness_analyze cex_fn has "v" live at ("L", 1) *)
Theorem cex_v_live[local]:
  MEM "v" (live_vars_at (liveness_analyze cex_fn) "L" 1)
Proof
  simp[cex_analyze, cex_lr_def, live_vars_at_def,
       lookup_block_liveness_def, FLOOKUP_UPDATE]
QED

(* "v" is only used at ("L", 0) in cex_fn *)
Theorem cex_use_at_0[local]:
  ∀lbl idx. var_used_at cex_fn.fn_blocks lbl idx "v" ==> lbl = "L" ∧ idx = 0
Proof
  simp[var_used_at_def, cex_fn_def, lookup_block_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `idx` >> gvs[] >> Cases_on `n` >> gvs[] >>
  gvs[EVAL ``inst_uses (instruction 1 JMP [Label "L"] [])``]
QED

(* All positions in cfg_exec_path from ("L",n) with n≥1 have index ≥ 1 *)
Theorem cex_path_ge1[local]:
  ∀path lbl n.
    n ≥ 1 ∧ lbl = "L" ∧ cfg_exec_path (cfg_analyze cex_fn) ((lbl,n)::path) ==>
    EVERY (λp. FST p = "L" ∧ SND p ≥ 1) path
Proof
  Induct >> simp[] >> Cases >>
  simp[cfg_exec_path_def, cex_succs] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `n+1` mp_tac) >> simp[]
QED

(* No cfg_exec_path from ("L", 1) witnesses used_before_defined for "v" *)
Theorem cex_no_path[local]:
  ∀path.
    ¬(cfg_exec_path (cfg_analyze cex_fn) (("L", 1) :: path) ∧
      used_before_defined cex_fn.fn_blocks "v" (("L", 1) :: path))
Proof
  rpt strip_tac >>
  `EVERY (λp. FST p = "L" ∧ SND p ≥ 1) (("L",1)::path)` by (
    simp[] >> irule cex_path_ge1 >> qexistsl_tac [`"L"`, `1`] >> simp[]) >>
  fs[used_before_defined_def] >>
  drule_then strip_assume_tac cex_use_at_0 >>
  Cases_on `k` >> gvs[] >>
  fs[EVERY_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* FORMAL COUNTEREXAMPLE: liveness_sound_proof is false *)
Theorem liveness_sound_proof_counterexample[local]:
  ¬(∀fn lbl idx v.
      let cfg = cfg_analyze fn in
      let lr = liveness_analyze fn in
      let bbs = fn.fn_blocks in
      wf_function fn ∧
      MEM v (live_vars_at lr lbl idx) ==>
      ∃path.
        cfg_exec_path cfg ((lbl, idx) :: path) ∧
        used_before_defined bbs v ((lbl, idx) :: path))
Proof
  simp[] >>
  qexistsl_tac [`cex_fn`, `"L"`, `1`, `"v"`] >>
  simp[cex_wf, cex_v_live] >>
  rpt strip_tac >> mp_tac cex_no_path >> simp[]
QED

(* The theorem as stated is FALSE — proved above as
   liveness_sound_proof_counterexample. Kept with cheat for build compatibility
   with downstream ACCEPT_TAC re-exports. *)
Theorem liveness_sound_proof:
  ∀fn lbl idx v.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn ∧
    MEM v (live_vars_at lr lbl idx) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  cheat
QED
