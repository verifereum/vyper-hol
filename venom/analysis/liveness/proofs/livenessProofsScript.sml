(*
 * Liveness Analysis — Internal Correctness Proofs
 *
 * Proofs are re-exported via livenessAnalysisPropsScript.sml.
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs dfIterateProofs

open listTheory pred_setTheory arithmeticTheory venomInstTheory finite_mapTheory
     pairTheory alistTheory sptreeTheory

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
    (∀lbl bl. FLOOKUP lr.lr_blocks lbl = SOME bl ==>
       ∃bb. MEM bb bbs ∧ bb.bb_label = lbl ∧
            FDOM bl.bl_inst_liveness ⊆ count (LENGTH bb.bb_instructions)) ∧
    FDOM lr.lr_blocks ⊆ set (MAP (λbb. bb.bb_label) bbs)
End

(* Consistency: inst_liveness entries are ⊆ what calculate_liveness
   would produce from current out_vars (using lookup_block). *)
Definition lr_consistent_def:
  lr_consistent bbs lr ⇔
    ∀lbl bl bb i vars.
      FLOOKUP lr.lr_blocks lbl = SOME bl ∧
      lookup_block lbl bbs = SOME bb ∧
      FLOOKUP bl.bl_inst_liveness i = SOME vars ==>
      ∃vars'.
        FLOOKUP (calculate_liveness bb bl).bl_inst_liveness i = SOME vars' ∧
        set vars ⊆ set vars'
End

(* Combined convergence invariant: bounded + shaped + consistent *)
Definition lr_inv_def:
  lr_inv bbs lr ⇔
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    lr_shaped bbs lr ∧
    lr_consistent bbs lr
End

(* Set-based measure: counts CARD of sets instead of LENGTH of lists.
   Unlike total_live_count (which uses list lengths), this is bounded
   under lr_vars_bounded alone, without needing ALL_DISTINCT. *)
Definition set_live_count_def:
  set_live_count lr =
    SUM (MAP (λ(k,bl). CARD (set bl.bl_out_vars) +
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
  gvs[empty_block_liveness_def, FDOM_FEMPTY, MEM_MAP] >> metis_tac[]
QED

Theorem init_liveness_consistent[local]:
  ∀bbs. lr_consistent bbs (init_liveness bbs)
Proof
  rw[lr_consistent_def, init_liveness_def] >>
  imp_res_tac foldl_init_flookup >>
  fs[empty_block_liveness_def, FLOOKUP_DEF, FDOM_FEMPTY]
QED

Theorem init_lr_inv[local]:
  ∀bbs. lr_inv bbs (init_liveness bbs)
Proof
  rw[lr_inv_def, init_liveness_bounded, init_liveness_shaped,
     init_liveness_consistent]
QED

(* --- Shape preservation --- *)

(* calc_liveness_loop produces FDOM ⊆ count(n+1) *)
Theorem calc_liveness_loop_fdom[local]:
  ∀instrs live n.
    n < LENGTH instrs ==>
    FDOM (SND (calc_liveness_loop instrs live n)) ⊆ count (n + 1)
Proof
  Induct_on `n` >>
  rw[calc_liveness_loop_def, LET_DEF, FDOM_FUPDATE, FDOM_FEMPTY] >> (
    `n < LENGTH instrs` by simp[] >>
    qmatch_goalsub_abbrev_tac `calc_liveness_loop instrs lv n` >>
    first_x_assum (qspecl_then [`instrs`, `lv`] mp_tac) >> simp[] >>
    strip_tac >>
    Cases_on `calc_liveness_loop instrs lv n` >>
    fs[FDOM_FUPDATE, SUBSET_DEF] >> rw[] >> res_tac >> simp[]
  )
QED

Theorem calculate_liveness_fdom[local]:
  ∀bb bl.
    ¬NULL bb.bb_instructions ==>
    FDOM (calculate_liveness bb bl).bl_inst_liveness ⊆
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
    lr_shaped bbs lr ∧ MEM bb bbs ==>
    lr_shaped bbs (process_block cfg bbs lr bb)
Proof
  rw[lr_shaped_def, process_block_def, LET_DEF, FDOM_FUPDATE,
     FLOOKUP_UPDATE] >>
  TRY (fs[SUBSET_DEF, MEM_MAP] >> metis_tac[] >> NO_TAC)
  >- (
    Cases_on `lbl = bb.bb_label` >> fs[]
    >- (
      Cases_on `NULL bb.bb_instructions`
      >- (
        (* NULL instrs: calculate_liveness = identity, use old witness *)
        rw[calculate_liveness_def] >>
        rw[lookup_block_liveness_def] >>
        Cases_on `FLOOKUP lr.lr_blocks bb.bb_label` >> fs[FDOM_FEMPTY]
        >- (qexists_tac `bb` >> simp[empty_block_liveness_def, FDOM_FEMPTY])
        >> res_tac >> metis_tac[]
      )
      >> (* non-NULL: calculate_liveness_fdom gives bound, witness bb *)
         qexists_tac `bb` >> rw[calculate_liveness_fdom]
    )
    >> res_tac >> metis_tac[]
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
  metis_tac[lookup_block_mem]
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
  Cases_on `lbl = bb.bb_label` >> fs[]
  >- (
    (* same label: bb' = bb, bl = calculate_liveness bb bl'.
       Goal: ∃vars'. FLOOKUP (calculate_liveness bb bl)... = SOME vars' ∧ ...
       Subst bl, use idempotency, get back FLOOKUP bl... = SOME vars. *)
    gvs[calculate_liveness_idempotent] >>
    qexists_tac `vars` >> simp[]
  )
  >> (* different label: use lr_consistent directly *)
     first_x_assum (qspecl_then [`lbl`, `bl`, `bb'`, `i`, `vars`] mp_tac) >>
     simp[]
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

(* Per-block contribution to set_live_count ≤ nv * (1 + CARD(FDOM inst_liveness)) *)
Theorem per_block_sum_le[local]:
  ∀lbl bl lr U.
    lr_vars_bounded lr U ∧
    FLOOKUP lr.lr_blocks lbl = SOME bl ==>
    CARD (set bl.bl_out_vars) +
    SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
    LENGTH (nub U) * (CARD (FDOM bl.bl_inst_liveness) + 1)
Proof
  rw[] >>
  qabbrev_tac `nv = LENGTH (nub U)` >>
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
  (* inner SUM ≤ nv * CARD(FDOM inst_liveness) *)
  `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
   nv * CARD (FDOM bl.bl_inst_liveness)` by (
    `SUM (MAP (λ(i,vs). CARD (set vs)) (fmap_to_alist bl.bl_inst_liveness)) ≤
     nv * LENGTH (fmap_to_alist bl.bl_inst_liveness)` suffices_by
      simp[LENGTH_fmap_to_alist] >>
    irule sum_map_card_le >>
    rw[MEM_pair_fmap_to_alist_FLOOKUP] >> res_tac) >>
  simp[]
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

(* set_live_count sums per-block; slot_sum_bounded bounds the slot count *)
Theorem set_live_count_bounded[local]:
  ∀bbs lr.
    lr_inv bbs lr ==>
    set_live_count lr ≤ all_var_slots bbs
Proof
  rw[lr_inv_def, set_live_count_def, all_var_slots_def, LET_DEF, fn_total_insts_def] >>
  (* Step 1: per-block bound *)
  irule LESS_EQ_TRANS >>
  qexists_tac `SUM (MAP (λ(k,bl).
    LENGTH (nub (fn_all_vars bbs)) * (CARD (FDOM bl.bl_inst_liveness) + 1))
    (fmap_to_alist lr.lr_blocks))` >>
  conj_tac >- (
    irule sum_map_pair_le >> rw[] >>
    irule per_block_sum_le >>
    fs[MEM_pair_fmap_to_alist_FLOOKUP] >> metis_tac[]) >>
  (* Step 2: factor out nv, then bound slot count *)
  simp[sum_map_factor] >>
  disj2_tac >>
  simp[GSYM sum_one_plus] >>
  irule slot_sum_bounded >>
  rw[ALL_DISTINCT_fmap_to_alist_keys, MEM_pair_fmap_to_alist_FLOOKUP] >>
  fs[lr_shaped_def] >> res_tac >>
  qexists_tac `bb` >> simp[] >>
  `CARD (FDOM bl.bl_inst_liveness) ≤ CARD (count (LENGTH bb.bb_instructions))` by (
    irule CARD_SUBSET >> simp[FINITE_COUNT]) >>
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

(* process_block is inflationary under lr_consistent *)
Theorem process_block_inflationary[local]:
  ∀cfg bbs lr bb.
    lr_consistent bbs lr ∧
    lookup_block bb.bb_label bbs = SOME bb ==>
    lr_leq lr (process_block cfg bbs lr bb)
Proof
  rw[lr_leq_def]
  >- (
    (* out_vars: merged ⊇ old *)
    rw[process_block_out_vars] >>
    Cases_on `lbl = bb.bb_label` >> simp[list_union_set_proof, SUBSET_DEF]
  )
  >> (* live_vars_at *)
     Cases_on `lbl = bb.bb_label`
  >- (
    (* same label: use consistency + monotonicity *)
    rw[live_vars_at_def, LET_DEF] >>
    simp[process_block_def, LET_DEF, lookup_block_liveness_def,
         FLOOKUP_UPDATE] >>
    Cases_on `FLOOKUP lr.lr_blocks bb.bb_label` >> simp[]
    >- (
      (* no existing block: old live_vars_at = [] *)
      simp[empty_block_liveness_def, FLOOKUP_DEF, FDOM_FEMPTY]
    )
    >> (* existing block x *)
       Cases_on `FLOOKUP x.bl_inst_liveness idx` >> simp[]
    >- simp[SUBSET_DEF]
    >> (* SOME vars in old block *)
       rename1 `FLOOKUP x.bl_inst_liveness idx = SOME old_vars` >>
       (* By consistency: calculate_liveness bb x has entry ⊇ old_vars *)
       `∃cv. FLOOKUP (calculate_liveness bb x).bl_inst_liveness idx = SOME cv ∧
             set old_vars ⊆ set cv` by (
         fs[lr_consistent_def] >> metis_tac[]) >>
       (* calculate_liveness on merged out_vars ⊇ calculate_liveness on old out_vars,
          because merged = list_union old new ⊇ old *)
       qmatch_goalsub_abbrev_tac `calculate_liveness bb bl_merged` >>
       `set x.bl_out_vars ⊆ set bl_merged.bl_out_vars` by (
         unabbrev_all_tac >> simp[list_union_set_proof, SUBSET_DEF]) >>
       Cases_on `FLOOKUP (calculate_liveness bb bl_merged).bl_inst_liveness idx`
       >> simp[SUBSET_DEF]
       >> rename1 `FLOOKUP _ _ = SOME new_vars` >>
       `set cv ⊆ set new_vars` by (
         Cases_on `NULL bb.bb_instructions`
         >- (
           (* NULL: calculate_liveness = identity, so cv = old_vars, new_vars = old_vars *)
           fs[calculate_liveness_def, LET_DEF] >>
           `bl_merged.bl_inst_liveness = x.bl_inst_liveness` by
             (unabbrev_all_tac >> simp[]) >>
           fs[])
         >> irule calculate_liveness_monotone >>
            qexistsl_tac [`bb`, `x`, `bl_merged`, `idx`] >> simp[]) >>
       fs[SUBSET_DEF]
  )
  >> (* different label: unchanged *)
     simp[process_block_live_vars_neq]
QED

(* one_pass is inflationary *)
Theorem one_pass_inflationary[local]:
  ∀cfg bbs order lr.
    lr_consistent bbs lr ==>
    lr_leq lr (liveness_one_pass cfg bbs lr order)
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF, lr_leq_def] >>
  Cases_on `lookup_block h bbs` >> fs[]
  >- (
    (* NONE: lr unchanged, apply IH *)
    `lr_leq lr (liveness_one_pass cfg bbs lr order)` by
      (first_x_assum irule >> simp[]) >>
    fs[lr_leq_def]
  )
  >> (* SOME bb: process_block then continue *)
     rename1 `lookup_block h bbs = SOME bb` >>
     imp_res_tac lookup_block_label >> gvs[] >>
     `lr_leq lr (process_block cfg bbs lr bb)` by (
       irule process_block_inflationary >> simp[]) >>
     `lr_consistent bbs (process_block cfg bbs lr bb)` by (
       irule process_block_preserves_consistent >> simp[]) >>
     `lr_leq (process_block cfg bbs lr bb)
             (liveness_one_pass cfg bbs (process_block cfg bbs lr bb) order)` by (
       first_x_assum irule >> simp[]) >>
     fs[lr_leq_def, SUBSET_DEF] >> metis_tac[]
QED

(* --- Set-based measure increases when one_pass changes something --- *)

(* If inflationary (lr_leq) and different, set_live_count strictly increases.
   Key insight: lr_leq means all sets ⊇, different means some set strictly grew,
   so the sum of CARDs strictly increases. *)
Theorem one_pass_set_measure_increase[local]:
  ∀cfg bbs order lr.
    lr_inv bbs lr ∧
    liveness_one_pass cfg bbs lr order ≠ lr ==>
    set_live_count (liveness_one_pass cfg bbs lr order) >
    set_live_count lr
Proof
  (* Factor as: one_pass_inflationary gives lr_leq lr (one_pass lr),
     then lr_leq + lr1 ≠ lr2 ⟹ set_live_count lr1 < set_live_count lr2
     (structural property of lr_leq/set_live_count).
     Alternatively, use df_iterate_inflationary_fixpoint directly in
     liveness_analyze_fixpoint_proof and delete this lemma. *)
  cheat
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
    `all_var_slots fn.fn_blocks`,
    `λlr'. lr_inv fn.fn_blocks lr'`,
    `init_liveness fn.fn_blocks`
  ] mp_tac df_iterate_fixpoint_orbit >>
  simp[] >> impl_tac
  >- metis_tac[init_lr_inv, one_pass_preserves_inv,
               one_pass_set_measure_increase, set_live_count_bounded]
  >> simp[]
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
    `set_live_count`, `all_var_slots bbs`,
    `λlr'. lr_inv bbs lr'`, `lr`
  ] mp_tac df_iterate_invariant >>
  simp[] >> impl_tac >>
  metis_tac[one_pass_preserves_inv, one_pass_set_measure_increase,
            set_live_count_bounded]
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

(* ===== Soundness ===== *)

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
  (* At the fixpoint, live_vars_at satisfies the dataflow equations.
     If v is live at (lbl, idx), either:
     1) inst at (lbl, idx) uses v — path = [], k=0
     2) inst doesn't define v, v is live at next point — extend path by IH
     Intra-block: idx < last → v live at (lbl, idx+1)
     Block boundary: idx = last (terminator) → v in out_vars → v live
       at some successor's idx 0 via calculate_out_vars/input_vars_from
     Need well-founded induction on the path length or the total live
     set structure to avoid infinite looping through back edges. *)
  cheat
QED
