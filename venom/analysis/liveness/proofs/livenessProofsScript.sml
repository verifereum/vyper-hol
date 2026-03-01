(*
 * Liveness Analysis — Internal Correctness Proofs
 *
 * Proofs are re-exported via livenessAnalysisPropsScript.sml.
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs dfIterateProofs cfgAnalysisProps cfgHelpers

open listTheory rich_listTheory pred_setTheory arithmeticTheory venomInstTheory
     finite_mapTheory pairTheory alistTheory sptreeTheory
     cfgAnalysisPropsTheory WhileTheory
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

(* ===== Generic boundedness chain =====
   Parameterized by universe U. The only requirement is that inst_uses
   values land in U (uses_in_U). This suffices because live_update only
   adds inst_uses elements, and input_vars_from only adds base or inst_uses. *)

(* One step of calculate_out_vars preserves U-boundedness *)
Theorem calc_out_step_gen_bounded[local]:
  ∀acc succ_lbl lr bb bbs U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    lr_vars_bounded lr U ∧
    (∀v. MEM v acc ==> MEM v U) ==>
    ∀v. MEM v (case lookup_block succ_lbl bbs of
          NONE => acc
        | SOME succ_bb =>
          list_union acc (input_vars_from bb.bb_label
            succ_bb.bb_instructions (live_vars_at lr succ_lbl 0))) ==>
    MEM v U
Proof
  rpt strip_tac >>
  Cases_on `lookup_block succ_lbl bbs` >> fs[list_union_mem] >>
  drule input_vars_from_vars_bounded >> strip_tac >> fs[] >>
  fs[lr_vars_bounded_def] >> res_tac >>
  imp_res_tac lookup_block_mem >> metis_tac[]
QED

(* FOLDL for calculate_out_vars preserves U-boundedness *)
Theorem calc_out_foldl_gen_bounded[local]:
  ∀succs acc lr bb bbs U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    lr_vars_bounded lr U ∧
    (∀v. MEM v acc ==> MEM v U) ==>
    ∀v. MEM v (FOLDL (λacc succ_lbl.
      case lookup_block succ_lbl bbs of
        NONE => acc
      | SOME succ_bb =>
        list_union acc (input_vars_from bb.bb_label
          succ_bb.bb_instructions (live_vars_at lr succ_lbl 0)))
      acc succs) ==> MEM v U
Proof
  Induct >> rw[FOLDL] >>
  qpat_x_assum `∀acc. _` (fn th =>
    irule (SIMP_RULE (srw_ss()) [] (Q.SPECL [
      `case lookup_block h bbs of NONE => acc
       | SOME succ_bb => list_union acc
           (input_vars_from bb.bb_label succ_bb.bb_instructions
              (live_vars_at lr h 0))`,
      `lr`, `bb`, `bbs`, `U`] th))) >>
  metis_tac[calc_out_step_gen_bounded]
QED

(* calculate_out_vars produces vars in U *)
Theorem calculate_out_vars_gen_bounded[local]:
  ∀cfg lr bb bbs U v.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    lr_vars_bounded lr U ∧
    MEM v (calculate_out_vars cfg lr bb bbs) ==>
    MEM v U
Proof
  rw[calculate_out_vars_def] >>
  drule_then (drule_then
    (qspecl_then [`cfg_succs_of cfg bb.bb_label`, `[]`, `bb`] mp_tac))
    calc_out_foldl_gen_bounded >> simp[]
QED

(* calc_liveness_loop preserves U-boundedness *)
Theorem calc_liveness_loop_gen_bounded[local]:
  ∀n instrs live bbs bb U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    MEM bb bbs ∧
    (∀v. MEM v live ==> MEM v U) ∧
    n < LENGTH instrs ∧
    bb.bb_instructions = instrs ==>
    (∀v. MEM v (FST (calc_liveness_loop instrs live n)) ==> MEM v U) ∧
    (∀idx vars. FLOOKUP (SND (calc_liveness_loop instrs live n)) idx = SOME vars ==>
       ∀v. MEM v vars ==> MEM v U)
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- (
    (* Base case: n = 0 *)
    `∀inst v. MEM inst bb.bb_instructions ∧ MEM v (inst_uses inst) ==> MEM v U` by
      metis_tac[] >>
    rw[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    TRY (fs[live_update_mem] >> res_tac >> NO_TAC) >>
    `bb.bb_instructions ≠ []` by (Cases_on `bb.bb_instructions` >> fs[]) >>
    `MEM (HD bb.bb_instructions) bb.bb_instructions` by metis_tac[HEAD_MEM] >>
    fs[live_update_mem] >> res_tac)
  >>
  (* Step case: SUC n *)
  `∀inst v. MEM inst bb.bb_instructions ∧ MEM v (inst_uses inst) ==> MEM v U` by
    metis_tac[] >>
  simp[calc_liveness_loop_def, LET_DEF] >>
  `MEM (EL (SUC n) bb.bb_instructions) bb.bb_instructions` by
       (irule EL_MEM >> simp[]) >>
  qabbrev_tac `live' = if NULL (inst_uses (EL (SUC n) bb.bb_instructions)) ∧
                              NULL (inst_defs (EL (SUC n) bb.bb_instructions))
                           then live
                           else live_update (inst_defs (EL (SUC n) bb.bb_instructions))
                                (inst_uses (EL (SUC n) bb.bb_instructions)) live` >>
  `∀v. MEM v live' ==> MEM v U` by (
       unabbrev_all_tac >> rw[] >> fs[live_update_mem] >> res_tac) >>
  Cases_on `calc_liveness_loop bb.bb_instructions live' n` >>
  simp[] >>
  first_x_assum (qspecl_then [`bb.bb_instructions`, `live'`, `bbs`, `bb`, `U`] mp_tac) >>
  impl_tac >- (simp[Abbr`live'`] >> metis_tac[]) >>
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

(* calculate_liveness inst_liveness entries are bounded by U *)
Theorem calculate_liveness_gen_bounded[local]:
  ∀bb bl bbs idx vars U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    MEM bb bbs ∧
    (∀v. MEM v bl.bl_out_vars ==> MEM v U) ∧
    (∀idx' vars'. FLOOKUP bl.bl_inst_liveness idx' = SOME vars' ==>
       ∀v. MEM v vars' ==> MEM v U) ∧
    FLOOKUP (calculate_liveness bb bl).bl_inst_liveness idx = SOME vars ==>
    ∀v. MEM v vars ==> MEM v U
Proof
  rw[calculate_liveness_def, LET_DEF] >>
  Cases_on `NULL bb.bb_instructions` >> fs[]
  >- res_tac >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions - 1)` >> fs[] >>
  qspecl_then [`LENGTH bb.bb_instructions - 1`, `bb.bb_instructions`,
    `bl.bl_out_vars`, `bbs`, `bb`, `U`] mp_tac calc_liveness_loop_gen_bounded >>
  impl_tac >- (Cases_on `bb.bb_instructions` >> fs[] >> metis_tac[]) >>
  rw[] >> fs[] >> res_tac
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

(* process_block preserves U-boundedness (generic) *)
Theorem process_block_preserves_gen_bounded[local]:
  ∀cfg bbs lr bb U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    lr_vars_bounded lr U ∧
    MEM bb bbs ==>
    lr_vars_bounded (process_block cfg bbs lr bb) U
Proof
  rpt strip_tac >> rw[lr_vars_bounded_def, process_block_out_vars]
  >- (
    Cases_on `lbl = bb.bb_label` >> fs[list_union_mem] >>
    metis_tac[calculate_out_vars_gen_bounded, lr_vars_bounded_def]
  )
  >> Cases_on `lbl = bb.bb_label`
  >- (
    gvs[] >>
    `∀v. MEM v (list_union (out_vars_of lr bb.bb_label)
                  (calculate_out_vars cfg lr bb bbs)) ==>
         MEM v U` by (
      rw[list_union_mem] >>
      metis_tac[lr_vars_bounded_def, calculate_out_vars_gen_bounded]) >>
    fs[live_vars_at_def, process_block_def, LET_DEF,
       lookup_block_liveness_def, FLOOKUP_UPDATE, out_vars_of_def] >>
    qabbrev_tac `bl0 = case FLOOKUP lr.lr_blocks bb.bb_label of
      NONE => empty_block_liveness | SOME bl => bl` >>
    qabbrev_tac `bl' = bl0 with bl_out_vars :=
      list_union bl0.bl_out_vars (calculate_out_vars cfg lr bb bbs)` >>
    `∀idx' vars'. FLOOKUP bl0.bl_inst_liveness idx' = SOME vars' ==>
       ∀v. MEM v vars' ==> MEM v U` by (
      `bl0 = lookup_block_liveness lr bb.bb_label`
        by rw[Abbr`bl0`, lookup_block_liveness_def] >>
      metis_tac[lr_vars_bounded_inst_liveness]
    ) >>
    Cases_on `FLOOKUP (calculate_liveness bb bl').bl_inst_liveness idx` >>
    fs[] >>
    qspecl_then [`bb`, `bl'`, `bbs`, `idx`, `x`, `U`] mp_tac
      calculate_liveness_gen_bounded >>
    impl_tac >- (rw[Abbr`bl'`] >> res_tac) >> metis_tac[]
  )
  >> fs[process_block_live_vars_neq] >>
     metis_tac[lr_vars_bounded_def]
QED

(* one pass preserves U-boundedness (generic) *)
Theorem one_pass_preserves_gen_bounded[local]:
  ∀cfg bbs order lr U.
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    lr_vars_bounded lr U ==>
    lr_vars_bounded (liveness_one_pass cfg bbs lr order) U
Proof
  Induct_on `order` >> rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  first_x_assum irule >> simp[]
  >- metis_tac[]
  >> conj_tac >- metis_tac[] >>
  irule process_block_preserves_gen_bounded >> simp[] >>
  metis_tac[lookup_block_mem]
QED

(* ===== Instantiations for fn_all_vars ===== *)

Theorem calculate_out_vars_bounded[local]:
  ∀cfg lr bb bbs v.
    lr_vars_bounded lr (fn_all_vars bbs) ∧
    MEM v (calculate_out_vars cfg lr bb bbs) ==>
    MEM v (fn_all_vars bbs)
Proof
  metis_tac[calculate_out_vars_gen_bounded, fn_all_vars_mem]
QED

Theorem process_block_preserves_bounded[local]:
  ∀cfg bbs lr bb.
    lr_vars_bounded lr (fn_all_vars bbs) ∧ MEM bb bbs ==>
    lr_vars_bounded (process_block cfg bbs lr bb) (fn_all_vars bbs)
Proof
  metis_tac[process_block_preserves_gen_bounded, fn_all_vars_mem]
QED

Theorem one_pass_preserves_bounded[local]:
  ∀cfg bbs order lr.
    lr_vars_bounded lr (fn_all_vars bbs) ==>
    lr_vars_bounded (liveness_one_pass cfg bbs lr order) (fn_all_vars bbs)
Proof
  rpt strip_tac >> irule one_pass_preserves_gen_bounded >>
  metis_tac[fn_all_vars_mem]
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

(* init_liveness has empty out_vars for all labels *)
Theorem init_out_vars_empty[local]:
  ∀bbs lbl. out_vars_of (init_liveness bbs) lbl = []
Proof
  rw[out_vars_of_def, lookup_block_liveness_def, init_liveness_def] >>
  Cases_on `FLOOKUP (FOLDL (λm bb'. m |+ (bb'.bb_label,
    empty_block_liveness)) FEMPTY bbs) lbl` >>
  imp_res_tac foldl_init_flookup >>
  gvs[empty_block_liveness_def]
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

(* === Monotonicity helpers === *)

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

(* ===== Path construction helpers ===== *)

(* An intra-block path (lbl, s) :: (lbl, s+1) :: ... :: (lbl, s+n) is valid. *)
Theorem cfg_exec_path_intra[local]:
  ∀n lbl s cfg.
    cfg_exec_path cfg (GENLIST (λi. (lbl:string, s + i)) (SUC n))
Proof
  Induct >- simp[GENLIST_CONS, cfg_exec_path_def] >>
  rpt gen_tac >>
  simp[Once GENLIST_CONS, combinTheory.o_DEF] >>
  `GENLIST (λx. (lbl:string, s + SUC x)) (SUC n) =
   GENLIST (λi. (lbl, SUC s + i)) (SUC n)` by (
    irule GENLIST_CONG >> simp[ADD_CLAUSES]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`lbl`, `SUC s`, `cfg`] mp_tac) >>
  Cases_on `GENLIST (λi. (lbl:string, SUC s + i)) (SUC n)` >- fs[GENLIST] >>
  strip_tac >>
  `h = (lbl, SUC s)` by (
    qpat_x_assum `_ = h::t` (mp_tac o SYM) >>
    simp[GENLIST_CONS, combinTheory.o_DEF]) >>
  rw[cfg_exec_path_def] >> simp[ADD1]
QED

(* Appending a valid transition preserves cfg_exec_path. *)
Theorem cfg_exec_path_snoc[local]:
  ∀path lbl1 idx1 lbl2 idx2 cfg.
    cfg_exec_path cfg (path ++ [(lbl1, idx1)]) ∧
    ((lbl1 = lbl2 ∧ idx2 = idx1 + 1) ∨
     (MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0)) ==>
    cfg_exec_path cfg (path ++ [(lbl1, idx1); (lbl2, idx2)])
Proof
  Induct >- (rw[cfg_exec_path_def] >> PairCases_on `h` >> gvs[cfg_exec_path_def]) >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `path` >> fs[cfg_exec_path_def] >>
  PairCases_on `h` >> gvs[cfg_exec_path_def] >>
  first_x_assum irule >> metis_tac[]
QED

(* Concatenating two valid paths sharing an endpoint. *)
Theorem cfg_exec_path_append[local]:
  ∀p1 lbl idx p2 cfg.
    cfg_exec_path cfg (p1 ++ [(lbl, idx)]) ∧
    cfg_exec_path cfg ((lbl, idx) :: p2) ==>
    cfg_exec_path cfg (p1 ++ (lbl, idx) :: p2)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `p1`
  >- gvs[cfg_exec_path_def] >>
  rename1 `q :: t` >> PairCases_on `q` >>
  gvs[cfg_exec_path_def]
QED

(* Extend a path with a valid step and append a suffix.
   Combines snoc + append into one reusable lemma. *)
Theorem cfg_exec_path_extend[local]:
  ∀path lbl2 idx2 suffix cfg.
    cfg_exec_path cfg path ∧ path ≠ [] ∧
    ((lbl2 = FST (LAST path) ∧ idx2 = SND (LAST path) + 1) ∨
     (MEM lbl2 (cfg_succs_of cfg (FST (LAST path))) ∧ idx2 = 0)) ∧
    cfg_exec_path cfg ((lbl2, idx2) :: suffix) ==>
    cfg_exec_path cfg (path ++ (lbl2, idx2) :: suffix)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `path`
  >- (gvs[cfg_exec_path_def]) >>
  gvs[cfg_exec_path_def] >>
  PairCases_on `h` >> gvs[cfg_exec_path_def] >>
  first_x_assum irule >> simp[]
QED

(* ===== used_before_defined helpers ===== *)

Theorem EL_TL[local]:
  ∀n l. SUC n < LENGTH l ==> EL n (TL l) = EL (SUC n) l
Proof
  Cases_on `l` >> simp[]
QED

Theorem lookup_block_unique[local]:
  ∀lbl bbs bb bb'.
    lookup_block lbl bbs = SOME bb ∧ lookup_block lbl bbs = SOME bb' ==>
    bb = bb'
Proof
  rw[] >> gvs[]
QED

(* If inst_defs doesn't contain v, then var_defined_at is false *)
Theorem not_var_defined_at_no_def[local]:
  ∀bbs lbl idx v bb.
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    ¬MEM v (inst_defs (EL idx bb.bb_instructions)) ==>
    ¬var_defined_at bbs lbl idx v
Proof
  rw[var_defined_at_def] >>
  imp_res_tac lookup_block_unique >> gvs[]
QED

(* If instruction is a PHI, then var_defined_at is false *)
Theorem not_var_defined_at_phi[local]:
  ∀bbs lbl idx v bb.
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    (EL idx bb.bb_instructions).inst_opcode = PHI ==>
    ¬var_defined_at bbs lbl idx v
Proof
  rw[var_defined_at_def] >>
  imp_res_tac lookup_block_unique >> gvs[]
QED

(* If v is used at position k and not defined at any position before k,
   then used_before_defined holds. *)
Theorem used_before_defined_witness[local]:
  ∀bbs v positions k.
    k < LENGTH positions ∧
    var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
    (∀j. j < k ==> ¬var_defined_at bbs (FST (EL j positions))
                                         (SND (EL j positions)) v) ==>
    used_before_defined bbs v positions
Proof
  rw[used_before_defined_def] >> qexists_tac `k` >> simp[]
QED

(* used_before_defined is preserved when prepending non-defining positions. *)
Theorem used_before_defined_prepend[local]:
  ∀prefix bbs v suffix.
    used_before_defined bbs v suffix ∧
    (∀j. j < LENGTH prefix ==>
       ¬var_defined_at bbs (FST (EL j prefix)) (SND (EL j prefix)) v) ==>
    used_before_defined bbs v (prefix ++ suffix)
Proof
  rw[used_before_defined_def] >>
  qexists_tac `LENGTH prefix + k` >>
  simp[EL_APPEND2, EL_APPEND1] >>
  rpt strip_tac >>
  Cases_on `j < LENGTH prefix`
  >- (res_tac >> gvs[EL_APPEND1]) >>
  `j - LENGTH prefix < k` by simp[] >>
  `LENGTH prefix ≤ j` by simp[] >>
  gvs[EL_APPEND2]
QED

(* Helper: EL into the intra-block path [(lbl,idx), (lbl,idx+1), ..., (lbl,j)] *)
Theorem intra_path_el[local]:
  ∀idx j k.
    idx ≤ j ∧ k ≤ j - idx ==>
    EL k ((lbl, idx) :: TL (GENLIST (λi. (lbl, idx + i)) (SUC (j - idx)))) =
    (lbl, idx + k)
Proof
  rpt strip_tac >> Cases_on `k`
  >- simp[] >>
  simp[EL_CONS, EL_TL, EL_GENLIST, LENGTH_GENLIST]
QED

(* v used at (lbl, j) and no def from idx to j: path is [(lbl,idx)...(lbl,j)] *)
Theorem use_in_block_path[local]:
  ∀bbs cfg lbl bb idx j v.
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx ≤ j ∧ j < LENGTH bb.bb_instructions ∧
    MEM v (inst_uses (EL j bb.bb_instructions)) ∧
    (∀k. idx ≤ k ∧ k < j ==> ¬MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  rpt strip_tac >>
  qabbrev_tac `positions = (lbl, idx) ::
    TL (GENLIST (λi. (lbl, idx + i)) (SUC (j - idx)))` >>
  qexists_tac `TL positions` >>
  `LENGTH positions = SUC (j - idx)` by
    simp[Abbr`positions`, LENGTH_TL, LENGTH_GENLIST] >>
  `∀k. k ≤ j - idx ==> EL k positions = (lbl, idx + k)` by
    (rpt strip_tac >> simp[Abbr`positions`, intra_path_el]) >>
  conj_tac >- (
    `GENLIST (λi. (lbl, idx + i)) (SUC (j - idx)) = positions` by (
      simp[Abbr`positions`] >>
      Cases_on `GENLIST (λi. (lbl, idx + i)) (SUC (j − idx))`
      >- fs[GENLIST] >> fs[GENLIST_CONS]) >>
    metis_tac[cfg_exec_path_intra]) >>
  `(lbl, idx) :: TL positions = positions` by simp[Abbr`positions`] >>
  pop_assum SUBST1_TAC >>
  irule used_before_defined_witness >>
  qexists_tac `j - idx` >> simp[] >>
  simp[var_used_at_def] >> gvs[var_defined_at_def]
QED

(* Path construction for cross-block transition:
   (lbl, idx) ... (lbl, last) :: (succ_lbl, 0) :: succ_path *)
Theorem cross_block_path[local]:
  ∀bbs cfg lr fn bb lbl idx succ_lbl succ_path v.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ bbs = fn.fn_blocks ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM succ_lbl (cfg_succs_of cfg lbl) ∧
    cfg_exec_path cfg ((succ_lbl, 0) :: succ_path) ∧
    (∀k. idx ≤ k ∧ k < LENGTH bb.bb_instructions ==>
       ¬MEM v (inst_defs (EL k bb.bb_instructions))) ∧
    used_before_defined bbs v ((succ_lbl, 0) :: succ_path) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  rpt strip_tac >>
  qabbrev_tac `last_idx = LENGTH bb.bb_instructions - 1` >>
  `idx ≤ last_idx` by simp[Abbr`last_idx`] >>
  qabbrev_tac `gl = GENLIST (λi. (lbl:string, idx + i)) (SUC (last_idx - idx))` >>
  (* Intra-block path properties *)
  `cfg_exec_path cfg gl` by metis_tac[cfg_exec_path_intra] >>
  `gl ≠ []` by simp[Abbr`gl`, GENLIST] >>
  `HD gl = (lbl, idx)` by simp[Abbr`gl`, GENLIST_CONS] >>
  `LAST gl = (lbl, last_idx)` by simp[Abbr`gl`, LAST_EL, EL_GENLIST, Abbr`last_idx`] >>
  `LENGTH gl = SUC (last_idx - idx)` by simp[Abbr`gl`] >>
  `∀k. k < LENGTH gl ==> EL k gl = (lbl, idx + k)` by simp[Abbr`gl`, EL_GENLIST] >>
  (* Extend across block boundary and append successor *)
  `cfg_exec_path cfg (gl ++ (succ_lbl, 0) :: succ_path)` by (
    irule cfg_exec_path_extend >> rpt conj_tac >> fs[] >> metis_tac[]) >>
  (* Build path using gl directly, avoid Cases_on *)
  qexists_tac `TL gl ++ (succ_lbl, 0) :: succ_path` >>
  `(lbl,idx) :: (TL gl ++ (succ_lbl,0)::succ_path) =
   gl ++ (succ_lbl,0)::succ_path` by
    (Cases_on `gl` >> fs[]) >>
  (* Rewrite both conjuncts to gl-based form *)
  pop_assum (fn th => REWRITE_TAC[th]) >>
  conj_tac >- fs[] >>
  (* used_before_defined via prepend lemma *)
  irule used_before_defined_prepend >> fs[] >>
  rpt strip_tac >>
  `EL j gl = (lbl, idx + j)` by (
    first_x_assum (qspec_then `j` mp_tac) >> fs[]) >>
  fs[var_defined_at_def] >>
  `bb' = bb` by metis_tac[lookup_block_unique] >>
  gvs[Abbr`last_idx`]
QED

(* Path from (succ_lbl, 0) witnessing a PHI use of v.
   succ_bb has a PHI instruction that reads (src_lbl, v).
   Path: [(succ_lbl,0), ..., (succ_lbl,k)] where k is the PHI position.
   All positions 0..k-1 are also PHIs (by bb_well_formed), so var_defined_at is false. *)
Theorem phi_use_path[local]:
  ∀bbs cfg succ_lbl succ_bb src_lbl inst v.
    lookup_block succ_lbl bbs = SOME succ_bb ∧ succ_bb.bb_label = succ_lbl ∧
    bb_well_formed succ_bb ∧
    MEM inst succ_bb.bb_instructions ∧ inst.inst_opcode = PHI ∧
    MEM (src_lbl, v) (phi_pairs inst.inst_operands) ==>
    ∃path.
      cfg_exec_path cfg ((succ_lbl, 0) :: path) ∧
      used_before_defined bbs v ((succ_lbl, 0) :: path)
Proof
  rpt strip_tac >>
  `∃k. k < LENGTH succ_bb.bb_instructions ∧
       EL k succ_bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
  `∀j. j < k ==> (EL j succ_bb.bb_instructions).inst_opcode = PHI` by
    (rpt strip_tac >> fs[bb_well_formed_def] >> metis_tac[]) >>
  imp_res_tac lookup_block_label >>
  qabbrev_tac `positions = GENLIST (λi. (succ_lbl:string, i)) (SUC k)` >>
  `LENGTH positions = SUC k` by simp[Abbr`positions`] >>
  `positions ≠ []` by simp[Abbr`positions`, GENLIST] >>
  `HD positions = (succ_lbl, 0)` by simp[Abbr`positions`, GENLIST_CONS] >>
  `(succ_lbl, 0) :: TL positions = positions` by
    (Cases_on `positions` >> fs[]) >>
  (* cfg_exec_path *)
  `cfg_exec_path cfg ((succ_lbl, 0) :: TL positions)` by (
    `(succ_lbl, 0) :: TL positions =
     GENLIST (λi. (succ_lbl, 0 + i)) (SUC (k - 0))` by
      simp[Abbr`positions`] >>
    pop_assum SUBST1_TAC >>
    irule cfg_exec_path_intra >> simp[]) >>
  (* Combine *)
  qexists_tac `TL positions` >> conj_tac >- simp[] >>
  `(succ_lbl, 0) :: TL positions = positions` by fs[] >>
  asm_rewrite_tac[] >>
  irule used_before_defined_witness >> qexists_tac `k` >> simp[] >>
  conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    `EL j positions = (succ_lbl, j)` by simp[Abbr`positions`, EL_GENLIST] >>
    simp[] >> irule not_var_defined_at_phi >>
    qexists_tac `succ_bb` >> simp[])
  >- (
    `EL k positions = (succ_lbl, k)` by simp[Abbr`positions`, EL_GENLIST] >>
    simp[var_used_at_def, inst_uses_def] >>
    irule phi_pairs_subset_uses >>
    simp[MEM_MAP] >> qexists_tac `(src_lbl, v)` >> simp[])
QED

(* ===== Main soundness proof ===== *)

(* If v is not used in any instruction, input_vars_from only propagates from base *)
Theorem input_vars_from_no_use[local]:
  ∀src instrs base v.
    (∀inst. MEM inst instrs ==> ¬MEM v (inst_uses inst)) ∧
    MEM v (input_vars_from src instrs base) ==>
    MEM v base
Proof
  rpt strip_tac >>
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  `MEM v (operand_vars inst.inst_operands)` by (
    irule phi_pairs_subset_uses >>
    simp[MEM_MAP] >> qexists_tac `(src, v)` >> simp[]) >>
  `MEM v (inst_uses inst)` by fs[inst_uses_def] >>
  metis_tac[]
QED

(* calc_liveness_loop: if v ∉ inst_uses for all instructions and v ∉ out_vars,
   then v doesn't appear in any liveness entry *)
Theorem calc_loop_no_use_no_mem[local]:
  ∀n instrs out v.
    n < LENGTH instrs ∧
    (∀i. i ≤ n ==> ¬MEM v (inst_uses (EL i instrs))) ∧
    ¬MEM v out ==>
    ¬MEM v (FST (calc_liveness_loop instrs out n)) ∧
    ∀idx vars. idx ≤ n ∧
      FLOOKUP (SND (calc_liveness_loop instrs out n)) idx = SOME vars ==>
      ¬MEM v vars
Proof
  Induct_on `n`
  >- (
    rpt gen_tac >> strip_tac >>
    simp[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    Cases_on `NULL (inst_uses (EL 0 instrs)) ∧ NULL (inst_defs (EL 0 instrs))`
    >> gvs[] >>
    fs[live_update_set_proof, EXTENSION] >> rpt strip_tac >> gvs[NULL_EQ])
  >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `live' = if NULL (inst_uses (EL (SUC n) instrs)) ∧
    NULL (inst_defs (EL (SUC n) instrs)) then out
    else live_update (inst_defs (EL (SUC n) instrs))
      (inst_uses (EL (SUC n) instrs)) out` >>
  `¬MEM v live'` by (
    unabbrev_all_tac >> rw[] >>
    fs[live_update_set_proof, EXTENSION] >>
    first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
  `¬MEM v (FST (calc_liveness_loop instrs live' n)) ∧
   ∀idx vars. idx ≤ n ∧ FLOOKUP (SND (calc_liveness_loop instrs live' n)) idx = SOME vars ==>
     ¬MEM v vars` by (
    first_x_assum irule >> simp[] >>
    rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `calc_liveness_loop instrs live' n` >> gvs[] >>
  `calc_liveness_loop instrs out (SUC n) = (q, r |+ (SUC n, live'))` by (
    simp[Once calc_liveness_loop_def, LET_DEF] >>
    unabbrev_all_tac >> simp[]) >>
  simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `SUC n = idx` >> gvs[] >>
  `idx ≤ n` by simp[] >> res_tac
QED

(* If v ∉ inst_uses for all instructions and v ∉ out_vars,
   then v ∉ live_vars_at (under lr_consistent + lr_shaped) *)
Theorem live_vars_no_use_no_out[local]:
  ∀bbs lr bb lbl idx v.
    lr_consistent bbs lr ∧ lr_shaped bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    (∀i. i < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_uses (EL i bb.bb_instructions))) ∧
    ¬MEM v (out_vars_of lr lbl) ==>
    ¬MEM v (live_vars_at lr lbl idx)
Proof
  rpt gen_tac >> strip_tac >>
  simp[live_vars_at_def, LET_DEF, lookup_block_liveness_def] >>
  Cases_on `FLOOKUP lr.lr_blocks lbl` >>
  gvs[empty_block_liveness_def] >>
  rename1 `FLOOKUP lr.lr_blocks lbl = SOME bl` >>
  Cases_on `FLOOKUP bl.bl_inst_liveness idx` >> gvs[] >>
  rename1 `FLOOKUP bl.bl_inst_liveness idx = SOME vars` >>
  strip_tac >>
  `¬MEM v bl.bl_out_vars` by
    fs[out_vars_of_def, lookup_block_liveness_def] >>
  `calculate_liveness bb bl = bl` by (
    fs[lr_consistent_def] >>
    first_x_assum (qspecl_then [`lbl`, `bl`, `bb`] mp_tac) >> simp[] >>
    strip_tac >> gvs[FLOOKUP_DEF, FDOM_FEMPTY]) >>
  `idx < LENGTH bb.bb_instructions` by (
    fs[lr_shaped_def] >> res_tac >>
    gvs[SUBSET_DEF, IN_COUNT] >>
    pop_assum irule >> fs[FLOOKUP_DEF]) >>
  `¬NULL bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  fs[calculate_liveness_def, LET_DEF] >> pairarg_tac >>
  gvs[block_liveness_component_equality] >>
  `¬MEM v (FST (calc_liveness_loop bb.bb_instructions bl.bl_out_vars
      (LENGTH bb.bb_instructions − 1))) ∧
   ∀idx vars. idx ≤ LENGTH bb.bb_instructions − 1 ∧
     FLOOKUP (SND (calc_liveness_loop bb.bb_instructions bl.bl_out_vars
       (LENGTH bb.bb_instructions − 1))) idx = SOME vars ==>
     ¬MEM v vars` by (
    irule calc_loop_no_use_no_mem >> simp[] >>
    rpt strip_tac >> first_x_assum irule >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`idx`, `vars`] mp_tac) >> simp[]
QED

(* v ∉ calculate_out_vars when self-loop is transparent and non-self don't contribute *)
Theorem calc_out_no_v[local]:
  ∀cfg lr bb bbs lbl v.
    lr_consistent bbs lr ∧ lr_shaped bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    (∀i. i < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_uses (EL i bb.bb_instructions))) ∧
    ¬MEM v (out_vars_of lr lbl) ∧
    (∀s sb. s ≠ lbl ∧ MEM s (cfg_succs_of cfg lbl) ∧
       lookup_block s bbs = SOME sb ==>
       ¬MEM v (input_vars_from lbl sb.bb_instructions
                 (live_vars_at lr s 0))) ==>
    ¬MEM v (calculate_out_vars cfg lr bb bbs)
Proof
  rpt strip_tac >>
  drule calc_out_vars_witness >> strip_tac >>
  Cases_on `succ_lbl = lbl`
  >- (
    gvs[] >>
    `∀inst. MEM inst bb.bb_instructions ==> ¬MEM v (inst_uses inst)` by (
      rpt strip_tac >>
      qpat_x_assum `MEM inst _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
      metis_tac[]) >>
    drule_all input_vars_from_no_use >> strip_tac >>
    (* v ∈ live_vars_at lr lbl 0 contradicts v ∉ out_vars *)
    imp_res_tac live_vars_no_use_no_out >> gvs[])
  >>
  metis_tac[]
QED

(* lr_leq is transitive *)
Theorem lr_leq_trans[local]:
  ∀a b c. lr_leq a b ∧ lr_leq b c ==> lr_leq a c
Proof
  rw[lr_leq_def] >> metis_tac[SUBSET_TRANS]
QED

(* Factored monotonicity: input_vars_from at lr ⊆ input_vars_from at one_pass(lr).
   Used to discharge CCONTR_TAC obligations in one_pass_preserves_no_v. *)
Theorem input_vars_from_mono_one_pass[local]:
  ∀cfg bbs lr order lbl s sb.
    lr_inv bbs lr ∧ lookup_block s bbs = SOME sb ==>
    set (input_vars_from lbl sb.bb_instructions (live_vars_at lr s 0)) ⊆
    set (input_vars_from lbl sb.bb_instructions
      (live_vars_at (liveness_one_pass cfg bbs lr order) s 0))
Proof
  rpt strip_tac >>
  irule input_vars_from_mono >>
  `lr_leq lr (liveness_one_pass cfg bbs lr order)` suffices_by fs[lr_leq_def] >>
  irule one_pass_inflationary >> fs[lr_inv_def]
QED

(* Common tactic for showing non-self input mono in one_pass_preserves_no_v:
   if v ∉ input_vars_from at one_pass(lr_final) and lr_mid ≤ lr_final,
   then v ∉ input_vars_from at lr_mid (by SUBSET containment). *)

(* one_pass preserves "v ∉ out_vars(lbl)" when self-loop is transparent and
   non-self successors don't contribute v at the final one_pass result.
   The key: intermediate lr_partial ⊑ one_pass(lr), so non-self don't contribute at lr_partial either. *)
Theorem one_pass_preserves_no_v[local]:
  ∀cfg bbs order lr bb lbl v.
    lr_inv bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    (∀i. i < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_uses (EL i bb.bb_instructions))) ∧
    ¬MEM v (out_vars_of lr lbl) ∧
    (∀s sb. s ≠ lbl ∧ MEM s (cfg_succs_of cfg lbl) ∧
       lookup_block s bbs = SOME sb ==>
       ¬MEM v (input_vars_from lbl sb.bb_instructions
                 (live_vars_at (liveness_one_pass cfg bbs lr order) s 0))) ==>
    ¬MEM v (out_vars_of (liveness_one_pass cfg bbs lr order) lbl)
Proof
  gen_tac >> gen_tac >> Induct_on `order`
  >- rw[liveness_one_pass_def, LET_DEF]
  >>
  rw[liveness_one_pass_def, LET_DEF] >>
  Cases_on `lookup_block h bbs` >> gvs[] >>
  rename1 `lookup_block h bbs = SOME blk` >>
  imp_res_tac lookup_block_label >> gvs[] >>
  qabbrev_tac `lr1 = process_block cfg bbs lr blk` >>
  `lr_inv bbs lr1` by
    (simp[Abbr`lr1`] >> irule process_block_preserves_inv >> fs[lr_inv_def]) >>
  (* Apply IH — leaves ¬MEM v (out_vars_of lr1 bb.bb_label) *)
  first_x_assum irule >> simp[] >>
  Cases_on `blk.bb_label = bb.bb_label`
  >- ( (* blk = bb: process_block adds calculate_out_vars *)
    `blk = bb` by metis_tac[lookup_block_unique] >> gvs[] >>
    `¬MEM v (calculate_out_vars cfg lr bb bbs)` suffices_by
      simp[Abbr`lr1`, process_block_out_vars, list_union_mem] >>
    irule calc_out_no_v >> fs[lr_inv_def] >> rpt strip_tac >>
    first_x_assum (qspecl_then [`s`, `sb`] mp_tac) >> simp[] >>
    `set (input_vars_from bb.bb_label sb.bb_instructions (live_vars_at lr s 0)) ⊆
     set (input_vars_from bb.bb_label sb.bb_instructions
       (live_vars_at (liveness_one_pass cfg bbs (process_block cfg bbs lr bb)
                        order) s 0))` by (
      irule input_vars_from_mono >>
      `lr_leq lr (liveness_one_pass cfg bbs (process_block cfg bbs lr bb) order)`
        suffices_by fs[lr_leq_def] >>
      irule lr_leq_trans >>
      qexists_tac `process_block cfg bbs lr bb` >> conj_tac
      >- (irule process_block_inflationary >> fs[])
      >> irule one_pass_inflationary >> fs[]) >>
    fs[Abbr`lr1`, SUBSET_DEF])
  >> (* blk ≠ bb: out_vars unchanged *)
  simp[Abbr`lr1`, process_block_out_vars]
QED

(* At fixpoint: if v ∈ out_vars(lbl) and v ∉ inst_uses of any instruction in bb,
(* lr_inv holds at any FUNPOW iteration *)
Theorem iter_lr_inv[local]:
  ∀n fn.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    lr_inv bbs (FUNPOW f n (init_liveness bbs))
Proof
  simp[LET_DEF] >> rpt gen_tac >>
  irule (INST_TYPE [alpha |-> ``:liveness_result``]
    (DB.fetch "arithmetic" "FUNPOW_invariant" |> SPEC_ALL |> GEN_ALL)) >>
  rw[init_lr_inv] >> irule one_pass_preserves_inv >> simp[]
QED

(* ===== Generalized nonself witness at any iteration ===== *)

(* If v is not used in any instruction, it can't appear in out_vars via
   non-self successors only. Holds at all FUNPOW iterations. *)
Theorem out_vars_nonself_at_iter[local]:
  ∀n fn bb lbl v.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    let lr = FUNPOW f n (init_liveness bbs) in
    wf_function fn ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (lookup_block_liveness lr lbl).bl_out_vars ∧
    (∀i. i < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_uses (EL i bb.bb_instructions))) ==>
    ∃succ_lbl succ_bb.
      succ_lbl ≠ lbl ∧
      MEM succ_lbl (cfg_succs_of cfg lbl) ∧
      lookup_block succ_lbl bbs = SOME succ_bb ∧
      MEM v (input_vars_from lbl succ_bb.bb_instructions
               (live_vars_at lr succ_lbl 0))
Proof
  simp[LET_DEF] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `f = λlr'. liveness_one_pass cfg bbs lr' cfg.cfg_dfs_post` >>
  qabbrev_tac `lr = FUNPOW f n (init_liveness bbs)` >>
  CCONTR_TAC >> fs[] >>
  `¬MEM v (out_vars_of lr bb.bb_label)` suffices_by fs[out_vars_of_def] >>
  qabbrev_tac `P = λlr'.
    lr_inv bbs lr' ∧
    ((∀s sb. s ≠ bb.bb_label ∧ MEM s (cfg_succs_of cfg bb.bb_label) ∧
       lookup_block s bbs = SOME sb ==>
       ¬MEM v (input_vars_from bb.bb_label sb.bb_instructions
                 (live_vars_at lr' s 0))) ==>
     ¬MEM v (out_vars_of lr' bb.bb_label))` >>
  `P lr` suffices_by (
    simp[Abbr`P`] >> strip_tac >>
    first_x_assum irule >> rpt strip_tac >>
    first_x_assum (qspecl_then [`s`, `sb`] mp_tac) >> simp[]) >>
  `lr = FUNPOW f n (init_liveness bbs)` by simp[Abbr`lr`] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [alpha |-> ``:liveness_result``]
    (DB.fetch "arithmetic" "FUNPOW_invariant" |> SPEC_ALL |> GEN_ALL)) >>
  simp[Abbr`P`, Abbr`f`] >>
  conj_tac >- (
    conj_tac >- simp[init_lr_inv] >>
    strip_tac >>
    simp[out_vars_of_def, init_liveness_def, lookup_block_liveness_def] >>
    Cases_on `FLOOKUP (FOLDL (λm bb'. m |+ (bb'.bb_label, empty_block_liveness))
                FEMPTY bbs) bb.bb_label` >>
    simp[empty_block_liveness_def] >>
    imp_res_tac foldl_init_flookup >> simp[empty_block_liveness_def]
  ) >- (
    rpt strip_tac >- (irule one_pass_preserves_inv >> simp[]) >- (
    `∀s sb.
       s ≠ bb.bb_label ∧ MEM s (cfg_succs_of cfg bb.bb_label) ∧
       lookup_block s bbs = SOME sb ⇒
       ¬MEM v (input_vars_from bb.bb_label sb.bb_instructions
                 (live_vars_at x s 0))` by (
      rpt strip_tac >> CCONTR_TAC >> fs[] >>
      `set (input_vars_from bb.bb_label sb.bb_instructions (live_vars_at x s 0)) ⊆
       set (input_vars_from bb.bb_label sb.bb_instructions
         (live_vars_at (liveness_one_pass cfg bbs x cfg.cfg_dfs_post) s 0))` by (
        irule input_vars_from_mono_one_pass >> simp[]) >>
      fs[SUBSET_DEF] >> res_tac >> res_tac) >>
    `¬MEM v (out_vars_of x bb.bb_label)` by (res_tac >> fs[]) >>
    qpat_x_assum `MEM v (out_vars_of (liveness_one_pass _ _ _ _) _)` mp_tac >>
    simp[] >>
    qspecl_then [`cfg`, `bbs`, `cfg.cfg_dfs_post`, `x`, `bb`, `bb.bb_label`, `v`]
      mp_tac one_pass_preserves_no_v >>
    simp[] >> fs[lr_inv_def]
    )
  )
QED

(* out_vars are justified (⊆ calculate_out_vars) at any FUNPOW iteration *)
Theorem out_vars_justified_at_iter[local]:
  ∀n fn lbl bb.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    let lr = FUNPOW f n (init_liveness bbs) in
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ==>
    set (out_vars_of lr lbl) ⊆ set (calculate_out_vars cfg lr bb bbs)
Proof
  simp[LET_DEF] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `f = λlr'. liveness_one_pass cfg bbs lr'
    cfg.cfg_dfs_post` >>
  qabbrev_tac `P = λlr'.
    lr_inv bbs lr' ∧
    ∀lbl' bb'. lookup_block lbl' bbs = SOME bb' ∧ bb'.bb_label = lbl' ==>
      set (out_vars_of lr' lbl') ⊆ set (calculate_out_vars cfg lr' bb' bbs)` >>
  `P (FUNPOW f n (init_liveness bbs))` suffices_by (
    simp[Abbr`P`] >> strip_tac >> res_tac) >>
  irule (INST_TYPE [alpha |-> ``:liveness_result``]
    (DB.fetch "arithmetic" "FUNPOW_invariant" |> SPEC_ALL |> GEN_ALL)) >>
  simp[Abbr`P`, Abbr`f`] >>
  conj_tac >- (
    conj_tac >- simp[init_lr_inv] >>
    rpt strip_tac >>
    simp[out_vars_of_def, init_liveness_def, lookup_block_liveness_def] >>
    Cases_on `FLOOKUP (FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
                FEMPTY bbs) bb'.bb_label` >>
    simp[empty_block_liveness_def] >>
    imp_res_tac foldl_init_flookup >> simp[empty_block_liveness_def]) >>
  rpt strip_tac
  >- (irule one_pass_preserves_inv >> simp[])
  >>
  qspecl_then [`cfg`, `bbs`, `cfg.cfg_dfs_post`, `x`]
    mp_tac one_pass_out_justified >>
  impl_tac >- fs[lr_inv_def] >>
  simp[LET_DEF]
QED

(* Combine justified + witness + phi_correct for any iteration *)
Theorem out_to_succ_at_iter[local]:
  ∀n fn bb lbl v.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    let lr = FUNPOW f n (init_liveness bbs) in
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (lookup_block_liveness lr lbl).bl_out_vars ==>
    ∃succ_lbl succ_bb.
      MEM succ_lbl (cfg_succs_of cfg lbl) ∧
      lookup_block succ_lbl bbs = SOME succ_bb ∧
      (MEM v (live_vars_at lr succ_lbl 0) ∨
       ∃inst. MEM inst succ_bb.bb_instructions ∧ inst.inst_opcode = PHI ∧
              MEM (lbl, v) (phi_pairs inst.inst_operands))
Proof
  simp[LET_DEF] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `lr = FUNPOW (λlr'. liveness_one_pass cfg bbs lr'
    cfg.cfg_dfs_post) n (init_liveness bbs)` >>
  `MEM v (calculate_out_vars cfg lr bb bbs)` by (
    mp_tac (Q.SPECL [`n`, `fn`, `bb.bb_label`, `bb`] out_vars_justified_at_iter) >>
    simp[LET_DEF, Abbr`cfg`, Abbr`bbs`, Abbr`lr`] >>
    disch_tac >> fs[SUBSET_DEF, out_vars_of_def]) >>
  drule calc_out_vars_witness >> strip_tac >>
  qexistsl_tac [`succ_lbl`, `succ_bb`] >> simp[] >>
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  disj2_tac >> metis_tac[]
QED

(* liveness_one_pass decomposes over list concatenation *)
Theorem one_pass_split[local]:
  ∀prefix cfg bbs lr suffix.
    liveness_one_pass cfg bbs lr (prefix ++ suffix) =
    liveness_one_pass cfg bbs (liveness_one_pass cfg bbs lr prefix) suffix
Proof
  Induct >> simp[liveness_one_pass_def, LET_DEF] >>
  rpt gen_tac >> Cases_on `lookup_block h bbs` >> simp[]
QED

(* Processing blocks in order doesn't change live_vars for labels not in order *)
Theorem one_pass_live_not_in_order[local]:
  ∀order cfg bbs lr lbl idx.
    ¬MEM lbl order ==>
    live_vars_at (liveness_one_pass cfg bbs lr order) lbl idx =
      live_vars_at lr lbl idx
Proof
  Induct >> simp[liveness_one_pass_def, LET_DEF] >> rpt strip_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  imp_res_tac lookup_block_label >>
  simp[process_block_live_vars_neq]
QED

(* Same for out_vars *)
Theorem one_pass_out_not_in_order[local]:
  ∀order cfg bbs lr lbl.
    ¬MEM lbl order ==>
    out_vars_of (liveness_one_pass cfg bbs lr order) lbl = out_vars_of lr lbl
Proof
  Induct >> simp[liveness_one_pass_def, LET_DEF] >> rpt strip_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  imp_res_tac lookup_block_label >>
  simp[process_block_out_vars]
QED

(* Key lemma: when v is NEW in out_vars at lbl after one_pass, trace the source.
   v entered through calculate_out_vars at the partial state when lbl was processed.
   The source is either: (1) at lr (input) for a not-yet-processed successor,
   (2) at the final result for an already-processed successor (with lower INDEX_OF),
   or (3) a PHI operand. Self-loop successors are allowed. *)
Theorem one_pass_new_comes_from[local]:
  ∀prefix lbl suffix cfg bbs lr bb v.
    ALL_DISTINCT (prefix ++ [lbl] ++ suffix) ∧
    lr_inv bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    MEM v (out_vars_of (liveness_one_pass cfg bbs lr
             (prefix ++ [lbl] ++ suffix)) lbl) ∧
    ¬MEM v (out_vars_of lr lbl) ==>
    ∃succ_lbl succ_bb.
      MEM succ_lbl (cfg_succs_of cfg lbl) ∧
      lookup_block succ_lbl bbs = SOME succ_bb ∧
      (MEM v (live_vars_at lr succ_lbl 0) ∨
       (MEM succ_lbl prefix ∧
        MEM v (live_vars_at (liveness_one_pass cfg bbs lr
                 (prefix ++ [lbl] ++ suffix)) succ_lbl 0)) ∨
       (∃inst. MEM inst succ_bb.bb_instructions ∧ inst.inst_opcode = PHI ∧
               MEM (lbl,v) (phi_pairs inst.inst_operands)))
Proof
  rpt strip_tac >>
  (* lbl ∉ prefix, lbl ∉ suffix *)
  `¬MEM lbl prefix ∧ ¬MEM lbl suffix` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[MEM]) >>
  (* out_vars at lr_partial = out_vars at lr for lbl *)
  `out_vars_of (liveness_one_pass cfg bbs lr prefix) lbl =
   out_vars_of lr lbl` by simp[one_pass_out_not_in_order] >>
  (* Decompose the one_pass computation *)
  `liveness_one_pass cfg bbs lr (prefix ++ [lbl] ++ suffix) =
   liveness_one_pass cfg bbs
     (process_block cfg bbs (liveness_one_pass cfg bbs lr prefix) bb) suffix` by
    (simp[GSYM APPEND_ASSOC, one_pass_split] >>
     simp[liveness_one_pass_def, LET_DEF]) >>
  (* out_vars at final for lbl = out_vars at process_block for lbl *)
  `out_vars_of (liveness_one_pass cfg bbs lr (prefix ++ [lbl] ++ suffix)) lbl =
   out_vars_of (process_block cfg bbs (liveness_one_pass cfg bbs lr prefix) bb)
     lbl` by simp[one_pass_out_not_in_order] >>
  (* v ∈ calculate_out_vars at lr_partial *)
  qabbrev_tac `lr_partial = liveness_one_pass cfg bbs lr prefix` >>
  `MEM v (calculate_out_vars cfg lr_partial bb bbs)` by
    (qpat_x_assum `MEM v (out_vars_of (liveness_one_pass _ _ _ _) _)` mp_tac >>
     simp[process_block_out_vars, list_union_mem]) >>
  (* Get successor witness *)
  drule calc_out_vars_witness >> strip_tac >>
  (* Case split on position — handles self-loop too *)
  qexistsl_tac [`succ_lbl`, `succ_bb`] >> gvs[] >>
  drule input_vars_from_phi_correct_proof >> strip_tac
  >- (
    (* v ∈ live_vars_at(lr_partial, succ_lbl, 0) *)
    Cases_on `MEM succ_lbl prefix`
    >- (
      (* succ was already processed: monotonicity gives v at final *)
      disj2_tac >> disj1_tac >> simp[] >>
      `lr_inv bbs lr_partial` by (
        simp[Abbr`lr_partial`] >>
        irule one_pass_preserves_inv >> fs[lr_inv_def]) >>
      `lr_leq lr_partial
         (liveness_one_pass cfg bbs (process_block cfg bbs lr_partial bb)
            suffix)` by (
        irule lr_leq_trans >>
        qexists_tac `process_block cfg bbs lr_partial bb` >>
        conj_tac
        >- (irule process_block_inflationary >> fs[lr_inv_def])
        >- (irule one_pass_inflationary >>
            `lr_inv bbs (process_block cfg bbs lr_partial bb)` suffices_by
              fs[lr_inv_def] >>
            irule process_block_preserves_inv >> fs[lr_inv_def])) >>
      fs[lr_leq_def, SUBSET_DEF])
    >- (
      (* succ not in prefix: live_vars_at(lr_partial) = live_vars_at(lr) *)
      disj1_tac >>
      `live_vars_at lr_partial succ_lbl 0 = live_vars_at lr succ_lbl 0` by
        (simp[Abbr`lr_partial`, one_pass_live_not_in_order]) >>
      fs[]))
  >- (
    (* PHI case *)
    disj2_tac >> disj2_tac >> metis_tac[])
QED

(* Helper: extract block from live_vars_at *)
Theorem live_vars_at_block[local]:
  ∀bbs lr lbl idx v.
    lr_inv bbs lr ∧
    MEM v (live_vars_at lr lbl idx) ==>
    ∃bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
         idx < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  fs[live_vars_at_def, lookup_block_liveness_def, lr_inv_def] >>
  Cases_on `FLOOKUP lr.lr_blocks lbl` >> gvs[]
  >- (fs[empty_block_liveness_def, FLOOKUP_DEF, FDOM_FEMPTY]) >>
  rename1 `FLOOKUP lr.lr_blocks lbl = SOME bl` >>
  Cases_on `FLOOKUP bl.bl_inst_liveness idx` >> gvs[] >>
  `lbl ∈ FDOM lr.lr_blocks` by metis_tac[flookup_thm] >>
  `MEM lbl (MAP (λbb. bb.bb_label) bbs)` by
    (fs[lr_shaped_def] >> metis_tac[]) >>
  `∃bb. lookup_block lbl bbs = SOME bb` by metis_tac[lookup_block_exists] >>
  qexists_tac `bb` >> simp[] >>
  imp_res_tac lookup_block_label >> simp[] >>
  `idx ∈ FDOM bl.bl_inst_liveness` by metis_tac[flookup_thm] >>
  `FDOM bl.bl_inst_liveness ⊆ count (LENGTH bb.bb_instructions)` by
    (fs[lr_shaped_def] >> first_x_assum irule >> metis_tac[]) >>
  fs[SUBSET_DEF]
QED

(* Back-propagation: if v ∈ out and no def from idx..n, then v at idx *)
Theorem calc_loop_back_propagate[local]:
  ∀n instrs out idx v.
    n < LENGTH instrs ∧ idx ≤ n ∧
    MEM v out ∧
    (∀k. idx ≤ k ∧ k ≤ n ==> ¬MEM v (inst_defs (EL k instrs))) ==>
    ∃vars. FLOOKUP (SND (calc_liveness_loop instrs out n)) idx = SOME vars ∧
           MEM v vars
Proof
  Induct_on `n` >> rpt strip_tac
  >- (
    (* Base: n = 0, idx = 0 *)
    `idx = 0` by simp[] >> gvs[] >>
    simp[calc_liveness_loop_def, LET_DEF, FLOOKUP_UPDATE] >>
    Cases_on `NULL (inst_uses (EL 0 instrs))` >>
    Cases_on `NULL (inst_defs (EL 0 instrs))` >>
    fs[live_update_mem, NULL_EQ]) >>
  (* Step: n = SUC n, expand calc_liveness_loop *)
  simp[calc_liveness_loop_def, LET_DEF] >>
  qabbrev_tac `live' = if NULL (inst_uses (EL (SUC n) instrs)) ∧
    NULL (inst_defs (EL (SUC n) instrs)) then out
    else live_update (inst_defs (EL (SUC n) instrs))
      (inst_uses (EL (SUC n) instrs)) out` >>
  Cases_on `calc_liveness_loop instrs live' n` >> simp[] >>
  (* v survives live_update at SUC n since no def *)
  `MEM v live'` by (
    simp[Abbr`live'`] >>
    `¬MEM v (inst_defs (EL (SUC n) instrs))` by
      (first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
    rw[live_update_mem]) >>
  Cases_on `idx = SUC n`
  >- (gvs[FLOOKUP_UPDATE]) >>
  `idx ≤ n` by simp[] >>
  simp[FLOOKUP_UPDATE] >>
  first_x_assum (qspecl_then [`instrs`, `live'`, `idx`, `v`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
                first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  strip_tac >> gvs[]
QED

(* Helper: consistent block's inst_liveness = calc_liveness_loop result *)
Theorem consistent_inst_eq_loop[local]:
  ∀bb bl.
    calculate_liveness bb bl = bl ∧ ¬NULL bb.bb_instructions ==>
    bl.bl_inst_liveness = SND (calc_liveness_loop bb.bb_instructions
      bl.bl_out_vars (LENGTH bb.bb_instructions − 1))
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = bl` (SUBST1_TAC o SYM) >>
  rw[calculate_liveness_def, LET_DEF] >>
  Cases_on `calc_liveness_loop bb.bb_instructions bl.bl_out_vars
    (LENGTH bb.bb_instructions − 1)` >> simp[]
QED

(* Block-level: out_vars + no def → live_vars_at.
   Caller must show bl_inst_liveness ≠ FEMPTY (e.g. block was processed). *)
Theorem out_vars_back_propagate[local]:
  ∀bbs lr bb lbl idx v bl.
    lr_consistent bbs lr ∧ lr_shaped bbs lr ∧
    FLOOKUP lr.lr_blocks lbl = SOME bl ∧
    bl.bl_inst_liveness ≠ FEMPTY ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM v bl.bl_out_vars ∧
    (∀k. idx ≤ k ∧ k < LENGTH bb.bb_instructions ==>
         ¬MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl idx)
Proof
  rpt strip_tac >>
  simp[live_vars_at_def, lookup_block_liveness_def] >>
  `¬NULL bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> fs[]) >>
  `calculate_liveness bb bl = bl` by (
    fs[lr_consistent_def] >>
    first_x_assum (qspecl_then [`lbl`, `bl`, `bb`] mp_tac) >> simp[]) >>
  qabbrev_tac `n = LENGTH bb.bb_instructions − 1` >>
  `bl.bl_inst_liveness = SND (calc_liveness_loop bb.bb_instructions
    bl.bl_out_vars n)` by simp[consistent_inst_eq_loop, Abbr`n`] >>
  `n < LENGTH bb.bb_instructions` by simp[Abbr`n`] >>
  `idx ≤ n` by simp[Abbr`n`] >>
  mp_tac (Q.SPECL [`n`, `bb.bb_instructions`, `bl.bl_out_vars`,
    `idx`, `v`] calc_loop_back_propagate) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[Abbr`n`]) >>
  strip_tac >> simp[]
QED

(* FLOOKUP at lbl unchanged after processing blocks not containing lbl *)
Theorem one_pass_flookup_not_in_order[local]:
  ∀order cfg bbs lr lbl.
    ¬MEM lbl order ==>
    FLOOKUP (liveness_one_pass cfg bbs lr order).lr_blocks lbl =
      FLOOKUP lr.lr_blocks lbl
Proof
  Induct >> simp[liveness_one_pass_def, LET_DEF] >> rpt strip_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  imp_res_tac lookup_block_label >>
  simp[process_block_def, LET_DEF, FLOOKUP_UPDATE]
QED

(* After one_pass with MEM lbl order, bl_inst_liveness ≠ FEMPTY *)
Theorem one_pass_inst_nonempty[local]:
  ∀order cfg bbs lr lbl bb bl.
    MEM lbl order ∧ ALL_DISTINCT order ∧
    lr_shaped bbs lr ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    ¬NULL bb.bb_instructions ∧
    FLOOKUP (liveness_one_pass cfg bbs lr order).lr_blocks lbl = SOME bl ==>
    bl.bl_inst_liveness ≠ FEMPTY
Proof
  rpt strip_tac >>
  `∃prefix suffix. order = prefix ++ [lbl] ++ suffix` by
    (imp_res_tac MEM_SPLIT_APPEND_first >>
     qexistsl_tac [`pfx`, `sfx`] >> simp[]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  qabbrev_tac `lr' = liveness_one_pass cfg bbs lr prefix` >>
  (* Rewrite order *)
  `liveness_one_pass cfg bbs lr (prefix ++ [bb.bb_label] ++ suffix) =
   liveness_one_pass cfg bbs (process_block cfg bbs lr' bb) suffix` by
    (simp[GSYM APPEND_ASSOC, one_pass_split,
          liveness_one_pass_def, LET_DEF, Abbr`lr'`]) >>
  (* FLOOKUP at bb.bb_label unchanged by suffix processing *)
  `FLOOKUP (liveness_one_pass cfg bbs
    (process_block cfg bbs lr' bb) suffix).lr_blocks bb.bb_label =
   FLOOKUP (process_block cfg bbs lr' bb).lr_blocks bb.bb_label` by
    (irule one_pass_flookup_not_in_order >> simp[]) >>
  gvs[process_block_def, LET_DEF, FLOOKUP_UPDATE] >>
  `FDOM (calculate_liveness bb
    (lookup_block_liveness lr' bb.bb_label with bl_out_vars :=
      list_union (lookup_block_liveness lr' bb.bb_label).bl_out_vars
        (calculate_out_vars cfg lr' bb bbs))).bl_inst_liveness =
   count (LENGTH bb.bb_instructions)` by
    (irule calculate_liveness_fdom >>
     Cases_on `bb.bb_instructions` >> fs[]) >>
  gvs[FDOM_FEMPTY]
QED

(* After ≥1 FUNPOW iteration, bl_inst_liveness ≠ FEMPTY for labels in order *)
Theorem iter_inst_nonempty[local]:
  ∀n fn lbl bb bl.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    n ≥ 1 ∧ wf_function fn ∧
    MEM lbl order ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    ¬NULL bb.bb_instructions ∧
    FLOOKUP (FUNPOW f n (init_liveness bbs)).lr_blocks lbl = SOME bl ==>
    bl.bl_inst_liveness ≠ FEMPTY
Proof
  simp[LET_DEF] >> rpt gen_tac >> strip_tac >>
  `∃m. n = SUC m` by (Cases_on `n` >> gvs[]) >>
  fs[FUNPOW_SUC] >>
  qabbrev_tac `lr_m = FUNPOW
    (λlr. liveness_one_pass (cfg_analyze fn) fn.fn_blocks lr
      (cfg_analyze fn).cfg_dfs_post) m (init_liveness fn.fn_blocks)` >>
  irule one_pass_inst_nonempty >>
  qexistsl_tac [`bb`, `fn.fn_blocks`, `cfg_analyze fn`,
    `bb.bb_label`, `lr_m`, `(cfg_analyze fn).cfg_dfs_post`] >>
  simp[cfg_analyze_dfs_post_distinct] >>
  mp_tac (Q.SPECL [`m`, `fn`] iter_lr_inv) >>
  simp[LET_DEF, Abbr`lr_m`] >> strip_tac >> fs[lr_inv_def]
QED

(* Helper: idx_of with default 0 for INDEX_OF *)
Definition idx_of_def:
  idx_of x l = case INDEX_OF x l of SOME i => i | NONE => 0
End

Theorem idx_of_bound[local]:
  ∀x l. idx_of x l < LENGTH l + 1
Proof
  rw[idx_of_def] >>
  Cases_on `INDEX_OF x l` >> simp[] >>
  fs[INDEX_OF_eq_SOME]
QED

(* If y appears in prefix and x is the pivot, y's idx_of is less than x's *)
Theorem idx_of_prefix[local]:
  ∀prefix x suffix y.
    ALL_DISTINCT (prefix ++ [x] ++ suffix) ∧ MEM y prefix ⇒
    idx_of y (prefix ++ [x] ++ suffix) < idx_of x (prefix ++ [x] ++ suffix)
Proof
  rpt strip_tac >>
  simp[idx_of_def] >>
  `INDEX_OF x (prefix ++ [x] ++ suffix) = SOME (LENGTH prefix)` by (
    simp[INDEX_OF_eq_SOME, EL_APPEND1, EL_APPEND2] >>
    rpt strip_tac >>
    `j < LENGTH prefix` by simp[] >>
    fs[ALL_DISTINCT_APPEND, EL_APPEND1] >>
    metis_tac[MEM_EL]) >>
  simp[] >>
  `MEM y (prefix ++ [x] ++ suffix)` by fs[MEM_APPEND] >>
  `∃i. INDEX_OF y (prefix ++ [x] ++ suffix) = SOME i` by
    (Cases_on `INDEX_OF y (prefix ++ [x] ++ suffix)` >> fs[INDEX_OF_eq_NONE]) >>
  simp[] >>
  fs[INDEX_OF_eq_SOME] >>
  `∃k. k < LENGTH prefix ∧ EL k prefix = y` by metis_tac[MEM_EL] >>
  `EL k (prefix ++ [x] ++ suffix) = y` by simp[EL_APPEND1] >>
  `k < LENGTH (prefix ++ [x] ++ suffix)` by simp[] >>
  `i < LENGTH (prefix ++ [x] ++ suffix)` by simp[] >>
  `k = i` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  simp[]
QED

(* Core soundness: v live at any FUNPOW iteration implies path to use.
   Lexicographic induction on (n, INDEX_OF lbl order):
   - n decreases when jumping to previous iteration (v was in lr_prev)
   - INDEX_OF decreases when following "new" chain within same iteration
     (one_pass_new_comes_from gives a successor processed earlier in order) *)
Theorem soundness_core[local]:
  ∀n fn lbl idx w.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let order = cfg.cfg_dfs_post in
    let f = λlr. liveness_one_pass cfg bbs lr order in
    let lr = FUNPOW f n (init_liveness bbs) in
    wf_function fn ∧
    MEM w (live_vars_at lr lbl idx) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs w ((lbl, idx) :: path)
Proof
  (* Combined measure: n * (K+1) + idx_of lbl order *)
  completeInduct_on
    `n * (LENGTH (cfg_analyze fn).cfg_dfs_post + 1) +
     idx_of lbl (cfg_analyze fn).cfg_dfs_post` >>
  simp[LET_DEF] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `order = cfg.cfg_dfs_post` >>
  qabbrev_tac `f = λlr. liveness_one_pass cfg bbs lr order` >>
  qabbrev_tac `lr = FUNPOW f n (init_liveness bbs)` >>
  qabbrev_tac `Klen = LENGTH order` >>
  (* n = 0: init has empty live sets *)
  Cases_on `n = 0`
  >- (
    gvs[Abbr`lr`, Abbr`f`] >>
    fs[live_vars_at_def, init_liveness_def, lookup_block_liveness_def] >>
    Cases_on `FLOOKUP (FOLDL (λm bb'. m |+ (bb'.bb_label, empty_block_liveness))
                FEMPTY bbs) lbl` >>
    imp_res_tac foldl_init_flookup >> gvs[empty_block_liveness_def]) >>
  (* n = SUC m *)
  `∃m. n = SUC m` by (Cases_on `n` >> gvs[]) >> gvs[] >>
  qabbrev_tac `lr_prev = FUNPOW f m (init_liveness bbs)` >>
  `lr = f lr_prev` by simp[Abbr`lr`, Abbr`lr_prev`, FUNPOW_SUC] >>
  (* Establish lr_inv *)
  `lr_inv bbs lr` by (
    simp[Abbr`lr`] >>
    mp_tac (Q.SPECL [`SUC m`, `fn`] iter_lr_inv) >>
    simp[LET_DEF, Abbr`cfg`, Abbr`bbs`]) >>
  (* Extract block *)
  `∃bb. lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
        idx < LENGTH bb.bb_instructions` by
    (irule live_vars_at_block >> metis_tac[]) >>
  (* Case split: v already in lr_prev? *)
  Cases_on `MEM w (live_vars_at lr_prev lbl idx)`
  >- (
    (* v in previous iteration: IH — measure strictly decreases *)
    qpat_x_assum `∀m'. m' < _ ⇒ _`
      (qspec_then `m * (Klen + 1) + idx_of lbl order` mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`m`, `fn`, `lbl`] mp_tac) >>
    simp[Abbr`Klen`, Abbr`order`, Abbr`cfg`] >>
    disch_then (qspecl_then [`idx`, `w`] mp_tac) >>
    simp[Abbr`lr_prev`, Abbr`f`, Abbr`bbs`]) >>
  (* v is new at this iteration *)
  (* intra_block_sound: case (a) used in block, case (b) reaches out_vars *)
  mp_tac (Q.SPECL [`bbs`, `lr`, `bb`, `lbl`, `idx`, `w`] intra_block_sound) >>
  impl_tac >- (fs[lr_inv_def] >> simp[]) >> strip_tac
  >- (
    (* Case (a): v used at j in same block *)
    irule use_in_block_path >> qexists_tac `bb` >>
    simp[] >> qexists_tac `j` >> simp[]) >>
  (* Case (b): v ∈ out_vars, no def from idx onward *)
  (* Helper: well-formed succ blocks *)
  `∀s sb. MEM s (cfg_succs_of cfg lbl) ∧ lookup_block s bbs = SOME sb ==>
          bb_well_formed sb` by (
    rpt strip_tac >>
    `MEM sb bbs` by (irule lookup_block_mem >> metis_tac[]) >>
    fs[wf_function_def, Abbr`bbs`]) >>
  (* First establish: lbl ∈ order (otherwise one_pass doesn't change lbl) *)
  `MEM lbl order` by (
    CCONTR_TAC >>
    `lr = liveness_one_pass cfg bbs lr_prev order` by
      (qpat_x_assum `lr = f lr_prev` mp_tac >> simp[Abbr`f`]) >>
    `live_vars_at lr lbl idx = live_vars_at lr_prev lbl idx` by
      (pop_assum SUBST1_TAC >>
       irule one_pass_live_not_in_order >> simp[]) >>
    metis_tac[]) >>
  (* Decompose order: order = prefix ++ [lbl] ++ suffix *)
  `∃prefix suffix. order = prefix ++ [lbl] ++ suffix` by (
    imp_res_tac MEM_SPLIT_APPEND_first >>
    qexistsl_tac [`pfx`, `sfx`] >> simp[]) >>
  `ALL_DISTINCT order` by
    simp[Abbr`order`, Abbr`cfg`, cfg_analyze_dfs_post_distinct] >>
  (* Apply one_pass_new_comes_from *)
  `MEM w (out_vars_of lr lbl)` by fs[GSYM out_vars_of_def] >>
  `lr_inv bbs lr_prev` by (
    qunabbrev_tac `lr_prev` >> qunabbrev_tac `f` >>
    qunabbrev_tac `bbs` >> qunabbrev_tac `cfg` >>
    mp_tac (Q.SPECL [`m`, `fn`] iter_lr_inv) >>
    simp_tac bool_ss [LET_THM] >> simp[]) >>
  `¬MEM w (out_vars_of lr_prev lbl)` by (
    spose_not_then assume_tac >> fs[] >>
    (* Now have: MEM w (out_vars_of lr_prev lbl), goal is F *)
    (* Case m=0: init has empty out_vars → direct contradiction *)
    Cases_on `m = 0`
    >- (`out_vars_of lr_prev lbl = []` by
          simp[Abbr`lr_prev`, Abbr`f`, init_out_vars_empty] >>
        fs[]) >>
    (* m ≥ 1: derive MEM w (live_vars_at lr_prev lbl idx) → contradiction *)
    `∃bl_prev. FLOOKUP lr_prev.lr_blocks lbl = SOME bl_prev ∧
               bl_prev.bl_inst_liveness ≠ FEMPTY` by (
      `lbl ∈ FDOM lr_prev.lr_blocks` by (
        fs[lr_inv_def, lr_shaped_def] >>
        `MEM lbl (MAP (λbb. bb.bb_label) bbs)` by
          (simp[MEM_MAP] >> qexists_tac `bb` >> fs[] >>
           irule lookup_block_mem >> metis_tac[]) >>
        gvs[]) >>
      `∃bl_prev'. FLOOKUP lr_prev.lr_blocks lbl = SOME bl_prev'` by
        metis_tac[flookup_thm] >>
      qexists_tac `bl_prev'` >> simp[] >>
      mp_tac (Q.SPECL [`m`, `fn`, `lbl`, `bb`, `bl_prev'`]
        iter_inst_nonempty) >>
      simp[LET_DEF] >>
      disch_then irule >> simp[] >>
      Cases_on `bb.bb_instructions` >> fs[]) >>
    `MEM w bl_prev.bl_out_vars` by
      (fs[out_vars_of_def, lookup_block_liveness_def]) >>
    `MEM w (live_vars_at lr_prev lbl idx)` by (
      irule out_vars_back_propagate >>
      conj_tac >- (qexists_tac `bl_prev` >> simp[]) >>
      qexistsl_tac [`bb`, `bbs`] >> fs[lr_inv_def]) >>
    metis_tac[]) >>
  `lr = liveness_one_pass cfg bbs lr_prev (prefix ++ [lbl] ++ suffix)` by
    (fs[Abbr`f`]) >>
  mp_tac (Q.SPECL [`prefix`, `lbl`, `suffix`, `cfg`, `bbs`, `lr_prev`,
    `bb`, `w`] one_pass_new_comes_from) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `lr = liveness_one_pass _ _ _ _` kall_tac
  >- (
    (* Case 1: v ∈ live_vars_at(lr_prev, succ_lbl, 0) → IH at m *)
    `∃succ_path.
      cfg_exec_path cfg ((succ_lbl, 0) :: succ_path) ∧
      used_before_defined bbs w ((succ_lbl, 0) :: succ_path)` by (
      qpat_x_assum `∀m'. m' < _ ⇒ _`
        (qspec_then `m * (Klen + 1) + idx_of succ_lbl order` mp_tac) >>
      impl_tac >- (
        `idx_of succ_lbl order ≤ Klen` by (
          `idx_of succ_lbl order < Klen + 1` suffices_by DECIDE_TAC >>
          simp[Abbr`Klen`, idx_of_bound]) >>
        REWRITE_TAC [MULT_CLAUSES] >> DECIDE_TAC) >>
      disch_then (qspecl_then [`m`, `fn`, `succ_lbl`] mp_tac) >>
      qpat_x_assum `_ = prefix ++ _ ++ suffix` kall_tac >>
      simp_tac bool_ss [Abbr`Klen`, Abbr`order`, Abbr`cfg`] >> simp[] >>
      disch_then (qspecl_then [`0`, `w`] mp_tac) >>
      qunabbrev_tac `lr_prev` >> qunabbrev_tac `f` >>
      simp[]) >>
    irule cross_block_path >>
    simp[Abbr`bbs`, Abbr`cfg`] >>
    conj_tac >- (qexists_tac `fn` >> simp[]) >>
    qexistsl_tac [`succ_lbl`, `succ_path`] >> simp[])
  >- (
    (* Case 2: succ in prefix, v at final result → IH at same n, lower INDEX_OF *)
    `∃succ_path.
      cfg_exec_path cfg ((succ_lbl, 0) :: succ_path) ∧
      used_before_defined bbs w ((succ_lbl, 0) :: succ_path)` by (
      qpat_x_assum `∀m'. m' < _ ⇒ _`
        (qspec_then `SUC m * (Klen + 1) + idx_of succ_lbl order` mp_tac) >>
      impl_tac
      >- ((* Need: measure < bound, i.e. idx_of succ < idx_of lbl *)
        `idx_of succ_lbl order < idx_of lbl order` suffices_by DECIDE_TAC >>
        metis_tac[idx_of_prefix]) >>
      disch_then (qspecl_then [`SUC m`, `fn`, `succ_lbl`] mp_tac) >>
      qpat_x_assum `order = prefix ++ _ ++ suffix`
        (fn eq_th =>
          qpat_x_assum `MEM w (live_vars_at (liveness_one_pass _ _ _ (prefix ++ _ ++ _)) _ _)`
            (fn th => assume_tac (ONCE_REWRITE_RULE [GSYM eq_th] th))) >>
      simp_tac bool_ss [Abbr`Klen`, Abbr`order`, Abbr`cfg`] >> simp[] >>
      disch_then (qspecl_then [`0`, `w`] mp_tac) >>
      qunabbrev_tac `lr_prev` >> qunabbrev_tac `lr` >>
      qunabbrev_tac `f` >>
      simp[]) >>
    irule cross_block_path >>
    simp[Abbr`bbs`, Abbr`cfg`] >>
    conj_tac >- (qexists_tac `fn` >> simp[]) >>
    qexistsl_tac [`succ_lbl`, `succ_path`] >> simp[])
  >- (
    (* Case 3: PHI source *)
    `bb_well_formed succ_bb` by metis_tac[] >>
    `∃succ_path.
      cfg_exec_path cfg ((succ_lbl, 0) :: succ_path) ∧
      used_before_defined bbs w ((succ_lbl, 0) :: succ_path)` by
      (irule phi_use_path >>
       qexistsl_tac [`inst`, `lbl`] >>
       imp_res_tac lookup_block_label >> simp[]) >>
    irule cross_block_path >>
    simp[Abbr`bbs`, Abbr`cfg`] >>
    conj_tac >- (qexists_tac `fn` >> simp[]) >>
    qexistsl_tac [`succ_lbl`, `succ_path`] >> simp[])
QED

(* Bridge: liveness_analyze = FUNPOW f N init for some N *)
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
  simp[LET_DEF] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `order = cfg.cfg_dfs_post` >>
  qabbrev_tac `f = λlr. liveness_one_pass cfg bbs lr order` >>
  `liveness_analyze fn = df_iterate f (init_liveness bbs)` by
    (simp[Abbr`f`, Abbr`order`, Abbr`bbs`, Abbr`cfg`,
          liveness_analyze_def, liveness_iterate_def]) >>
  (* Step 1: f eventually reaches a fixpoint *)
  sg `∃n. f (FUNPOW f n (init_liveness bbs)) = FUNPOW f n (init_liveness bbs)` >- (
    CCONTR_TAC >> fs[] >>
    `∀k. set_live_count (FUNPOW f k (init_liveness bbs)) <
         set_live_count (f (FUNPOW f k (init_liveness bbs)))` by (
      rpt strip_tac >> qunabbrev_tac `f` >> simp[] >>
      irule one_pass_set_measure_increase >>
      conj_tac
      >- (first_x_assum (qspec_then `k` mp_tac) >> simp[])
      >- (qunabbrev_tac `order` >> qunabbrev_tac `bbs` >> qunabbrev_tac `cfg` >>
          mp_tac (Q.SPECL [`k`, `fn`] iter_lr_inv) >>
          simp_tac bool_ss [LET_THM] >> simp[])) >>
    `∀k:num. k ≤ set_live_count (FUNPOW f k (init_liveness bbs))` by (
      Induct >> simp[] >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[FUNPOW_SUC] >> DECIDE_TAC) >>
    `∀k. lr_inv bbs (FUNPOW f k (init_liveness bbs))` by (
      rpt strip_tac >>
      qunabbrev_tac `f` >> qunabbrev_tac `order` >>
      qunabbrev_tac `bbs` >> qunabbrev_tac `cfg` >>
      mp_tac (Q.SPECL [`k`, `fn`] iter_lr_inv) >>
      simp_tac bool_ss [LET_THM] >> simp[]) >>
    `∀k. set_live_count (FUNPOW f k (init_liveness bbs)) ≤
         (LENGTH (nub (fn_all_vars bbs)) + 1) *
         (fn_total_insts bbs + LENGTH bbs)` by (
      rpt strip_tac >> irule set_live_count_bounded >>
      pop_assum (qspec_then `k` mp_tac) >> simp[lr_inv_def]) >>
    qpat_x_assum `∀k. k ≤ _`
      (qspec_then `(LENGTH (nub (fn_all_vars bbs)) + 1) *
                   (fn_total_insts bbs + LENGTH bbs) + 1` mp_tac) >>
    qpat_x_assum `∀k. _ ≤ _`
      (qspec_then `(LENGTH (nub (fn_all_vars bbs)) + 1) *
                   (fn_total_insts bbs + LENGTH bbs) + 1` mp_tac) >>
    DECIDE_TAC) >>
  (* Step 2: df_iterate = FUNPOW via OWHILE *)
  `∃N. liveness_analyze fn = FUNPOW f N (init_liveness bbs)` by (
    simp[df_iterate_def] >>
    `OWHILE (λy. f y ≠ y) f (init_liveness bbs) =
     SOME (FUNPOW f ($LEAST (λn. ¬(λy. f y ≠ y) (FUNPOW f n (init_liveness bbs))))
                    (init_liveness bbs))` by
      (simp[OWHILE_def] >> qexists_tac `n` >> simp[]) >>
    imp_res_tac OWHILE_WHILE >> simp[] >>
    qexists_tac `$LEAST (λn. ¬(λy. f y ≠ y)
                              (FUNPOW f n (init_liveness bbs)))` >> simp[]) >>
  (* Step 3: Apply soundness_core *)
  gvs[] >>
  mp_tac (Q.SPECL [`N`, `fn`, `lbl`, `idx`, `v`] soundness_core) >>
  simp[LET_DEF]
QED
