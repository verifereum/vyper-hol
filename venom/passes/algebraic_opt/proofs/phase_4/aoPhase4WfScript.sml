(* Phase 4 WF preservation: ao_cmp_flip_function
 *
 * TOP-LEVEL:
 *   ao_phase4_preserves_wf — wf_function preserved through phase 4
 *
 * Key helpers:
 *   ao_cmp_flip_scan_no_term — terminators untouched by scan
 *   ao_cmp_flip_scan_no_phi  — PHIs untouched by scan
 *)

Theory aoPhase4Wf
Ancestors
  algebraicOptDefs aoPhase3Wf
  venomState venomWf venomInst passSimulationProps
  passSharedDefs alist
Libs
  pairLib BasicProvers

(* ===== ao_cmp_flip_apply_inst properties ===== *)

Theorem ao_cmp_flip_apply_ne:
  !mid flips removes inserts inst.
    ao_cmp_flip_apply_inst mid flips removes inserts inst <> []
Proof
  rpt gen_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac
QED

Triviality ao_cmp_flip_apply_non_term[local]:
  !mid flips removes inserts inst.
    ~is_terminator inst.inst_opcode /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
       ~is_terminator opc) ==>
    EVERY (\r. ~is_terminator r.inst_opcode)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  res_tac
QED

Triviality flip_cmp_non_term[local]:
  !opc. is_comparator opc ==> ~is_terminator (flip_comparison_opcode opc)
Proof
  simp[is_comparator_def] >> rpt strip_tac >>
  gvs[flip_comparison_opcode_def, is_terminator_def]
QED

Triviality flip_cmp_non_phi[local]:
  !opc. is_comparator opc ==> flip_comparison_opcode opc <> PHI
Proof
  simp[is_comparator_def] >> rpt strip_tac >>
  gvs[flip_comparison_opcode_def]
QED

(* ===== ao_cmp_flip_scan characterization ===== *)

Triviality ao_cmp_flip_scan_non_comp_unchanged[local]:
  !dfg h insts flips removes inserts.
    ao_cmp_flip_scan dfg (h::insts) = (flips, removes, inserts) /\
    ~is_comparator h.inst_opcode ==>
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts)
Proof
  rpt strip_tac >>
  gvs[ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Triviality scan_step_detail[local]:
  !dfg h rest fl0 rm0 ins0 fl1 rm1 ins1.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (fl1, rm1, ins1) ==>
    (fl1 = fl0 /\ rm1 = rm0 /\ ins1 = ins0) \/
    (?w op1 out_var.
       is_comparator h.inst_opcode /\
       h.inst_operands = [op1; Lit w] /\
       h.inst_outputs = [out_var] /\
       fl1 = (h.inst_id, flip_comparison_opcode h.inst_opcode,
              (if h.inst_opcode = GT \/ h.inst_opcode = SGT
               then w + 1w else w - 1w), op1) :: fl0 /\
       LENGTH (dfg_get_uses dfg out_var) = 1 /\
       ((rm1 = (HD (dfg_get_uses dfg out_var)).inst_id :: rm0 /\
         ins1 = ins0 /\
         (HD (dfg_get_uses dfg out_var)).inst_opcode = ISZERO) \/
        (rm1 = rm0 /\
         ins1 = ((HD (dfg_get_uses dfg out_var)).inst_id, out_var,
                  ao_fresh_var h.inst_id "iz", h.inst_id) :: ins0 /\
         (HD (dfg_get_uses dfg out_var)).inst_opcode = ASSERT)))
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC [ao_cmp_flip_scan_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> simp[] >>
  every_case_tac >> simp[] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[is_comparator_def, flip_comparison_opcode_def,
    ao_unsigned_boundaries_def, ao_signed_boundaries_def, LET_THM]
QED

Triviality scan_step_flips_subset[local]:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    flips = fl0 \/
    (?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0 /\
                 is_comparator h.inst_opcode)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >> strip_tac >> gvs[]
QED

Triviality scan_step_removes_subset[local]:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    removes = rm0 \/
    (?v ui. removes = ui.inst_id :: rm0 /\
            MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  qexists_tac `out_var` >>
  qexists_tac `HD (dfg_get_uses dfg out_var)` >>
  `dfg_get_uses dfg out_var <> []` by
    (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
  simp[rich_listTheory.HEAD_MEM]
QED

Theorem scan_step_inserts_subset:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    inserts = ins0 \/
    (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: ins0 /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  qexists_tac `HD (dfg_get_uses dfg out_var)` >>
  `dfg_get_uses dfg out_var <> []` by
    (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
  simp[rich_listTheory.HEAD_MEM]
QED

Triviality ao_cmp_flip_scan_flips_non_term[local]:
  !dfg insts flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) ==>
    !id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
      ~is_terminator opc
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  rpt strip_tac
  >- metis_tac[]
  >| [Cases_on `id = h.inst_id` >> gvs[]
      >- (gvs[is_comparator_def] >>
          gvs[flip_comparison_opcode_def, is_terminator_def])
      >> metis_tac[],
      Cases_on `id = h.inst_id` >> gvs[]
      >- (gvs[is_comparator_def] >>
          gvs[flip_comparison_opcode_def, is_terminator_def])
      >> metis_tac[]]
QED

Triviality ao_cmp_flip_scan_flips_non_phi[local]:
  !dfg insts flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) ==>
    !id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
      opc <> PHI
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  rpt strip_tac
  >- metis_tac[]
  >| [Cases_on `id = h.inst_id` >> gvs[]
      >- (gvs[is_comparator_def] >>
          gvs[flip_comparison_opcode_def])
      >> metis_tac[],
      Cases_on `id = h.inst_id` >> gvs[]
      >- (gvs[is_comparator_def] >>
          gvs[flip_comparison_opcode_def])
      >> metis_tac[]]
QED

Triviality scan_flips_are_comparators[local]:
  !dfg insts flips removes inserts id opc w op.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP flips id = SOME (opc, w, op) ==>
    ?i. MEM i insts /\ i.inst_id = id /\ is_comparator i.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `flips = flips' \/
   (?opc' w' op1. flips = (h.inst_id, opc', w', op1) :: flips' /\
                is_comparator h.inst_opcode)` by
    metis_tac[scan_step_flips_subset] >>
  gvs[]
  >- (first_x_assum drule_all >> metis_tac[])
  >> metis_tac[]
QED

Triviality scan_removes_are_iszero[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id removes ==>
    ?v ui. MEM ui (dfg_get_uses dfg v) /\ ui.inst_id = id /\
           ui.inst_opcode = ISZERO
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `removes = removes' \/
   (?v ui. removes = ui.inst_id :: removes' /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)` by
    metis_tac[scan_step_removes_subset] >>
  gvs[] >> metis_tac[]
QED

Triviality scan_inserts_are_assert[local]:
  !dfg insts flips removes inserts id cmp_out fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP inserts id = SOME (cmp_out, fresh, cmp_id) ==>
    ?v ui. MEM ui (dfg_get_uses dfg v) /\ ui.inst_id = id /\
           ui.inst_opcode = ASSERT
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `inserts = inserts' \/
   (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: inserts' /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[] >> metis_tac[]
QED

(* ===== Untouched properties ===== *)

Triviality terminator_not_comparator[local]:
  !opc. is_terminator opc ==> ~is_comparator opc
Proof
  Cases >> simp[is_terminator_def, is_comparator_def]
QED

Triviality phi_not_comparator[local]:
  ~is_comparator PHI
Proof
  simp[is_comparator_def]
QED

Triviality all_distinct_id_eq[local]:
  !l x y. ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
           MEM x l /\ MEM y l /\ x.inst_id = y.inst_id ==> x = y
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[listTheory.MEM_MAP]
QED

Triviality untouched_by_scan[local]:
  !dfg insts flips removes inserts inst.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM inst insts /\
    ~is_comparator inst.inst_opcode /\
    inst.inst_opcode <> ISZERO /\
    inst.inst_opcode <> ASSERT /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i insts) ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac
  >- (CCONTR_TAC >> gvs[] >>
      `?val. ALOOKUP flips inst.inst_id = SOME val` by
        (Cases_on `ALOOKUP flips inst.inst_id` >> gvs[]) >>
      PairCases_on `val` >>
      drule_all scan_flips_are_comparators >>
      strip_tac >> metis_tac[all_distinct_id_eq])
  >- (CCONTR_TAC >> gvs[] >>
      drule_all scan_removes_are_iszero >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by metis_tac[all_distinct_id_eq] >>
      gvs[])
  >- (CCONTR_TAC >> gvs[] >>
      `?val. ALOOKUP inserts inst.inst_id = SOME val` by
        (Cases_on `ALOOKUP inserts inst.inst_id` >> gvs[]) >>
      PairCases_on `val` >>
      drule_all scan_inserts_are_assert >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by metis_tac[all_distinct_id_eq] >>
      gvs[])
QED

(* Terminators are untouched by scan *)
Theorem ao_cmp_flip_scan_no_term:
  !dfg insts flips removes inserts inst.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM inst insts /\
    is_terminator inst.inst_opcode /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i insts) ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >>
  `~is_comparator inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_terminator_def, is_comparator_def]) >>
  `inst.inst_opcode <> ISZERO` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `inst.inst_opcode <> ASSERT` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  metis_tac[untouched_by_scan]
QED

(* PHIs are untouched by scan *)
Theorem ao_cmp_flip_scan_no_phi:
  !dfg insts flips removes inserts inst.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM inst insts /\
    inst.inst_opcode = PHI /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i insts) ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >>
  `~is_comparator inst.inst_opcode` by gvs[is_comparator_def] >>
  `inst.inst_opcode <> ISZERO` by gvs[] >>
  `inst.inst_opcode <> ASSERT` by gvs[] >>
  metis_tac[untouched_by_scan]
QED

(* Untouched instruction maps to singleton *)
Triviality ao_cmp_flip_apply_untouched[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  gvs[]
QED

Triviality ao_cmp_flip_apply_non_phi[local]:
  !mid flips removes inserts inst.
    inst.inst_opcode <> PHI /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==> opc <> PHI) ==>
    EVERY (\r. r.inst_opcode <> PHI)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[] >>
  CCONTR_TAC >> gvs[]
QED

(* ===== Phase 4 preserves wf_function ===== *)

Triviality flat_map_ne[local]:
  !f l. l <> [] /\ (!x. MEM x l ==> f x <> []) ==>
    FLAT (MAP f l) <> []
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `f h` >> gvs[]
QED

Triviality flat_map_last_singleton[local]:
  !f l x. l <> [] /\ (!y. MEM y l ==> f y <> []) /\
    f (LAST l) = [x] ==>
    LAST (FLAT (MAP f l)) = x
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l`
  >- (gvs[] >> Cases_on `f h` >> gvs[])
  >> rename1 `h1::h2::t` >>
  `h2::t <> []` by simp[] >>
  `FLAT (MAP f (h2::t)) <> []` by (irule flat_map_ne >> simp[]) >>
  `f (LAST (h2::t)) = [x]` by
    (qpat_x_assum `f (LAST _) = _` mp_tac >>
     simp[listTheory.LAST_CONS]) >>
  `LAST (FLAT (MAP f (h2::t))) = x` by
    (first_x_assum (qspecl_then [`f`,`x`] mp_tac) >> simp[]) >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL]
QED

Triviality flat_map_split_last[local]:
  !(f:'a -> 'b list) l.
    l <> [] /\ (!x. MEM x l ==> f x <> []) ==>
    FLAT (MAP f l) = FLAT (MAP f (FRONT l)) ++ f (LAST l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l`
  >- simp[]
  >> rename1 `h1::h2::t` >>
  `h2::t <> []` by simp[] >>
  `FLAT (MAP f (h2::t)) =
   FLAT (MAP f (FRONT (h2::t))) ++ f (LAST (h2::t))` by
    (first_x_assum irule >> simp[]) >>
  simp[listTheory.FRONT_CONS]
QED

Triviality every_flat[local]:
  !P ls. EVERY P (FLAT ls) <=> EVERY (EVERY P) ls
Proof
  Induct_on `ls` >>
  simp[listTheory.EVERY_APPEND]
QED

Triviality fn_insts_blocks_mem[local]:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Triviality map_id_fn_insts_blocks[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem fn_inst_ids_to_fn_insts:
  !fn. fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def, map_id_fn_insts_blocks]
QED

Triviality all_distinct_sub[local]:
  !(l1:'a list) l2.
    ALL_DISTINCT l2 /\ (!x. MEM x l1 ==> MEM x l2) /\
    ALL_DISTINCT l1 ==>
    ALL_DISTINCT l1
Proof
  simp[]
QED

Triviality all_distinct_flat_mem[local]:
  !bbs (bb:'a list). ALL_DISTINCT (FLAT bbs) /\ MEM bb bbs ==>
    ALL_DISTINCT bb
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[listTheory.ALL_DISTINCT_APPEND]
QED

Triviality block_inst_ids_distinct[local]:
  !fn bb. fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >> fs[fn_inst_ids_distinct_def] >>
  irule all_distinct_flat_mem >>
  qexists_tac `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
                 fn.fn_blocks` >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[]
QED

Triviality term_untouched[local]:
  !dfg all_insts flips removes inserts mid inst.
    ao_cmp_flip_scan dfg all_insts = (flips, removes, inserts) /\
    MEM inst all_insts /\
    is_terminator inst.inst_opcode /\
    ALL_DISTINCT (MAP (\i. i.inst_id) all_insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i all_insts) ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >>
  `ALOOKUP flips inst.inst_id = NONE /\
   ~MEM inst.inst_id removes /\
   ALOOKUP inserts inst.inst_id = NONE` by
    metis_tac[ao_cmp_flip_scan_no_term] >>
  simp[ao_cmp_flip_apply_inst_def] >> gvs[]
QED

Triviality phi_untouched[local]:
  !dfg all_insts flips removes inserts mid inst.
    ao_cmp_flip_scan dfg all_insts = (flips, removes, inserts) /\
    MEM inst all_insts /\
    inst.inst_opcode = PHI /\
    ALL_DISTINCT (MAP (\i. i.inst_id) all_insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i all_insts) ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >>
  `ALOOKUP flips inst.inst_id = NONE /\
   ~MEM inst.inst_id removes /\
   ALOOKUP inserts inst.inst_id = NONE` by
    metis_tac[ao_cmp_flip_scan_no_phi] >>
  simp[ao_cmp_flip_apply_inst_def] >> gvs[]
QED

Triviality every_non_term_flat_map[local]:
  !(f:instruction -> instruction list) insts flips.
    (!inst. MEM inst insts ==> ~is_terminator inst.inst_opcode ==>
       EVERY (\r. ~is_terminator r.inst_opcode) (f inst)) /\
    (!inst. MEM inst insts ==> is_terminator inst.inst_opcode ==>
       f inst = [inst]) /\
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts ==>
    EVERY (\inst. ~is_terminator inst.inst_opcode) (FLAT (MAP f insts))
Proof
  Induct_on `insts` >> simp[listTheory.EVERY_APPEND] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Triviality every_non_phi_flat_map[local]:
  !(f:instruction -> instruction list) insts flips.
    (!inst. MEM inst insts ==> inst.inst_opcode <> PHI ==>
       EVERY (\r. r.inst_opcode <> PHI) (f inst)) /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==>
       f inst = [inst]) /\
    EVERY (\inst. inst.inst_opcode <> PHI) insts ==>
    EVERY (\inst. inst.inst_opcode <> PHI) (FLAT (MAP f insts))
Proof
  Induct_on `insts` >> simp[listTheory.EVERY_APPEND] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

(* FRONT elements of a well-formed block are non-terminators *)
Triviality bb_wf_front_non_term[local]:
  !bb. bb_well_formed bb ==>
    EVERY (\inst. ~is_terminator inst.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  simp[listTheory.EVERY_EL] >> rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `LENGTH (FRONT bb.bb_instructions) = PRE (LENGTH bb.bb_instructions)`
    by (Cases_on `bb.bb_instructions` >> gvs[rich_listTheory.LENGTH_FRONT]) >>
  `n < LENGTH bb.bb_instructions` by simp[] >>
  `EL n (FRONT bb.bb_instructions) = EL n bb.bb_instructions` by
    (irule rich_listTheory.EL_FRONT >>
     Cases_on `bb.bb_instructions` >> gvs[]) >>
  `is_terminator (EL n bb.bb_instructions).inst_opcode` by gvs[] >>
  `n = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  gvs[]
QED

(* flat-map of EVERY non-term inputs gives non-term outputs *)
Triviality flat_map_every_non_term[local]:
  !(ap:instruction -> instruction list) insts.
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts /\
    (!inst. MEM inst insts ==>
       EVERY (\r. ~is_terminator r.inst_opcode) (ap inst)) ==>
    EVERY (\r. ~is_terminator r.inst_opcode) (FLAT (MAP ap insts))
Proof
  Induct_on `insts` >>
  simp[listTheory.EVERY_APPEND] >> metis_tac[]
QED

(* flat-map of EVERY non-phi inputs gives non-phi outputs *)
Triviality flat_map_every_non_phi[local]:
  !(ap:instruction -> instruction list) insts.
    EVERY (\inst. inst.inst_opcode <> PHI) insts /\
    (!inst. MEM inst insts ==>
       EVERY (\r. r.inst_opcode <> PHI) (ap inst)) ==>
    EVERY (\r. r.inst_opcode <> PHI) (FLAT (MAP ap insts))
Proof
  Induct_on `insts` >>
  simp[listTheory.EVERY_APPEND] >> metis_tac[]
QED

Triviality phi_prefix_cons[local]:
  !h insts.
    h.inst_opcode = PHI /\
    (!i j. i < j /\ j < LENGTH (h::insts) /\
           (EL j (h::insts)).inst_opcode = PHI ==>
           (EL i (h::insts)).inst_opcode = PHI) ==>
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI)
Proof
  rpt strip_tac >>
  `SUC i < SUC j` by simp[] >>
  `SUC j < LENGTH (h::insts)` by simp[] >>
  `(EL (SUC j) (h::insts)).inst_opcode = PHI` by simp[] >>
  `(EL (SUC i) (h::insts)).inst_opcode = PHI` by metis_tac[] >>
  gvs[]
QED

Triviality phi_prefix_non_phi_tl[local]:
  !h insts.
    h.inst_opcode <> PHI /\
    (!i j. i < j /\ j < LENGTH (h::insts) /\
           (EL j (h::insts)).inst_opcode = PHI ==>
           (EL i (h::insts)).inst_opcode = PHI) ==>
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI)
Proof
  rpt strip_tac >>
  `SUC i < SUC j` by simp[] >>
  `SUC j < LENGTH (h::insts)` by simp[] >>
  `(EL (SUC j) (h::insts)).inst_opcode = PHI` by simp[] >>
  `(EL (SUC i) (h::insts)).inst_opcode = PHI` by metis_tac[] >>
  gvs[]
QED

(* PHI prefix via EVERY split *)
Triviality phi_prefix_from_split[local]:
  !(phis:instruction list) rest.
    EVERY (\i. i.inst_opcode = PHI) phis /\
    EVERY (\i. i.inst_opcode <> PHI) rest ==>
    !i j. i < j /\ j < LENGTH (phis ++ rest) /\
      (EL j (phis ++ rest)).inst_opcode = PHI ==>
      (EL i (phis ++ rest)).inst_opcode = PHI
Proof
  rpt strip_tac >>
  `j < LENGTH phis` by
    (CCONTR_TAC >> gvs[] >>
     `LENGTH phis <= j` by simp[] >>
     `j - LENGTH phis < LENGTH rest` by simp[] >>
     `MEM (EL (j - LENGTH phis) rest) rest` by
       (simp[listTheory.MEM_EL] >>
        qexists_tac `j - LENGTH phis` >> simp[]) >>
     `(EL (j - LENGTH phis) rest).inst_opcode <> PHI` by
       (qpat_x_assum `EVERY _ rest`
          (strip_assume_tac o SIMP_RULE std_ss [listTheory.EVERY_MEM]) >>
        res_tac) >>
     qpat_x_assum `_ .inst_opcode = PHI` mp_tac >>
     simp[rich_listTheory.EL_APPEND2]) >>
  `i < LENGTH phis` by simp[] >>
  `MEM (EL i phis) phis` by
    (simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >>
  simp[rich_listTheory.EL_APPEND1] >>
  qpat_x_assum `EVERY _ phis`
    (strip_assume_tac o SIMP_RULE std_ss [listTheory.EVERY_MEM]) >>
  res_tac
QED

Triviality flat_map_phi_split[local]:
  !(phis:instruction list) (ap:instruction -> instruction list) rest.
    (!inst. MEM inst phis ==> ap inst = [inst]) ==>
    FLAT (MAP ap (phis ++ rest)) =
      phis ++ FLAT (MAP ap rest)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `ap h = [h]` by metis_tac[] >>
  `FLAT (MAP ap (phis ++ rest)) = phis ++ FLAT (MAP ap rest)` by
    (first_x_assum irule >> metis_tac[]) >>
  gvs[]
QED

(* PHI prefix preserved by FLAT MAP *)
Triviality phi_split_exists[local]:
  !insts.
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    ?phis rest.
      insts = phis ++ rest /\
      EVERY (\i. i.inst_opcode = PHI) phis /\
      EVERY (\i. i.inst_opcode <> PHI) rest
Proof
  Induct >- (rpt strip_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]) >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`!i j. i < j /\ j < LENGTH insts /\
             (EL j insts).inst_opcode = PHI ==>
             (EL i insts).inst_opcode = PHI` by
       metis_tac[phi_prefix_cons] >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [`h::phis`, `rest`] >> simp[])
  >> qexistsl_tac [`[]`, `h::insts`] >> simp[] >>
  simp[listTheory.EVERY_EL] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `(EL (SUC n) (h::insts)).inst_opcode = PHI` by simp[] >>
  `SUC n < LENGTH (h::insts)` by simp[] >>
  `0 < SUC n` by simp[] >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Triviality phi_prefix_flat_map[local]:
  !(ap:instruction -> instruction list) insts.
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       ap inst = [inst]) /\
    (!inst. MEM inst insts /\ inst.inst_opcode <> PHI ==>
       EVERY (\r. r.inst_opcode <> PHI) (ap inst)) /\
    (!inst. MEM inst insts ==> ap inst <> []) ==>
    (!i j. i < j /\ j < LENGTH (FLAT (MAP ap insts)) /\
           (EL j (FLAT (MAP ap insts))).inst_opcode = PHI ==>
           (EL i (FLAT (MAP ap insts))).inst_opcode = PHI)
Proof
  rpt strip_tac >>
  drule phi_split_exists >> strip_tac >> gvs[] >>
  `FLAT (MAP ap (phis ++ rest)) = phis ++ FLAT (MAP ap rest)` by
    (irule flat_map_phi_split >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     fs[listTheory.EVERY_MEM] >> res_tac) >>
  `EVERY (\i. i.inst_opcode <> PHI) (FLAT (MAP ap rest))` by
    (irule flat_map_every_non_phi >> simp[] >>
     rpt strip_tac >> res_tac >>
     fs[listTheory.EVERY_MEM]) >>
  gvs[] >>
  drule phi_prefix_from_split >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[]
QED

(* Main helper: flat-map preserves bb_well_formed *)
Triviality phase4_bb_wf_preserved[local]:
  !all_insts flips removes inserts dfg mid bb.
    bb_well_formed bb /\
    ao_cmp_flip_scan dfg all_insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) all_insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i all_insts) /\
    (!inst. MEM inst bb.bb_instructions ==> MEM inst all_insts) /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
       ~is_terminator opc) /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
       opc <> PHI) ==>
    bb_well_formed (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb.bb_instructions))
Proof
  rpt strip_tac >>
  qabbrev_tac `ap = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  fs[bb_well_formed_def] >>
  `bb.bb_instructions <> []` by simp[] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  `MEM (LAST bb.bb_instructions) all_insts` by metis_tac[] >>
  `!inst. ap inst <> []` by simp[Abbr `ap`, ao_cmp_flip_apply_ne] >>
  `ap (LAST bb.bb_instructions) = [LAST bb.bb_instructions]` by
    (simp[Abbr `ap`] >> irule ao_cmp_flip_apply_untouched >>
     metis_tac[ao_cmp_flip_scan_no_term]) >>
  `bb_well_formed bb` by
    (simp[bb_well_formed_def] >> metis_tac[]) >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode) (FRONT bb.bb_instructions)` by
    (irule bb_wf_front_non_term >> simp[]) >>
  rpt conj_tac
  (* non-empty *)
  >- (simp[Abbr `ap`] >> irule flat_map_ne >> simp[ao_cmp_flip_apply_ne])
  (* LAST is terminator *)
  >- (`LAST (FLAT (MAP ap bb.bb_instructions)) =
       LAST bb.bb_instructions` by
        (irule flat_map_last_singleton >> simp[]) >>
      simp[])
  (* only LAST is terminator *)
  >- (rpt strip_tac >>
      `FLAT (MAP ap bb.bb_instructions) =
       FLAT (MAP ap (FRONT bb.bb_instructions)) ++
       ap (LAST bb.bb_instructions)` by
        (irule flat_map_split_last >> simp[]) >>
      `EVERY (\inst. ~is_terminator inst.inst_opcode)
         (FLAT (MAP ap (FRONT bb.bb_instructions)))` by
        (irule flat_map_every_non_term >> simp[] >>
         rpt gen_tac >> strip_tac >>
         rename1 `MEM inst0 (FRONT _)` >>
         `~is_terminator inst0.inst_opcode` by
           (fs[listTheory.EVERY_MEM] >> res_tac) >>
         fs[Abbr `ap`] >>
         irule ao_cmp_flip_apply_non_term >> simp[] >>
         rpt strip_tac >> res_tac) >>
      gvs[] >>
      Cases_on `i < LENGTH (FLAT (MAP ap (FRONT bb.bb_instructions)))`
      >- (fs[rich_listTheory.EL_APPEND1] >>
          fs[listTheory.EVERY_EL] >>
          first_x_assum drule >> simp[])
      >> fs[rich_listTheory.EL_APPEND2] >>
      `i - LENGTH (FLAT (MAP ap (FRONT bb.bb_instructions))) = 0` by simp[] >>
      simp[])
  (* phi prefix *)
  >- (`(!i j. i < j /\ j < LENGTH (FLAT (MAP ap bb.bb_instructions)) /\
           (EL j (FLAT (MAP ap bb.bb_instructions))).inst_opcode = PHI ==>
           (EL i (FLAT (MAP ap bb.bb_instructions))).inst_opcode = PHI)` by
       (`(!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
           ap inst = [inst])` by
          (rpt strip_tac >> simp[Abbr `ap`] >>
           irule ao_cmp_flip_apply_untouched >>
           `MEM inst all_insts` by metis_tac[] >>
           metis_tac[ao_cmp_flip_scan_no_phi]) >>
        `(!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI ==>
           EVERY (\r. r.inst_opcode <> PHI) (ap inst))` by
          (rpt strip_tac >> simp[Abbr `ap`] >>
           irule ao_cmp_flip_apply_non_phi >> simp[] >>
           rpt strip_tac >> res_tac) >>
        `!inst. MEM inst bb.bb_instructions ==> ap inst <> []` by
           simp[] >>
        metis_tac[phi_prefix_flat_map]) >>
      simp[])
QED

(* bb_succs preserved: terminators are untouched so successors don't change *)
Triviality phase4_bb_succs[local]:
  !all_insts flips removes inserts dfg mid bb.
    bb_well_formed bb /\
    ao_cmp_flip_scan dfg all_insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) all_insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i all_insts) /\
    (!inst. MEM inst bb.bb_instructions ==> MEM inst all_insts) ==>
    bb_succs (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb.bb_instructions)) = bb_succs bb
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  `bb.bb_instructions <> []` by simp[] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  `MEM (LAST bb.bb_instructions) all_insts` by metis_tac[] >>
  `ao_cmp_flip_apply_inst mid flips removes inserts
     (LAST bb.bb_instructions) = [LAST bb.bb_instructions]` by
    (irule ao_cmp_flip_apply_untouched >>
     metis_tac[ao_cmp_flip_scan_no_term]) >>
  `!inst. ao_cmp_flip_apply_inst mid flips removes inserts inst <> []` by
    simp[ao_cmp_flip_apply_ne] >>
  `FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
             bb.bb_instructions) <> []` by
    (irule flat_map_ne >> simp[]) >>
  `LAST (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                    bb.bb_instructions)) =
   LAST bb.bb_instructions` by
    (irule flat_map_last_singleton >> simp[]) >>
  simp[bb_succs_def] >>
  Cases_on `FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                      bb.bb_instructions)` >> gvs[] >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED


(* ===== fn_inst_ids_distinct helpers ===== *)

Triviality ao_fresh_id_gt[local]:
  !mid id slot. ao_fresh_id mid id slot > mid
Proof
  simp[ao_fresh_id_def]
QED

Triviality ao_fresh_id_inj[local]:
  !mid id1 id2 s. ao_fresh_id mid id1 s = ao_fresh_id mid id2 s ==> id1 = id2
Proof
  simp[ao_fresh_id_def]
QED

Triviality apply_inst_id_cases[local]:
  !mid flips removes inserts inst x.
    MEM x (ao_cmp_flip_apply_inst mid flips removes inserts inst) ==>
    x.inst_id = inst.inst_id \/
    ?cmp_id. x.inst_id = ao_fresh_id mid cmp_id 0
Proof
  rpt strip_tac >>
  gvs[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality apply_inst_ids_flip[local]:
  !mid flips removes inserts inst opc w op.
    ALOOKUP flips inst.inst_id = SOME (opc, w, op) ==>
    MAP (\i. i.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst) =
    [inst.inst_id]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

Triviality apply_inst_ids_remove[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    MEM inst.inst_id removes ==>
    MAP (\i. i.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst) =
    [inst.inst_id]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

Triviality apply_inst_ids_insert[local]:
  !mid flips removes inserts inst cmp_out fresh_v cmp_id.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh_v, cmp_id) ==>
    MAP (\i. i.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst) =
    [ao_fresh_id mid cmp_id 0; inst.inst_id]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

Triviality apply_inst_ids_none[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    MAP (\i. i.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst) =
    [inst.inst_id]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

Triviality all_distinct_pred_split_local[local]:
  !(l:num list) mid.
    ALL_DISTINCT (FILTER (\id. id <= mid) l) /\
    ALL_DISTINCT (FILTER (\id. ~(id <= mid)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h <= mid` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  qexists_tac `mid` >> simp[] >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Theorem scan_inserts_cmp_id_mem:
  !dfg insts flips removes inserts id out_var fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (id, out_var, fresh, cmp_id) inserts ==>
    ?i. MEM i insts /\ i.inst_id = cmp_id
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `inserts = inserts' \/
   (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: inserts' /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
  >- (first_x_assum drule_all >> strip_tac >> metis_tac[])
  >> gvs[] >> metis_tac[]
QED

Theorem scan_inserts_fresh_form:
  !dfg insts flips removes inserts id out fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (id, out, fresh, cmp_id) inserts ==>
    fresh = ao_fresh_var cmp_id "iz"
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `inserts = inserts' \/
   (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: inserts' /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
  >- metis_tac[]
  >> gvs[] >> metis_tac[]
QED

Theorem scan_inserts_cmp_id_comparator:
  !dfg insts flips removes inserts id out_var fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (id, out_var, fresh, cmp_id) inserts ==>
    ?i. MEM i insts /\ i.inst_id = cmp_id /\ is_comparator i.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  metis_tac[listTheory.MEM]
QED

Theorem scan_inserts_cmp_ids_distinct:
  !dfg insts flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ALL_DISTINCT (MAP (\(_, _, _, cmp_id). cmp_id) inserts)
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `inserts = inserts' \/
   (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: inserts' /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
  >- metis_tac[]
  >> `ALL_DISTINCT (MAP (\(_, _, _, cmp_id). cmp_id) inserts')` by
       metis_tac[] >>
  simp[] >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >>
  rename1 `MEM (p1, p2, p3, h.inst_id) inserts'` >>
  drule_all scan_inserts_cmp_id_mem >>
  strip_tac >>
  gvs[listTheory.MEM_MAP] >>
  metis_tac[]
QED

Triviality alookup_mem_4th[local]:
  !(l:(num # string # string # num) list) k a b c.
    ALOOKUP l k = SOME (a, b, c) ==>
    MEM c (MAP (\(_, _, _, x). x) l)
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem alookup_cmp_id_inj:
  !(inserts:(num # string # string # num) list) id1 id2 a1 b1 a2 b2 cmp_id.
    ALL_DISTINCT (MAP (\(_, _, _, c). c) inserts) /\
    ALOOKUP inserts id1 = SOME (a1, b1, cmp_id) /\
    ALOOKUP inserts id2 = SOME (a2, b2, cmp_id) ==>
    id1 = id2
Proof
  Induct >> simp[] >>
  rpt gen_tac >>
  PairCases_on `h` >>
  simp[] >> strip_tac >>
  Cases_on `id1 = h0` >> Cases_on `id2 = h0` >> gvs[]
  >- (drule_all alookup_mem_4th >> simp[])
  >- (drule_all alookup_mem_4th >> simp[])
  >> first_x_assum irule >> metis_tac[]
QED

Triviality apply_inst_fresh_has_insert[local]:
  !mid flips removes inserts inst x.
    MEM x (ao_cmp_flip_apply_inst mid flips removes inserts inst) /\
    x.inst_id <> inst.inst_id ==>
    ?cmp_out fresh_v cmp_id.
      ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh_v, cmp_id) /\
      x.inst_id = ao_fresh_id mid cmp_id 0
Proof
  rpt strip_tac >>
  gvs[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[]
QED

Triviality fresh_id_not_mem_inst[local]:
  !mid flips removes inserts inst yi h_id x2.
    h_id <> inst.inst_id /\
    ALL_DISTINCT (MAP (\(_, _, _, cmp_id). cmp_id) inserts) /\
    inst.inst_id <= mid /\ h_id <= mid /\
    ALOOKUP inserts h_id = SOME (x0:string, x1:string, x2) /\
    MEM yi (ao_cmp_flip_apply_inst mid flips removes inserts inst) /\
    ao_fresh_id mid x2 0 = yi.inst_id ==>
    F
Proof
  rpt strip_tac >>
  `yi.inst_id = inst.inst_id \/
   ?cmp_id. yi.inst_id = ao_fresh_id mid cmp_id 0`
    by metis_tac[apply_inst_id_cases]
  >- (`ao_fresh_id mid x2 0 > mid` by simp[ao_fresh_id_gt] >> decide_tac)
  >> `cmp_id = x2` by metis_tac[ao_fresh_id_inj] >>
  `ao_fresh_id mid x2 0 > mid` by simp[ao_fresh_id_gt] >>
  `yi.inst_id > mid` by metis_tac[] >>
  `yi.inst_id <> inst.inst_id` by decide_tac >>
  `?cmp_out fresh_v cmp_id'.
     ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh_v, cmp_id') /\
     yi.inst_id = ao_fresh_id mid cmp_id' 0`
    by metis_tac[apply_inst_fresh_has_insert] >>
  `cmp_id' = x2` by metis_tac[ao_fresh_id_inj] >>
  `ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh_v, x2)` by
    metis_tac[] >>
  mp_tac (Q.SPECL [`inserts`, `h_id`, `inst.inst_id`,
                    `x0`, `x1`, `cmp_out`, `fresh_v`, `x2`]
          alookup_cmp_id_inj) >>
  simp[]
QED

Triviality fresh_id_not_mem_flat[local]:
  !mid flips removes inserts insts h_id x2.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!inst. MEM inst insts ==> inst.inst_id <= mid) /\
    ALL_DISTINCT (MAP (\(_, _, _, cmp_id). cmp_id) inserts) /\
    h_id <= mid /\
    (!ii:instruction. h_id = ii.inst_id ==> ~MEM ii insts) /\
    ALOOKUP inserts h_id = SOME (x0:string, x1:string, x2) ==>
    ~MEM (ao_fresh_id mid x2 0)
      (FILTER (\id. ~(id <= mid))
        (FLAT (MAP (\i. MAP (\x. x.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts i)) insts)))
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_FILTER, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  `?yi. MEM yi (ao_cmp_flip_apply_inst mid flips removes inserts i) /\
        ao_fresh_id mid x2 0 = yi.inst_id` by
    metis_tac[listTheory.MEM_MAP] >>
  `h_id <> i.inst_id` by
    (CCONTR_TAC >> gvs[] >> metis_tac[]) >>
  `i.inst_id <= mid` by metis_tac[] >>
  mp_tac (Q.SPECL [`mid`, `flips`, `removes`, `inserts`, `i`, `yi`,
                    `h_id`, `x2`] fresh_id_not_mem_inst) >>
  simp[]
QED

Triviality filter_gt_flat_map_distinct[local]:
  !mid flips removes inserts insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!inst. MEM inst insts ==> inst.inst_id <= mid) /\
    ALL_DISTINCT (MAP (\(_, _, _, cmp_id). cmp_id) inserts) ==>
    ALL_DISTINCT
      (FILTER (\id. ~(id <= mid))
        (FLAT (MAP (\i. MAP (\x. x.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts i)) insts)))
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[listTheory.FILTER_APPEND_DISTRIB] >>
  `h.inst_id <= mid` by metis_tac[] >>
  Cases_on `ALOOKUP flips h.inst_id`
  >- (Cases_on `MEM h.inst_id removes`
      >- (`FILTER (\id. ~(id <= mid))
             (MAP (\x. x.inst_id)
               (ao_cmp_flip_apply_inst mid flips removes inserts h)) = []`
            by simp[ao_cmp_flip_apply_inst_def] >>
          simp[] >> first_x_assum irule >> simp[] >> metis_tac[])
      >> Cases_on `ALOOKUP inserts h.inst_id`
      >- (`FILTER (\id. ~(id <= mid))
             (MAP (\x. x.inst_id)
               (ao_cmp_flip_apply_inst mid flips removes inserts h)) = []`
            by simp[ao_cmp_flip_apply_inst_def] >>
          simp[] >> first_x_assum irule >> simp[] >> metis_tac[])
      >> PairCases_on `x` >>
         `FILTER (\id. ~(id <= mid))
            (MAP (\x'. x'.inst_id)
              (ao_cmp_flip_apply_inst mid flips removes inserts h)) =
          [ao_fresh_id mid x2 0]` by
           simp[ao_cmp_flip_apply_inst_def, ao_fresh_id_def] >>
         pop_assum (fn th => REWRITE_TAC [th]) >>
         simp[] >>
         irule fresh_id_not_mem_flat >>
         simp[] >>
         qexists_tac `h.inst_id` >> simp[] >>
         rpt strip_tac >> gvs[listTheory.MEM_MAP] >> metis_tac[])
  >> PairCases_on `x` >>
     `FILTER (\id. ~(id <= mid))
        (MAP (\x'. x'.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts h)) = []`
        by simp[ao_cmp_flip_apply_inst_def] >>
     simp[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Triviality filter_le_ids_eq_original[local]:
  !mid flips removes inserts insts.
    (!inst. MEM inst insts ==> inst.inst_id <= mid) ==>
    FLAT (MAP (\x. FILTER (\id. id <= mid)
        (MAP (\i. i.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts x))) insts) =
    MAP (\i. i.inst_id) insts
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `h.inst_id <= mid` by metis_tac[] >>
  `FLAT (MAP (\x. FILTER (\id. id <= mid)
      (MAP (\i. i.inst_id)
        (ao_cmp_flip_apply_inst mid flips removes inserts x))) insts) =
   MAP (\i. i.inst_id) insts` by
    (first_x_assum match_mp_tac >> metis_tac[]) >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[ao_fresh_id_def]
QED

Triviality fn_inst_ids_flat_map[local]:
  !bbs ap.
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (MAP (\bb. bb with bb_instructions :=
        FLAT (MAP ap bb.bb_instructions)) bbs)) =
    FLAT (MAP (\inst. MAP (\i. i.inst_id) (ap inst))
      (fn_insts_blocks bbs))
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >>
  simp[listTheory.MAP_FLAT, listTheory.MAP_MAP_o,
       combinTheory.o_DEF] >>
  simp[listTheory.FLAT_APPEND, rich_listTheory.FLAT_FLAT]
QED

Theorem ao_phase4_preserves_wf:
  !mid dfg fn.
    wf_function fn /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i (fn_insts fn)) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid) ==>
    wf_function (ao_cmp_flip_function mid dfg fn)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_function_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
     ~is_terminator opc` by metis_tac[ao_cmp_flip_scan_flips_non_term] >>
  `!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
     opc <> PHI` by metis_tac[ao_cmp_flip_scan_flips_non_phi] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (irule fn_inst_ids_to_fn_insts >>
     fs[wf_function_def]) >>
  fs[wf_function_def] >>
  ONCE_REWRITE_TAC [wf_function_def] >>
  fs[fn_labels_def, fn_has_entry_def] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  rpt conj_tac
  (* bb_well_formed *)
  >- (rpt strip_tac >>
      gvs[listTheory.MEM_MAP] >>
      rename1 `MEM bb0 fn.fn_blocks` >>
      irule phase4_bb_wf_preserved >>
      simp[] >>
      conj_tac >- (rpt strip_tac >> res_tac >> gvs[]) >>
      qexistsl_tac [`fn_insts fn`, `dfg`] >>
      simp[] >>
      conj_tac
      >- (rpt strip_tac >>
          simp[fn_insts_def] >> irule fn_insts_blocks_mem >>
          qexists_tac `bb0` >> simp[])
      >- metis_tac[])
  (* fn_succs_closed *)
  >- (simp[fn_succs_closed_def, fn_labels_def,
           listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
      rpt strip_tac >>
      gvs[listTheory.MEM_MAP] >>
      rename1 `MEM bb0 fn.fn_blocks` >>
      `bb_succs (bb0 with bb_instructions :=
         FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                   bb0.bb_instructions)) = bb_succs bb0` by
        (irule phase4_bb_succs >>
         simp[] >>
         qexistsl_tac [`fn_insts fn`, `dfg`] >>
         simp[] >>
         conj_tac
         >- (rpt strip_tac >>
             simp[fn_insts_def] >> irule fn_insts_blocks_mem >>
             qexists_tac `bb0` >> simp[])
         >- metis_tac[]) >>
      gvs[] >>
      fs[fn_succs_closed_def, fn_labels_def, listTheory.MEM_MAP] >>
      res_tac >> metis_tac[])
  (* fn_inst_ids_distinct *)
  >> simp[fn_inst_ids_distinct_def, fn_inst_ids_flat_map, fn_insts_def] >>
     `ALL_DISTINCT (FILTER (\id. ~(id <= mid))
        (FLAT (MAP (\i. MAP (\x. x.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts i))
          (fn_insts_blocks fn.fn_blocks))))` by
       (fs[fn_insts_def] >>
        irule filter_gt_flat_map_distinct >>
        simp[] >>
        rpt conj_tac >>
        TRY (metis_tac[]) >>
        irule scan_inserts_cmp_ids_distinct >>
        metis_tac[]) >>
     `ALL_DISTINCT (FILTER (\id. id <= mid)
        (FLAT (MAP (\i. MAP (\x. x.inst_id)
          (ao_cmp_flip_apply_inst mid flips removes inserts i))
          (fn_insts_blocks fn.fn_blocks))))` by
       (simp[rich_listTheory.FILTER_FLAT, listTheory.MAP_MAP_o,
             combinTheory.o_DEF] >>
        `FLAT (MAP (\x. FILTER (\id. id <= mid)
            (MAP (\i. i.inst_id)
              (ao_cmp_flip_apply_inst mid flips removes inserts x)))
            (fn_insts_blocks fn.fn_blocks)) =
         MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)` by
          (irule filter_le_ids_eq_original >>
           simp[fn_insts_def] >> metis_tac[]) >>
        simp[] >>
        fs[fn_inst_ids_distinct_def, fn_insts_def]) >>
     irule all_distinct_pred_split_local >>
     qexists_tac `mid` >> simp[]
QED

val _ = export_theory();
