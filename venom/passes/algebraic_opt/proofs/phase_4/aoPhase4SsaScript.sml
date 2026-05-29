(* Phase 4 SSA preservation: ao_cmp_flip_function preserves ssa_form.
 *
 * TOP-LEVEL:
 *   ao_phase4_preserves_ssa — ssa_form preserved through phase 4
 *)

Theory aoPhase4Ssa
Ancestors
  algebraicOptDefs aoPhase4Wf venomWf venomInst alist
Libs
  pairLib BasicProvers

(* ===== Phase 4 SSA preservation ===== *)

Triviality ao_fresh_var_iz_inj[local]:
  !id1 id2. ao_fresh_var id1 "iz" = ao_fresh_var id2 "iz" ==> id1 = id2
Proof
  simp[ao_fresh_var_def, stringTheory.STRCAT_11,
       ASCIInumbersTheory.toString_inj]
QED

(* Inserted fresh output vars from the scan are always ao_fresh_var c "iz". *)
Triviality scan_inserts_fresh_form[local]:
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

(* Generic ALL_DISTINCT split on a set-membership predicate. *)
Triviality all_distinct_mem_split[local]:
  !(fv:string set) l.
    ALL_DISTINCT (FILTER (\v. v IN fv) l) /\
    ALL_DISTINCT (FILTER (\v. ~(v IN fv)) l) ==>
    ALL_DISTINCT l
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h IN fv` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >> metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

(* fn_insts of a per-block FLAT-MAP transform = FLAT-MAP over fn_insts. *)
Triviality fn_insts_blocks_map_flat[local]:
  !bbs ap.
    fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        FLAT (MAP ap bb.bb_instructions)) bbs) =
    FLAT (MAP ap (fn_insts_blocks bbs))
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.FLAT_APPEND]
QED

Triviality flat_map_outputs_flat_map[local]:
  !insts ap.
    FLAT (MAP (\i. i.inst_outputs) (FLAT (MAP ap insts))) =
    FLAT (MAP (\i. FLAT (MAP (\x. x.inst_outputs) (ap i))) insts)
Proof
  Induct >> simp[listTheory.FLAT_APPEND]
QED

(* Per-instruction: the non-fresh outputs are exactly the original outputs. *)
Triviality apply_outputs_nonfresh_eq[local]:
  !mid flips removes inserts inst fv.
    (!v. MEM v inst.inst_outputs ==> v NOTIN fv) /\
    (!co f c. ALOOKUP inserts inst.inst_id = SOME (co, f, c) ==> f IN fv) ==>
    FILTER (\v. ~(v IN fv))
      (FLAT (MAP (\x. x.inst_outputs)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst))) =
    inst.inst_outputs
Proof
  rpt strip_tac >>
  `FILTER (\v. ~(v IN fv)) inst.inst_outputs = inst.inst_outputs` by
    (simp[listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (Cases_on `MEM inst.inst_id removes`
      >- gvs[]
      >> Cases_on `ALOOKUP inserts inst.inst_id`
         >- gvs[]
         >> PairCases_on `x` >>
            `x1 IN fv` by metis_tac[] >>
            gvs[listTheory.FILTER])
  >> PairCases_on `x` >> gvs[]
QED

(* Per-instruction: the fresh outputs are the inserted fresh var (or none). *)
Triviality apply_outputs_fresh_eq[local]:
  !mid flips removes inserts inst fv.
    (!v. MEM v inst.inst_outputs ==> v NOTIN fv) /\
    (!co f c. ALOOKUP inserts inst.inst_id = SOME (co, f, c) ==> f IN fv) ==>
    FILTER (\v. v IN fv)
      (FLAT (MAP (\x. x.inst_outputs)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst))) =
    (if ALOOKUP flips inst.inst_id = NONE /\ ~MEM inst.inst_id removes then
       case ALOOKUP inserts inst.inst_id of
         NONE => []
       | SOME (co, f, c) => [f]
     else [])
Proof
  rpt strip_tac >>
  `FILTER (\v. v IN fv) inst.inst_outputs = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (Cases_on `MEM inst.inst_id removes`
      >- gvs[]
      >> Cases_on `ALOOKUP inserts inst.inst_id`
         >- gvs[]
         >> PairCases_on `x` >>
            `x1 IN fv` by metis_tac[] >>
            gvs[listTheory.FILTER])
  >> PairCases_on `x` >> gvs[]
QED

(* Non-fresh part of the whole transformed output list = original outputs. *)
Triviality filter_nonfresh_outputs_eq[local]:
  !mid flips removes inserts insts fv.
    (!inst v. MEM inst insts /\ MEM v inst.inst_outputs ==> v NOTIN fv) /\
    (!id co f c. ALOOKUP inserts id = SOME (co, f, c) ==> f IN fv) ==>
    FILTER (\v. ~(v IN fv))
      (FLAT (MAP (\i. FLAT (MAP (\x. x.inst_outputs)
        (ao_cmp_flip_apply_inst mid flips removes inserts i))) insts)) =
    FLAT (MAP (\i. i.inst_outputs) insts)
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[listTheory.FILTER_APPEND_DISTRIB] >>
  `FILTER (\v. ~(v IN fv)) (FLAT (MAP (\x. x.inst_outputs)
     (ao_cmp_flip_apply_inst mid flips removes inserts h))) = h.inst_outputs` by
    (irule apply_outputs_nonfresh_eq >> simp[] >> metis_tac[]) >>
  simp[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* A fresh output of one transformed instruction comes from an insert. *)
Triviality fresh_filter_mem[local]:
  !mid flips removes inserts inst fv v.
    (!w. MEM w inst.inst_outputs ==> w NOTIN fv) /\
    MEM v (FILTER (\u. u IN fv)
      (FLAT (MAP (\x. x.inst_outputs)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst)))) ==>
    ?co c. ALOOKUP inserts inst.inst_id = SOME (co, v, c)
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_FILTER] >>
  qpat_x_assum `MEM v (FLAT _)` mp_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP flips inst.inst_id` >> simp[]
  >- (Cases_on `MEM inst.inst_id removes` >> simp[]
      >- (strip_tac >> metis_tac[])
      >> Cases_on `ALOOKUP inserts inst.inst_id` >> simp[]
         >- (strip_tac >> metis_tac[])
         >> PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >> metis_tac[])
  >> PairCases_on `x` >> simp[] >> strip_tac >> metis_tac[]
QED

(* Any fresh var among the flattened transformed outputs comes from an insert. *)
Triviality fresh_mem_flat_insert[local]:
  !insts mid flips removes inserts fv f.
    (!i v. MEM i insts /\ MEM v i.inst_outputs ==> v NOTIN fv) /\
    MEM f (FILTER (\v. v IN fv)
       (FLAT (MAP (\i. FLAT (MAP (\x. x.inst_outputs)
         (ao_cmp_flip_apply_inst mid flips removes inserts i))) insts))) ==>
    ?inst co c. MEM inst insts /\
      ALOOKUP inserts inst.inst_id = SOME (co, f, c)
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.MEM_APPEND]
  >- (`!w. MEM w h.inst_outputs ==> w NOTIN fv` by metis_tac[] >>
      drule_all fresh_filter_mem >> strip_tac >>
      qexistsl_tac [`h`, `co`, `c`] >> simp[]) >>
  first_x_assum (qspecl_then [`mid`, `flips`, `removes`, `inserts`, `fv`, `f`]
    mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  qexistsl_tac [`inst`, `co`, `c`] >> simp[]
QED

(* The fresh part of the whole transformed output list is ALL_DISTINCT. *)
Triviality filter_fresh_outputs_distinct[local]:
  !mid flips removes inserts insts fv.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    ALL_DISTINCT (MAP (\(_, _, _, c). c) inserts) /\
    (!i v. MEM i insts /\ MEM v i.inst_outputs ==> v NOTIN fv) /\
    (!id co f c. ALOOKUP inserts id = SOME (co, f, c) ==>
       f IN fv /\ f = ao_fresh_var c "iz") ==>
    ALL_DISTINCT (FILTER (\v. v IN fv)
      (FLAT (MAP (\i. FLAT (MAP (\x. x.inst_outputs)
        (ao_cmp_flip_apply_inst mid flips removes inserts i))) insts)))
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `FILTER (\v. v IN fv) (FLAT (MAP (\x. x.inst_outputs)
     (ao_cmp_flip_apply_inst mid flips removes inserts h))) =
   (if ALOOKUP flips h.inst_id = NONE /\ ~MEM h.inst_id removes then
      case ALOOKUP inserts h.inst_id of
        NONE => [] | SOME (co, f, c) => [f]
    else [])` by
    (irule apply_outputs_fresh_eq >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (FILTER (\v. v IN fv) (FLAT (MAP (\i. FLAT (MAP
     (\x. x.inst_outputs)
       (ao_cmp_flip_apply_inst mid flips removes inserts i))) insts)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  reverse (Cases_on `ALOOKUP flips h.inst_id = NONE /\ ~MEM h.inst_id removes`)
  >- gvs[listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND]
  >> Cases_on `ALOOKUP inserts h.inst_id`
  >- gvs[listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND]
  >> PairCases_on `x` >>
     gvs[listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND] >>
     strip_tac >>
     `!i v. MEM i insts /\ MEM v i.inst_outputs ==> v NOTIN fv` by
       metis_tac[listTheory.MEM] >>
     drule_all fresh_mem_flat_insert >> strip_tac >>
     rename1 `ALOOKUP inserts inst2.inst_id = SOME (co2, x1, c2)` >>
     `x1 = ao_fresh_var c2 "iz"` by metis_tac[] >>
     `x1 = ao_fresh_var x2 "iz"` by metis_tac[] >>
     `c2 = x2` by metis_tac[ao_fresh_var_iz_inj] >>
     `inst2.inst_id = h.inst_id` by metis_tac[alookup_cmp_id_inj] >>
     fs[listTheory.MEM_MAP] >> metis_tac[]
QED

(* Phase 4 preserves SSA. The freshness side-condition is the minimal honest
 * requirement: the original outputs must avoid the specific fresh "iz" vars
 * that the comparator-flip scan inserts (disjoint from the inserts image).
 * This is satisfiable downstream of phase 3, unlike the broader
 * ao_fn_fresh_vars namespace, since it concerns only the vars phase 4 adds. *)
Theorem ao_phase4_preserves_ssa:
  !mid dfg fn.
    ssa_form fn /\
    fn_inst_ids_distinct fn /\
    (!flips removes inserts.
       ao_cmp_flip_scan dfg (fn_insts fn) = (flips, removes, inserts) ==>
       !aid out f c inst v.
         MEM (aid, out, f, c) inserts /\
         MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==> v <> f) ==>
    ssa_form (ao_cmp_flip_function mid dfg fn)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_function_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >> TRY (gvs[ssa_form_def] >> NO_TAC) >>
     qabbrev_tac `fv = {f | ?aid out c. MEM (aid, out, f, c) inserts}` >>
     `!aid out f c inst v.
        MEM (aid, out, f, c) inserts /\
        MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==> v <> f` by
       metis_tac[] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
       metis_tac[fn_inst_ids_to_fn_insts] >>
     `ALL_DISTINCT (MAP (\(_, _, _, c). c) inserts)` by
       (drule_all scan_inserts_cmp_ids_distinct >> simp[]) >>
     `!id co f c. ALOOKUP inserts id = SOME (co, f, c) ==>
        f IN fv /\ f = ao_fresh_var c "iz"` by
       (rpt gen_tac >> strip_tac >>
        `MEM (id, co, f, c) inserts` by metis_tac[alistTheory.ALOOKUP_MEM] >>
        `f = ao_fresh_var c "iz"` by metis_tac[scan_inserts_fresh_form] >>
        simp[Abbr `fv`] >> metis_tac[]) >>
     `!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
        v NOTIN fv` by
       (rpt strip_tac >> fs[Abbr `fv`] >> metis_tac[]) >>
     simp[ssa_form_def, fn_insts_def, fn_insts_blocks_map_flat] >>
     simp[GSYM fn_insts_def, flat_map_outputs_flat_map] >>
     irule all_distinct_mem_split >>
     qexists_tac `fv` >>
     conj_tac
     >- (`FILTER (\v. ~(v IN fv))
            (FLAT (MAP (\i. FLAT (MAP (\x. x.inst_outputs)
              (ao_cmp_flip_apply_inst mid flips removes inserts i)))
              (fn_insts fn))) =
          FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))` by
           (irule filter_nonfresh_outputs_eq >> simp[] >> metis_tac[]) >>
         fs[ssa_form_def, fn_insts_def])
     >> irule filter_fresh_outputs_distinct >> rpt conj_tac >> metis_tac[]
QED


val _ = export_theory();
