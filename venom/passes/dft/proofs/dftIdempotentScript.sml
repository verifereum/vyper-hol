(*
 * DFT Idempotent — Input-Order-Independence of dft_block
 *
 * Key result: dft_block order (dft_block order' bb) = dft_block order bb
 *
 * This means applying dft_block to an already-dft'd block gives the same
 * result as applying it to the original. The second dft_block "sees through"
 * the first transformation.
 *
 * Proof strategy: Show that the schedule pipeline only depends on:
 *   (1) The set of non-pseudo inst_ids (with their opcodes and outputs)
 *   (2) The phi instructions (same in both cases)
 *   (3) The order parameter (same in both cases)
 * NOT on the order of non-pseudo instructions in bb.bb_instructions.
 *
 * Key sub-lemmas:
 *   - producing_inst is order-independent under unique defs
 *   - build_eda is order-independent when same-effect-type pairs
 *     maintain relative order (which dft_block guarantees)
 *   - DFS is deterministic given same deps and order
 *)

Theory dftIdempotent
Ancestors
  dftStructural dftDefs venomExecSemantics venomEffects passSharedDefs
  venomInst list rich_list sorting finite_map

(* ===== producing_inst order-independence ===== *)

(* producing_inst returns the FIRST instruction with var in outputs.
   Under unique defs (at most one inst defines each var), the result
   is the same regardless of list order. *)

Definition unique_defs_def:
  unique_defs insts <=>
    !i j. i < j /\ j < LENGTH insts ==>
      DISJOINT (set (EL i insts).inst_outputs) (set (EL j insts).inst_outputs)
End

(* producing_inst returns an instruction that is in the list
   and has var in its outputs. *)
Theorem producing_inst_unique:
  !insts var inst.
    producing_inst insts var = SOME inst ==>
    MEM inst insts /\ MEM var inst.inst_outputs
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem producing_inst_mem_outputs:
  !insts var inst.
    producing_inst insts var = SOME inst ==>
    MEM var inst.inst_outputs
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

(* For an instruction at the head that does NOT define var,
   producing_inst skips it *)
Triviality producing_inst_skip:
  !h rest var.
    ~MEM var h.inst_outputs ==>
    producing_inst (h :: rest) var = producing_inst rest var
Proof
  rw[producing_inst_def]
QED

(* For an instruction at the head that DOES define var,
   producing_inst returns it *)
Triviality producing_inst_hit:
  !h rest var.
    MEM var h.inst_outputs ==>
    producing_inst (h :: rest) var = SOME h
Proof
  rw[producing_inst_def]
QED

(* Key: if there is a unique definer in the list, producing_inst finds it
   regardless of position *)
Theorem producing_inst_unique_definer:
  !insts var inst.
    MEM inst insts /\ MEM var inst.inst_outputs /\
    (!j. MEM j insts /\ j <> inst ==> ~MEM var j.inst_outputs) ==>
    producing_inst insts var = SOME inst
Proof
  Induct >> rw[producing_inst_def] >>
  Cases_on `MEM var h.inst_outputs`
  >- (gvs[] >> metis_tac[])
  >> gvs[] >> metis_tac[]
QED

(* ===== flip_operands preserves key properties ===== *)

(* flip_operands preserves inst_opcode for non-comparators *)
Triviality flip_operands_opcode_non_comp:
  !i. ~is_comparator i.inst_opcode ==>
      (flip_operands i).inst_opcode = i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM]
QED

(* flip_operands preserves write_effects and read_effects *)
Triviality flip_operands_write_effects:
  !i. write_effects (flip_operands i).inst_opcode = write_effects i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, write_effects_def]
QED

Triviality flip_operands_read_effects:
  !i. read_effects (flip_operands i).inst_opcode = read_effects i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, read_effects_def]
QED

Triviality flip_operands_is_terminator:
  !i. is_terminator (flip_operands i).inst_opcode = is_terminator i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, is_terminator_def]
QED

(* flip_operands_involution is now in dftStructuralTheory *)

(* ===== dft_block structural decomposition ===== *)

(* The non-pseudos of dft_block output are exactly the scheduled part *)
Triviality dft_block_instructions:
  !order bb.
    (dft_block order bb).bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
    schedule_from_entries bb.bb_instructions order
      (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order
        (build_full_eda bb.bb_instructions))
Proof
  rw[dft_block_def, LET_THM]
QED

(* Non-pseudos of dft_block output = the scheduled part *)
Triviality dft_block_non_pseudos:
  !order bb.
    FILTER (\i. ~is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions =
    schedule_from_entries bb.bb_instructions order
      (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order
        (build_full_eda bb.bb_instructions))
Proof
  rw[dft_block_instructions, rich_listTheory.FILTER_APPEND] >>
  simp[rich_listTheory.FILTER_FILTER] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode)
    (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]) >>
  simp[] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode)
    (schedule_from_entries bb.bb_instructions order
      (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order
        (build_full_eda bb.bb_instructions))) =
   schedule_from_entries bb.bb_instructions order
      (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order
        (build_full_eda bb.bb_instructions))` suffices_by simp[] >>
  simp[FILTER_EQ_ID, EVERY_MEM] >>
  rpt strip_tac >>
  metis_tac[schedule_output_from_block, build_full_eda_wf, entry_instructions_mem]
QED

(* ===== Effect-equivalent instructions ===== *)

(* Two instructions are "effect-equivalent" if they have the same inst_id,
   and the same write/read effects. This is the relevant equivalence for
   build_eda — it processes instructions only through these fields. *)
Definition eff_equiv_def:
  eff_equiv i1 i2 <=>
    i1.inst_id = i2.inst_id /\
    write_effects i1.inst_opcode = write_effects i2.inst_opcode /\
    read_effects i1.inst_opcode = read_effects i2.inst_opcode
End

(* flip_operands produces effect-equivalent instructions *)
Theorem flip_operands_eff_equiv:
  !i. eff_equiv i (flip_operands i) /\ eff_equiv (flip_operands i) i
Proof
  rw[eff_equiv_def, flip_operands_write_effects, flip_operands_read_effects] >>
  metis_tac[flip_operands_inst_id]
QED

(* from_block instructions are effect-equivalent to originals *)
Theorem from_block_eff_equiv:
  !block_insts i.
    from_block block_insts i ==>
    ?j. MEM j block_insts /\ ~is_pseudo j.inst_opcode /\ eff_equiv i j
Proof
  rw[from_block_def, eff_equiv_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[]
  >> qexists_tac `j` >> simp[flip_operands_write_effects, flip_operands_read_effects] >>
  metis_tac[flip_operands_inst_id]
QED

(* ===== Effect tracking equivalence via injection ===== *)

(* et_equiv_via f: tracking state et2 is the image of et1 under injection f.
   This captures structural consistency: same instruction stored in et1 maps
   to same instruction in et2 via f, so nub behaves identically. *)
Definition et_equiv_via_def:
  et_equiv_via f et1 et2 <=>
    (!eff. case (FLOOKUP et1.et_last_write eff, FLOOKUP et2.et_last_write eff) of
      (NONE, NONE) => T
    | (SOME w1, SOME w2) => w2 = f w1
    | (NONE, SOME _) => F  (* et2 has writer but et1 doesn't *)
    | (SOME _, NONE) => F  (* et1 has writer but et2 doesn't *)
    ) /\
    (!eff. case (FLOOKUP et1.et_all_reads eff, FLOOKUP et2.et_all_reads eff) of
      (NONE, NONE) => T
    | (SOME rs1, SOME rs2) => rs2 = MAP f rs1
    | (NONE, SOME _) => F  (* et2 has readers but et1 doesn't *)
    | (SOME _, NONE) => F  (* et1 has readers but et2 doesn't *)
    )
End

(* Identity gives reflexivity *)
Triviality et_equiv_via_id:
  !et. et_equiv_via I et et
Proof
  rw[et_equiv_via_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP et.et_last_write eff` >> simp[] >>
  Cases_on `FLOOKUP et.et_all_reads eff` >> simp[MAP_ID]
QED

(* Empty tracking states are equivalent via any f *)
Triviality et_equiv_via_empty:
  !f. et_equiv_via f empty_effect_track empty_effect_track
Proof
  rw[et_equiv_via_def, empty_effect_track_def, FLOOKUP_DEF, FDOM_FEMPTY]
QED

(* Helper: et_get_reads under et_equiv_via *)
Triviality et_get_reads_via:
  !f et1 et2 eff.
    et_equiv_via f et1 et2 ==>
    et_get_reads et2 eff = MAP f (et_get_reads et1 eff)
Proof
  rw[et_equiv_via_def, et_get_reads_def] >>
  first_x_assum (qspec_then `eff` mp_tac) >>
  Cases_on `FLOOKUP et1.et_all_reads eff` >>
  Cases_on `FLOOKUP et2.et_all_reads eff` >> simp[]
QED

(* Helper: FLOOKUP et_last_write under et_equiv_via *)
Triviality et_last_write_via:
  !f et1 et2 eff.
    et_equiv_via f et1 et2 ==>
    case FLOOKUP et1.et_last_write eff of
      NONE => FLOOKUP et2.et_last_write eff = NONE
    | SOME w => FLOOKUP et2.et_last_write eff = SOME (f w)
Proof
  rw[et_equiv_via_def] >>
  pop_assum kall_tac >>
  first_x_assum (qspec_then `eff` mp_tac) >>
  Cases_on `FLOOKUP et1.et_last_write eff` >>
  Cases_on `FLOOKUP et2.et_last_write eff` >> simp[]
QED

(* Helper: write FOLDL preserves et_equiv_via *)
Triviality write_step_via:
  !f et1 et2 i1 weff.
    et_equiv_via f et1 et2 ==>
    et_equiv_via f
      (et1 with <| et_last_write := et1.et_last_write |+ (weff, i1);
                    et_all_reads := et1.et_all_reads |+ (weff, []) |>)
      (et2 with <| et_last_write := et2.et_last_write |+ (weff, f i1);
                    et_all_reads := et2.et_all_reads |+ (weff, []) |>)
Proof
  rw[et_equiv_via_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `eff` mp_tac) >>
  Cases_on `eff = weff` >> simp[FLOOKUP_UPDATE]
QED

Triviality write_foldl_via:
  !f effs et1 et2 i1.
    et_equiv_via f et1 et2 ==>
    et_equiv_via f
      (FOLDL (\acc weff.
        acc with <| et_last_write := acc.et_last_write |+ (weff, i1);
                    et_all_reads := acc.et_all_reads |+ (weff, []) |>) et1 effs)
      (FOLDL (\acc weff.
        acc with <| et_last_write := acc.et_last_write |+ (weff, f i1);
                    et_all_reads := acc.et_all_reads |+ (weff, []) |>) et2 effs)
Proof
  Induct_on `effs`
  >- simp[]
  >> rpt strip_tac >>
  ONCE_REWRITE_TAC[FOLDL] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  first_x_assum irule >> irule write_step_via >> simp[]
QED

(* Helper: single read step preserves et_equiv_via *)
Triviality read_step_via:
  !f et1 et2 i1 reff.
    et_equiv_via f et1 et2 ==>
    et_equiv_via f
      (et1 with et_all_reads :=
        et1.et_all_reads |+ (reff, et_get_reads et1 reff ++ [i1]))
      (et2 with et_all_reads :=
        et2.et_all_reads |+ (reff, et_get_reads et2 reff ++ [f i1]))
Proof
  rpt strip_tac >>
  `et_get_reads et2 reff = MAP f (et_get_reads et1 reff)` by
    metis_tac[et_get_reads_via] >>
  fs[et_equiv_via_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `eff` mp_tac) >>
  Cases_on `eff = reff` >> simp[FLOOKUP_UPDATE, MAP_APPEND]
QED

(* Helper: read FOLDL preserves et_equiv_via *)
Triviality read_foldl_via:
  !f effs et1 et2 i1.
    et_equiv_via f et1 et2 ==>
    et_equiv_via f
      (FOLDL (\acc reff.
        acc with et_all_reads :=
          acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [i1])) et1 effs)
      (FOLDL (\acc reff.
        acc with et_all_reads :=
          acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [f i1])) et2 effs)
Proof
  Induct_on `effs`
  >- simp[]
  >> rpt strip_tac >>
  ONCE_REWRITE_TAC[FOLDL] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  first_x_assum irule >> irule read_step_via >> simp[]
QED

(* Helper: MAP THE o FILTER IS_SOME o MAP distributes through OPTION_MAP *)
Triviality filter_some_map_option:
  !f g1 g2 ls.
    (!x. MEM x ls ==> g2 x = OPTION_MAP f (g1 x)) ==>
    MAP THE (FILTER IS_SOME (MAP g2 ls)) =
    MAP f (MAP THE (FILTER IS_SOME (MAP g1 ls)))
Proof
  ntac 3 gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  `g2 h = OPTION_MAP f (g1 h)` by simp[] >>
  Cases_on `g1 h` >> gvs[]
QED

(* Helper: FLAT distributes through pointwise MAP f *)
Triviality flat_map_map_f:
  !f g1 g2 ls.
    (!x. MEM x ls ==> g2 x = MAP f (g1 x)) ==>
    FLAT (MAP g2 ls) = MAP f (FLAT (MAP g1 ls))
Proof
  ntac 3 gen_tac >> Induct >> simp[MAP_APPEND]
QED

(* Helper: the raw dep list (before nub) maps through f *)
Triviality raw_deps_map_f:
  !f et1 et2 i1.
    (!eff. et_get_reads et2 eff = MAP f (et_get_reads et1 eff)) /\
    (!eff. case FLOOKUP et1.et_last_write eff of
        NONE => FLOOKUP et2.et_last_write eff = NONE
      | SOME w => FLOOKUP et2.et_last_write eff = SOME (f w)) /\
    (!i. (f i).inst_id = i.inst_id) ==>
    FLAT (MAP (\weff. et_get_reads et2 weff ++
        case FLOOKUP et2.et_last_write weff of
               NONE => [] | SOME w => [w])
        (effects_to_list (write_effects i1.inst_opcode))) ++
    MAP THE (FILTER IS_SOME (MAP (\reff.
        case FLOOKUP et2.et_last_write reff of
          NONE => NONE
        | SOME writer =>
            if writer.inst_id <> i1.inst_id then SOME writer else NONE)
        (effects_to_list (read_effects i1.inst_opcode))))
    =
    MAP f (
      FLAT (MAP (\weff. et_get_reads et1 weff ++
          case FLOOKUP et1.et_last_write weff of
                 NONE => [] | SOME w => [w])
          (effects_to_list (write_effects i1.inst_opcode))) ++
      MAP THE (FILTER IS_SOME (MAP (\reff.
          case FLOOKUP et1.et_last_write reff of
            NONE => NONE
          | SOME writer =>
              if writer.inst_id <> i1.inst_id then SOME writer else NONE)
          (effects_to_list (read_effects i1.inst_opcode)))))
Proof
  rpt strip_tac >>
  REWRITE_TAC[MAP_APPEND] >>
  (* Write part: use flat_map_map_f *)
  sg `FLAT (MAP (\weff. et_get_reads et2 weff ++
      case FLOOKUP et2.et_last_write weff of
             NONE => [] | SOME w => [w])
      (effects_to_list (write_effects i1.inst_opcode))) =
    MAP f (FLAT (MAP (\weff. et_get_reads et1 weff ++
      case FLOOKUP et1.et_last_write weff of
             NONE => [] | SOME w => [w])
      (effects_to_list (write_effects i1.inst_opcode))))`
  >- (
    irule flat_map_map_f >> rpt strip_tac >> rename1 `MEM weff _` >>
    simp[MAP_APPEND] >>
    first_x_assum (qspec_then `weff` mp_tac) >>
    Cases_on `FLOOKUP et1.et_last_write weff` >> simp[]
  ) >>
  (* Read part: use filter_some_map_option *)
  sg `MAP THE (FILTER IS_SOME (MAP (\reff.
      case FLOOKUP et2.et_last_write reff of
        NONE => NONE
      | SOME writer =>
          if writer.inst_id <> i1.inst_id then SOME writer else NONE)
      (effects_to_list (read_effects i1.inst_opcode)))) =
    MAP f (MAP THE (FILTER IS_SOME (MAP (\reff.
      case FLOOKUP et1.et_last_write reff of
        NONE => NONE
      | SOME writer =>
          if writer.inst_id <> i1.inst_id then SOME writer else NONE)
      (effects_to_list (read_effects i1.inst_opcode)))))`
  >- (
    irule filter_some_map_option >> rpt strip_tac >> rename1 `MEM reff _` >>
    first_x_assum (qspec_then `reff` mp_tac) >>
    Cases_on `FLOOKUP et1.et_last_write reff` >> simp[] >>
    strip_tac >> gvs[] >>
    Cases_on `x.inst_id <> i1.inst_id` >> simp[]
  ) >>
  simp[]
QED

(* Main lemma: compute_effect_deps maps deps through f.
   When f is globally injective and preserves inst_id/effects,
   deps2 = MAP f deps1 and et_equiv_via is preserved. *)
Theorem compute_effect_deps_via:
  !f et1 et2 i1 deps1 et1' deps2 et2'.
    et_equiv_via f et1 et2 /\
    INJ f UNIV UNIV /\
    (!i. (f i).inst_id = i.inst_id) /\
    (!i. write_effects (f i).inst_opcode = write_effects i.inst_opcode) /\
    (!i. read_effects (f i).inst_opcode = read_effects i.inst_opcode) /\
    compute_effect_deps et1 i1 = (deps1, et1') /\
    compute_effect_deps et2 (f i1) = (deps2, et2') ==>
    et_equiv_via f et1' et2' /\
    deps2 = MAP f deps1
Proof
  rpt strip_tac >>
  fs[compute_effect_deps_def, LET_THM] >>
  ntac 4 (pop_assum (SUBST_ALL_TAC o SYM)) >> fs[]
  >- (
    irule read_foldl_via >>
    irule (SIMP_RULE (srw_ss()) [] write_foldl_via) >> simp[]
  )
  >>
  (* Establish key hypotheses *)
  `!eff. et_get_reads et2 eff = MAP f (et_get_reads et1 eff)` by
    metis_tac[et_get_reads_via]
  >>
  `!eff. case FLOOKUP et1.et_last_write eff of
      NONE => FLOOKUP et2.et_last_write eff = NONE
    | SOME w => FLOOKUP et2.et_last_write eff = SOME (f w)` by
    metis_tac[et_last_write_via]
  >>
  (* Use raw_deps_map_f to rewrite inner_et2 = MAP f inner_et1 *)
  imp_res_tac raw_deps_map_f >>
  pop_assum (qspec_then `i1` (fn th => REWRITE_TAC[th])) >>
  (* Now: nub(MAP f inner) = MAP f (nub inner) via nub_MAP_INJ *)
  irule nub_MAP_INJ >>
  first_assum (irule o MATCH_MP (DB.fetch "pred_set" "INJ_SUBSET_UNIV"))
QED

(* ===== Main Idempotency Result ===== *)

(* Key structural lemma: dft_block expands into phis ++ schedule,
   and the schedule only depends on bb.bb_instructions.
   Two blocks with the same bb_instructions and bb_label produce
   the same dft_block output. *)
Triviality dft_block_only_depends_on_insts:
  !order bb1 bb2.
    bb1.bb_instructions = bb2.bb_instructions /\
    bb1.bb_label = bb2.bb_label ==>
    dft_block order bb1 = dft_block order bb2
Proof
  rw[dft_block_def, LET_THM] >>
  simp[basic_block_component_equality]
QED

(* Counterexample: dft_block_idempotent is FALSE without unique_defs.
   Two instructions with duplicate outputs get reordered by dft_block,
   and reordering changes producing_inst, breaking the fixed-point property. *)
Theorem dft_block_idempotent_needs_unique_defs:
  ?order bb.
    dft_block order (dft_block order bb) <> dft_block order bb
Proof
  qexistsl_tac [`[]`,
    `<| bb_label := "t";
        bb_instructions :=
          [<| inst_id := 1; inst_opcode := ADD;
              inst_operands := [Lit 0w; Lit 0w]; inst_outputs := ["x"] |>;
           <| inst_id := 2; inst_opcode := ADD;
              inst_operands := [Lit 0w; Lit 0w]; inst_outputs := ["x"] |>;
           <| inst_id := 3; inst_opcode := STOP;
              inst_operands := [Var "x"]; inst_outputs := [] |>] |>`] >>
  EVAL_TAC
QED

(* dft_block_idempotent: proved FALSE by counterexample above.
   build_eda is order-dependent due to "last writer clears readers" mechanism. *)


