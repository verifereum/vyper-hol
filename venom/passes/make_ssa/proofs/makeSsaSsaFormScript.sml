(*
 * Make SSA Pass — SSA Form Proof
 *
 * Cross-block output distinctness and ssa_form for make_ssa_fn.
 * Depends on makeSsaProofTheory for label preservation, counter mono, etc.
 *)

Theory makeSsaSsaForm
Ancestors
  makeSsaProof makeSsaHelper makeSsaDefs dominatorDefs cfgTransform venomInst venomWf
  venomExecProofs cfgTransformProofs cfgTransformProps
  list rich_list alist arithmetic sorting pred_set

(* ==========================================================================
   Part 7: SSA form — every variable defined at most once
   ========================================================================== *)

(* All output variables from a list of instructions *)
Definition all_output_vars_def:
  all_output_vars insts = FLAT (MAP (\i. i.inst_outputs) insts)
End

(* Upper bound on version numbers: each output version_var v n from
   rename_outputs has n < get_counter rs' v (requires colon_free) *)
Triviality rename_outputs_ver_upper:
  !outs rs rs' outs'.
    EVERY colon_free outs /\
    rename_outputs rs outs = (rs', outs') ==>
    !x v n. MEM x outs' /\ colon_free v /\
            x = version_var v n ==>
            n < get_counter rs' v
Proof
  Induct >- rw[rename_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[]
  (* Case 1: x = version_var h ver (the newly produced output) *)
  >- (imp_res_tac version_var_inj >> gvs[] >>
      imp_res_tac push_version_counter >>
      imp_res_tac rename_outputs_counter_mono >>
      first_x_assum (qspec_then `h` mp_tac) >>
      gvs[get_counter_def])
  (* Both cases solved by case 1 tactic *)
QED

(* Counter monotonicity for rename_inst *)
Triviality rename_inst_counter_mono:
  !rs inst rs' inst'.
    rename_inst rs inst = (rs', inst') ==>
    !v. get_counter rs' v >= get_counter rs v
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rename_outputs_counter_mono]
QED

(* Counter monotonicity for rename_block_insts *)
Triviality rename_block_insts_counter_mono:
  !insts rs rs' insts'.
    rename_block_insts rs insts = (rs', insts') ==>
    !v. get_counter rs' v >= get_counter rs v
Proof
  Induct >- (rw[rename_block_insts_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt strip_tac >>
  imp_res_tac rename_inst_counter_mono >>
  first_x_assum (qspec_then `v` mp_tac) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

(* Upper bound: all outputs from rename_inst have version < counter after *)
Triviality rename_inst_ver_upper:
  !rs inst rs' inst'.
    EVERY colon_free inst.inst_outputs /\
    rename_inst rs inst = (rs', inst') ==>
    !x v n. MEM x inst'.inst_outputs /\ colon_free v /\
            x = version_var v n ==>
            n < get_counter rs' v
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rename_outputs_ver_upper]
QED

(* Lower bound: all outputs from rename_inst have version >= counter before *)
Triviality rename_inst_ver_lower:
  !rs inst rs' inst'.
    EVERY colon_free inst.inst_outputs /\
    rename_inst rs inst = (rs', inst') ==>
    !x v n. MEM x inst'.inst_outputs /\ colon_free v /\
            x = version_var v n ==>
            n >= get_counter rs v
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rename_outputs_versions_ge]
QED

(* Key lemma: all_output_vars from rename_block_insts are ALL_DISTINCT
   and have version numbers in [get_counter rs, get_counter rs') for
   their respective base variables.

   We prove ALL_DISTINCT all_output_vars and the range property together. *)
(* Range property: outputs of rename_block_insts have version numbers
   in [get_counter rs, get_counter rs') for each base variable *)
Triviality rename_block_insts_ver_range:
  !insts rs rs' insts'.
    EVERY (\i. EVERY colon_free i.inst_outputs) insts /\
    rename_block_insts rs insts = (rs', insts') ==>
    (!x v n. MEM x (all_output_vars insts') /\ colon_free v /\
             x = version_var v n ==>
             n >= get_counter rs v /\ n < get_counter rs' v)
Proof
  Induct >- rw[rename_block_insts_def, all_output_vars_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[all_output_vars_def, MEM_FLAT, MEM_MAP] >>
  gvs[MEM_APPEND]
  (* Head case: output from renamed head instruction *)
  >- (sg `n >= get_counter rs v`
      >- (imp_res_tac rename_inst_ver_lower >> gvs[]) >>
      sg `n < get_counter rs'' v`
      >- (imp_res_tac rename_inst_ver_upper >> gvs[]) >>
      sg `get_counter rs' v >= get_counter rs'' v`
      >- (imp_res_tac rename_block_insts_counter_mono >> gvs[]) >>
      gvs[GREATER_EQ] >> DECIDE_TAC)
  (* Tail case: output from recursive result *)
  >- (sg `n >= get_counter rs'' v /\ n < get_counter rs' v`
      >- (qpat_x_assum `!v' n'. _ /\ colon_free v' ==> _`
            (qspecl_then [`v`, `n`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (qexists_tac `i.inst_outputs` >>
                  conj_tac >- (qexists_tac `i` >> simp[]) >>
                  simp[]) >>
              simp[]) >>
          simp[]) >>
      sg `get_counter rs'' v >= get_counter rs v`
      >- (imp_res_tac rename_inst_counter_mono >> gvs[]) >>
      gvs[GREATER_EQ] >> DECIDE_TAC)
QED

(* Each instruction's outputs are a version_var with colon_free base *)
Triviality rename_outputs_is_version_var:
  !outs rs rs' outs'.
    EVERY colon_free outs /\
    rename_outputs rs outs = (rs', outs') ==>
    !x. MEM x outs' ==> ?base ver. x = version_var base ver /\ colon_free base
Proof
  Induct >- rw[rename_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Triviality rename_inst_output_is_version_var:
  !rs inst rs' inst'.
    EVERY colon_free inst.inst_outputs /\
    rename_inst rs inst = (rs', inst') ==>
    !x. MEM x inst'.inst_outputs ==>
        ?base ver. x = version_var base ver /\ colon_free base
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rename_outputs_is_version_var]
QED

(* Block-level: all outputs of renamed block are version_vars *)
Triviality rename_block_insts_is_version_var:
  !insts rs rs' insts'.
    EVERY (\i. EVERY colon_free i.inst_outputs) insts /\
    rename_block_insts rs insts = (rs', insts') ==>
    !x. MEM x (all_output_vars insts') ==>
        ?base ver. x = version_var base ver /\ colon_free base
Proof
  Induct >- rw[rename_block_insts_def, all_output_vars_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rpt strip_tac >> gvs[all_output_vars_def, MEM_FLAT, MEM_MAP] >>
  gvs[MEM_APPEND]
  >- (drule_all rename_inst_output_is_version_var >> metis_tac[])
  >- (first_x_assum drule >> strip_tac >>
      gvs[all_output_vars_def, MEM_FLAT, MEM_MAP] >> metis_tac[])
QED

(* ALL_DISTINCT for a single renamed instruction's outputs *)
Triviality rename_inst_all_distinct_outputs:
  !rs inst rs' inst'.
    EVERY colon_free inst.inst_outputs /\
    rename_inst rs inst = (rs', inst') ==>
    ALL_DISTINCT inst'.inst_outputs
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rename_outputs_all_distinct, pairTheory.SND]
QED

(* No overlap between head instruction outputs and tail outputs,
   because head versions < get_counter rs'' and tail versions >= get_counter rs'' *)
Triviality rename_block_head_tail_disjoint:
  !h insts rs rs'' rs' inst' rest'.
    EVERY colon_free h.inst_outputs /\
    EVERY (\i. EVERY colon_free i.inst_outputs) insts /\
    rename_inst rs h = (rs'', inst') /\
    rename_block_insts rs'' insts = (rs', rest') ==>
    !x. MEM x inst'.inst_outputs ==> ~MEM x (all_output_vars rest')
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  drule_all rename_inst_output_is_version_var >> strip_tac >> gvs[] >>
  (* Head: ver < get_counter rs'' base' *)
  qspecl_then [`rs`, `h`, `rs''`, `inst'`] mp_tac rename_inst_ver_upper >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`version_var base' ver`, `base'`, `ver`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  (* Tail: ver >= get_counter rs'' base' *)
  qspecl_then [`insts`, `rs''`, `rs'`, `rest'`] mp_tac
    rename_block_insts_ver_range >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`version_var base' ver`, `base'`, `ver`] mp_tac) >>
  impl_tac >- simp[] >>
  gvs[GREATER_EQ]
QED

Triviality rename_block_insts_distinct_outputs:
  !insts rs rs' insts'.
    EVERY (\i. EVERY colon_free i.inst_outputs) insts /\
    rename_block_insts rs insts = (rs', insts') ==>
    ALL_DISTINCT (all_output_vars insts')
Proof
  Induct >- rw[rename_block_insts_def, all_output_vars_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[all_output_vars_def] >>
  rw[ALL_DISTINCT_APPEND]
  >- (imp_res_tac rename_inst_all_distinct_outputs)
  >- (rpt strip_tac >>
      gvs[GSYM all_output_vars_def] >>
      imp_res_tac rename_block_head_tail_disjoint >>
      metis_tac[])
QED

(* Counter monotonicity for rename_blocks (returns only counters) *)
Triviality rename_blocks_counter_mono:
  (!dtree rs bbs succ_map ctrs' bbs'.
    rename_blocks rs bbs succ_map dtree = (ctrs', bbs') ==>
    !v. (case ALOOKUP ctrs' v of NONE => 0 | SOME n => n) >=
        get_counter rs v) /\
  (!children ctrs stacks bbs succ_map ctrs' bbs'.
    rename_children ctrs stacks bbs succ_map children = (ctrs', bbs') ==>
    !v. (case ALOOKUP ctrs' v of NONE => 0 | SOME n => n) >=
        (case ALOOKUP ctrs v of NONE => 0 | SOME n => n))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  (* DNode s children: IH on children, prove for rename_blocks *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC[rename_blocks_def] >>
      Cases_on `lookup_block s bbs` >> gvs[] >>
      TRY (strip_tac >> gvs[get_counter_def] >>
           BasicProvers.EVERY_CASE_TAC >> gvs[] >> NO_TAC) >>
      simp[LET_THM] >> pairarg_tac >> gvs[] >>
      strip_tac >> gen_tac >>
      qpat_x_assum `!ctrs stacks bbs' succ_map' ctrs'' bbs''. _`
        (drule_then (qspec_then `v` mp_tac)) >>
      qspecl_then [`x.bb_instructions`, `rs`, `rs1`, `insts'`]
        mp_tac rename_block_insts_counter_mono >>
      simp[] >> strip_tac >>
      first_x_assum (qspec_then `v` mp_tac) >>
      gvs[get_counter_def] >>
      BasicProvers.EVERY_CASE_TAC >> gvs[GREATER_EQ] >> DECIDE_TAC)
  (* children = [] *)
  >- simp[Once rename_blocks_def]
  (* dtree::children *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once rename_blocks_def, LET_THM] >>
      pairarg_tac >> gvs[] >>
      strip_tac >> gen_tac >>
      (* IH for children: drule with rename_children assm *)
      qpat_x_assum `!ctrs stacks bbs' succ_map' ctrs'' bbs''. rename_children _ _ _ _ children = _ ==> _`
        (drule_then (qspec_then `v` mp_tac)) >>
      (* IH for dtree: drule with rename_blocks assm *)
      qpat_x_assum `!rs bbs' succ_map' ctrs'' bbs''. rename_blocks _ _ _ dtree = _ ==> _`
        (drule_then (qspec_then `v` mp_tac)) >>
      gvs[get_counter_def] >>
      BasicProvers.EVERY_CASE_TAC >> gvs[GREATER_EQ] >> DECIDE_TAC)
QED

(* Modifying only inst_operands preserves inst_outputs *)
Triviality modify_operands_preserves_outputs:
  !insts f.
    MAP (\i. i.inst_outputs)
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else inst with inst_operands := f inst) insts) =
    MAP (\i. i.inst_outputs) insts
Proof
  Induct >> simp[] >> rw[] >> gvs[]
QED

(* Single step: processing one successor preserves output MAP *)
Triviality update_one_succ_preserves_outputs:
  !s rs lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    let bbs' = case lookup_block s bbs of
                 NONE => bbs
               | SOME sbb =>
                   replace_block s
                     (sbb with bb_instructions :=
                        MAP (\inst. if inst.inst_opcode <> PHI then inst
                                    else inst with inst_operands :=
                                      update_phi_for_pred rs lbl inst.inst_operands)
                          sbb.bb_instructions) bbs in
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs' =
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs')
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac lookup_block_label >>
  conj_tac
  >- (simp[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
      rw[MAP_EQ_f] >> rpt strip_tac >> rw[] >>
      drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO]
        venomExecProofsTheory.MEM_lookup_block) >>
      strip_tac >> gvs[modify_operands_preserves_outputs])
  >- (irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> gvs[])
QED

(* update_succ_phis preserves instruction outputs under ALL_DISTINCT labels *)
Triviality update_succ_phis_preserves_outputs:
  !succs rs lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions)
      (update_succ_phis rs lbl bbs succs) =
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label)
      (update_succ_phis rs lbl bbs succs))
Proof
  simp[update_succ_phis_def] >>
  Induct >> simp[] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `FOLDL _ bbs' succs` >>
  `MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs' =
   MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs /\
   ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs')` suffices_by (
    strip_tac >> first_x_assum drule >> metis_tac[]) >>
  simp[Abbr `bbs'`] >>
  irule (SIMP_RULE std_ss [LET_THM] update_one_succ_preserves_outputs) >>
  simp[]
QED

(* Helper: collect outputs from specific labels in a block list *)
Definition collect_outputs_def:
  collect_outputs bbs labels =
    FLAT (MAP (\lbl. case lookup_block lbl bbs of
                       NONE => []
                     | SOME bb => all_output_vars bb.bb_instructions) labels)
End

(* When update_succ_phis preserves the output map, individual lookups preserve *)
Triviality output_map_eq_lookup:
  !bbs bbs'.
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs' =
    MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs ==>
    !lbl bb bb'. lookup_block lbl bbs = SOME bb /\
                 lookup_block lbl bbs' = SOME bb' ==>
      MAP (\i. i.inst_outputs) bb'.bb_instructions =
      MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `bbs'` >> gvs[] >>
  strip_tac >> rpt gen_tac >>
  rw[lookup_block_def, FIND_thm] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[lookup_block_def] >>
  metis_tac[]
QED

(* Given matching labels, lookup at one list implies lookup at other *)
Triviality labels_eq_lookup_exists:
  !lbl bbs bbs'.
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    lookup_block lbl bbs <> NONE ==>
    ?bb'. lookup_block lbl bbs' = SOME bb'
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `bbs'` >> gvs[] >>
  rw[lookup_block_def, FIND_thm] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  first_x_assum (qspecl_then [`lbl`, `t`] mp_tac) >>
  simp[lookup_block_def]
QED

(* One rename step (replace_block + update_succ_phis) preserves outputs at
   any label different from the target. *)
Triviality rename_step_preserves_other_lookup:
  !s x insts' rs succs bbs lbl bb.
    lookup_block s bbs = SOME x /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lbl <> s /\ lookup_block lbl bbs = SOME bb ==>
    let bbs_mid = update_succ_phis rs s
          (replace_block s (x with bb_instructions := insts') bbs) succs in
    ?bb_mid. lookup_block lbl bbs_mid = SOME bb_mid /\
             MAP (\i. i.inst_outputs) bb_mid.bb_instructions =
             MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  rpt strip_tac >> simp[LET_THM] >>
  imp_res_tac lookup_block_label >>
  (* 1. lookup at lbl in replace_block result *)
  qspecl_then [`lbl`, `s`, `x with bb_instructions := insts'`, `bbs`] mp_tac
    cfgTransformPropsTheory.lookup_block_replace_neq >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* 2. ALL_DISTINCT for replace_block result *)
  qspecl_then [`s`, `x with bb_instructions := insts'`, `bbs`] mp_tac
    cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
  (impl_tac >- gvs[]) >>
  REWRITE_TAC[cfgTransformProofsTheory.fn_labels_replace_block
    |> Q.SPECL [`s`, `x with bb_instructions := insts'`]
    |> SIMP_RULE std_ss [combinTheory.K_THM]] >>
  strip_tac >>
  (* 3. output MAP equality through update_succ_phis *)
  qspecl_then [`succs`, `rs`, `s`,
    `replace_block s (x with bb_instructions := insts') bbs`] mp_tac
    update_succ_phis_preserves_outputs >>
  (impl_tac >- gvs[cfgTransformProofsTheory.fn_labels_replace_block]) >>
  strip_tac >>
  (* 4. lookup exists in bbs2 via labels_eq_lookup_exists *)
  qspecl_then [`lbl`,
    `replace_block s (x with bb_instructions := insts') bbs`,
    `update_succ_phis rs s
       (replace_block s (x with bb_instructions := insts') bbs) succs`]
    mp_tac labels_eq_lookup_exists >>
  (impl_tac >- gvs[update_succ_phis_preserves_labels]) >>
  strip_tac >>
  (* 5. outputs match via output_map_eq_lookup *)
  qexists_tac `bb'` >> simp[] >>
  irule (REWRITE_RULE [AND_IMP_INTRO] output_map_eq_lookup) >>
  qexistsl_tac [`replace_block s (x with bb_instructions := insts') bbs`,
    `update_succ_phis rs s
       (replace_block s (x with bb_instructions := insts') bbs) succs`,
    `lbl`] >>
  gvs[update_succ_phis_preserves_labels]
QED

(* DNode case helper for rename_blocks_preserves_non_tree_outputs *)
(* DNode case helper — children is free (matches dom_tree_induction IH) *)
Triviality dnode_preserves_non_tree_outputs:
  (!ctrs stacks bbs succ_map ctrs' bbs'.
    rename_children ctrs stacks bbs succ_map children = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    (!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
       lookup_block lbl bbs = SOME bb /\
       lookup_block lbl bbs' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
  !s rs bbs succ_map ctrs' bbs'.
    rename_blocks rs bbs succ_map (DNode s children) = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    (!lbl bb bb'. ~MEM lbl (dom_tree_labels (DNode s children)) /\
       lookup_block lbl bbs = SOME bb /\
       lookup_block lbl bbs' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions)
Proof
  strip_tac >> rpt gen_tac >>
  ONCE_REWRITE_TAC[rename_blocks_def] >>
  Cases_on `lookup_block s bbs` >> gvs[]
  >- (rpt strip_tac >> gvs[]) >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >> strip_tac >>
  imp_res_tac lookup_block_label >>
  qmatch_asmsub_abbrev_tac `rename_children _ _ bbs_mid` >>
  first_x_assum
    (qspecl_then [`FST rs1`, `SND rs1`, `bbs_mid`,
                  `succ_map`, `ctrs'`, `bbs'`] mp_tac) >>
  (impl_tac >- (
    gvs[Abbr `bbs_mid`, update_succ_phis_preserves_labels] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> gvs[])) >>
  strip_tac >>
  rpt conj_tac
  >- gvs[]
  >- (gvs[] >>
      simp[Abbr `bbs_mid`, update_succ_phis_preserves_labels,
           cfgTransformProofsTheory.fn_labels_replace_block])
  >> (rpt gen_tac >> simp[dom_tree_labels_def] >> strip_tac >>
      qunabbrev_tac `bbs_mid` >>
      qspecl_then [`s`, `x`, `insts'`, `rs1`,
        `case ALOOKUP succ_map s of NONE => [] | SOME ss => ss`,
        `bbs`, `lbl`, `bb`] mp_tac
        rename_step_preserves_other_lookup >>
      simp[LET_THM] >>
      strip_tac >>
      qpat_x_assum `!lbl bb bb'. _ /\ lookup_block lbl _ = SOME bb /\
        lookup_block lbl bbs' = SOME bb' ==> _`
        (qspecl_then [`lbl`, `bb_mid`, `bb'`] mp_tac) >>
      impl_tac >- metis_tac[] >>
      metis_tac[])
QED

(* Cons case helper for rename_blocks_preserves_non_tree_outputs *)
Triviality cons_preserves_non_tree_outputs:
  ((!rs bbs succ_map ctrs' bbs'.
     rename_blocks rs bbs succ_map dtree = (ctrs',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
     MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
     (!lbl bb bb'. ~MEM lbl (dom_tree_labels dtree) /\
        lookup_block lbl bbs = SOME bb /\
        lookup_block lbl bbs' = SOME bb' ==>
        MAP (\i. i.inst_outputs) bb'.bb_instructions =
        MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
   (!ctrs stacks bbs succ_map ctrs' bbs'.
     rename_children ctrs stacks bbs succ_map children = (ctrs',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
     MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
     (!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
        lookup_block lbl bbs = SOME bb /\
        lookup_block lbl bbs' = SOME bb' ==>
        MAP (\i. i.inst_outputs) bb'.bb_instructions =
        MAP (\i. i.inst_outputs) bb.bb_instructions))) ==>
  !ctrs stacks bbs succ_map ctrs'' bbs''.
    rename_children ctrs stacks bbs succ_map (dtree::children) = (ctrs'', bbs'') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs'') /\
    MAP (\bb. bb.bb_label) bbs'' = MAP (\bb. bb.bb_label) bbs /\
    (!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels (dtree::children))) /\
       lookup_block lbl bbs = SOME bb /\
       lookup_block lbl bbs'' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions)
Proof
  strip_tac >> rpt gen_tac >>
  simp[Once rename_blocks_def, LET_THM] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  (* Apply IH for child: rename_blocks ... dtree *)
  qpat_x_assum `!rs bbs succ_map ctrs' bbs'. rename_blocks _ _ _ dtree = _ /\ _ ==> _`
    (drule_then strip_assume_tac) >>
  (* Apply IH for rest: rename_children ... children *)
  qpat_x_assum `!ctrs stacks bbs succ_map ctrs' bbs'. rename_children _ _ _ _ children = _ /\ _ ==> _`
    (fn ih =>
      qspecl_then [`ctrs'`, `stacks`, `bbs'`, `succ_map`, `ctrs''`, `bbs''`]
        mp_tac ih) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  gvs[dom_tree_labels_def, MEM_FLAT, MEM_MAP] >>
  (* From child IH: lbl not in dtree → lookup preserved from bbs to bbs' *)
  qspecl_then [`lbl`, `bbs`, `bbs'`] mp_tac labels_eq_lookup_exists >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Use child IH output preservation: bbs → bbs' preserves at lbl *)
  qpat_x_assum `!lbl bb bb'. ~MEM lbl (dom_tree_labels dtree) /\ _ ==> _`
    (qspecl_then [`lbl`, `bb`, `bb''`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Use rest IH output preservation: bbs' → bbs'' preserves at lbl *)
  first_x_assum (qspecl_then [`lbl`, `bb''`, `bb'`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  metis_tac[]
QED

(* rename_blocks preserves outputs at labels not in the tree *)
Triviality rename_blocks_preserves_non_tree_outputs:
  (!dtree rs bbs succ_map ctrs' bbs'.
    rename_blocks rs bbs succ_map dtree = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    (!lbl bb bb'. ~MEM lbl (dom_tree_labels dtree) /\
       lookup_block lbl bbs = SOME bb /\
       lookup_block lbl bbs' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  (!children ctrs stacks bbs succ_map ctrs' bbs'.
    rename_children ctrs stacks bbs succ_map children = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    (!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
       lookup_block lbl bbs = SOME bb /\
       lookup_block lbl bbs' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    (* DNode *)
    rpt gen_tac >> strip_tac >>
    mp_tac dnode_preserves_non_tree_outputs >>
    (impl_tac >- first_x_assum ACCEPT_TAC) >>
    simp[],
    (* [] *)
    simp[Once rename_blocks_def] >> rpt strip_tac >> gvs[],
    (* cons *)
    rpt gen_tac >> disch_tac >>
    mp_tac cons_preserves_non_tree_outputs >>
    (impl_tac >- first_x_assum ACCEPT_TAC) >>
    simp[]
  ]
QED

(* collect_outputs distributes over APPEND *)
Triviality collect_outputs_append:
  !bbs xs ys. collect_outputs bbs (xs ++ ys) =
              collect_outputs bbs xs ++ collect_outputs bbs ys
Proof
  rw[collect_outputs_def]
QED

(* collect_outputs cons *)
Triviality collect_outputs_cons:
  !bbs x xs. collect_outputs bbs (x::xs) =
    (case lookup_block x bbs of
       NONE => []
     | SOME bb => all_output_vars bb.bb_instructions) ++
    collect_outputs bbs xs
Proof
  rw[collect_outputs_def]
QED

(* collect_outputs nil *)
Triviality collect_outputs_nil:
  !bbs. collect_outputs bbs [] = []
Proof
  rw[collect_outputs_def]
QED

(* When outputs at a label are preserved between bbs and bbs',
   collect_outputs at that label agrees *)
Triviality collect_outputs_preserved:
  !bbs bbs' lbl rest.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    ~MEM lbl (FLAT (MAP dom_tree_labels rest)) /\
    (!l bb bb'. ~MEM l (FLAT (MAP dom_tree_labels rest)) /\
       lookup_block l bbs = SOME bb /\ lookup_block l bbs' = SOME bb' ==>
       MAP (\i. i.inst_outputs) bb'.bb_instructions =
       MAP (\i. i.inst_outputs) bb.bb_instructions) ==>
    !bb bb'. lookup_block lbl bbs = SOME bb /\
             lookup_block lbl bbs' = SOME bb' ==>
    all_output_vars bb'.bb_instructions = all_output_vars bb.bb_instructions
Proof
  rpt strip_tac >> gvs[all_output_vars_def] >>
  first_x_assum drule_all >> simp[]
QED

(* Output MAP equality preserves colon_free EVERY *)
Triviality output_map_eq_colon_free:
  !insts1 insts2.
    MAP (\i. i.inst_outputs) insts1 = MAP (\i. i.inst_outputs) insts2 ==>
    (EVERY (\i. EVERY colon_free i.inst_outputs) insts1 <=>
     EVERY (\i. EVERY colon_free i.inst_outputs) insts2)
Proof
  Induct >> Cases_on `insts2` >> gvs[] >> rpt strip_tac >> metis_tac[]
QED

(* Cross-block distinctness: rename_blocks produces blocks whose collected
   outputs are ALL_DISTINCT with version numbers in the counter range.
   Proved by dom_tree mutual induction.

   The colon_free precondition is restricted to blocks in the current subtree,
   because already-visited blocks have version_var outputs (not colon_free). *)
(* Comprehensive rename_step properties: labels, ALL_DISTINCT, and
   output preservation at other labels. Unifies the repeated pattern. *)
Triviality rename_step_props:
  !s x insts' rs succs bbs.
    lookup_block s bbs = SOME x /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    let bbs' = update_succ_phis rs s
                 (replace_block s (x with bb_instructions := insts') bbs) succs in
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs') /\
    (!lbl bb_orig. lbl <> s /\ lookup_block lbl bbs = SOME bb_orig ==>
       ?bb_new. lookup_block lbl bbs' = SOME bb_new /\
               MAP (\i. i.inst_outputs) bb_new.bb_instructions =
               MAP (\i. i.inst_outputs) bb_orig.bb_instructions) /\
    (!lbl. lbl <> s /\ lookup_block lbl bbs <> NONE ==>
           lookup_block lbl bbs' <> NONE)
Proof
  rpt strip_tac >> simp[LET_THM] >>
  drule lookup_block_label >> strip_tac >> gvs[] >>
  rpt conj_tac
  >- simp[update_succ_phis_preserves_labels,
          cfgTransformProofsTheory.fn_labels_replace_block]
  >- (simp[update_succ_phis_preserves_labels] >>
      irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> gvs[])
  >- (rpt strip_tac >>
      qspecl_then [`x.bb_label`, `x`, `insts'`, `rs`, `succs`,
        `bbs`, `lbl`, `bb_orig`] mp_tac rename_step_preserves_other_lookup >>
      simp[LET_THM])
  >- (rpt strip_tac >>
      Cases_on `lookup_block lbl bbs` >> gvs[] >>
      qspecl_then [`x.bb_label`, `x`, `insts'`, `rs`, `succs`,
        `bbs`, `lbl`] mp_tac rename_step_preserves_other_lookup >>
      simp[LET_THM])
QED

(* Version-range disjointness: two lists of version_vars with non-overlapping
   ranges [lo, mid) and [mid, hi) are disjoint, hence ALL_DISTINCT when appended *)
(* Combine two output lists with disjoint version ranges [lo,mid) and [mid,hi)
   into a single list with range [lo,hi). *)
Triviality ver_range_combine:
  !xs ys lo mid hi.
    ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
    (!base ver. MEM (version_var base ver) xs /\ colon_free base ==>
       ver >= lo base /\ ver < mid base) /\
    (!base ver. MEM (version_var base ver) ys /\ colon_free base ==>
       ver >= mid base /\ ver < hi base) /\
    (!x. MEM x xs ==> ?base ver. colon_free base /\ x = version_var base ver) /\
    (!y. MEM y ys ==> ?base ver. colon_free base /\ y = version_var base ver) /\
    (!base. lo base <= mid base) /\
    (!base. mid base <= hi base) ==>
    ALL_DISTINCT (xs ++ ys) /\
    (!base ver. MEM (version_var base ver) (xs ++ ys) /\
       colon_free base ==>
       ver >= lo base /\ ver < hi base) /\
    (!x. MEM x (xs ++ ys) ==>
       ?base ver. colon_free base /\ x = version_var base ver)
Proof
  rpt gen_tac >> strip_tac >>
  `!e. MEM e xs ==> ~MEM e ys` suffices_by (
    strip_tac >> simp[ALL_DISTINCT_APPEND, MEM_APPEND] >>
    rpt conj_tac >> rpt strip_tac >> gvs[] >>
    res_tac >> gvs[GREATER_EQ] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
  ) >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  `?b v. colon_free b /\ e = version_var b v`
    suffices_by (strip_tac >> gvs[] >>
      res_tac >> gvs[GREATER_EQ] >> DECIDE_TAC) >>
  metis_tac[]
QED

(* After replace_block + update_succ_phis, block s exists and
   its outputs match the replaced instructions *)
Triviality rename_step_self_lookup:
  !s x insts' rs succs bbs.
    lookup_block s bbs = SOME x /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ?bb_s. lookup_block s
             (update_succ_phis rs s
               (replace_block s (x with bb_instructions := insts') bbs) succs) =
           SOME bb_s /\
           MAP (\i. i.inst_outputs) bb_s.bb_instructions =
           MAP (\i. i.inst_outputs) insts'
Proof
  rpt strip_tac >>
  drule lookup_block_label >> strip_tac >> gvs[] >>
  (* Step 1: block exists in replace_block result *)
  qspecl_then [`x.bb_label`, `x with bb_instructions := insts'`, `bbs`]
    mp_tac cfgTransformProofsTheory.lookup_block_replace_eq >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Step 2: ALL_DISTINCT for replace_block result *)
  qspecl_then [`x.bb_label`, `x with bb_instructions := insts'`, `bbs`]
    mp_tac cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Step 3: update_succ_phis preserves positional output MAP *)
  qspecl_then [`succs`, `rs`, `x.bb_label`,
    `replace_block x.bb_label (x with bb_instructions := insts') bbs`]
    mp_tac update_succ_phis_preserves_outputs >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Step 4: lookup s exists in updated bbs *)
  qspecl_then [`x.bb_label`,
    `replace_block x.bb_label (x with bb_instructions := insts') bbs`,
    `update_succ_phis rs x.bb_label
      (replace_block x.bb_label (x with bb_instructions := insts') bbs) succs`]
    mp_tac labels_eq_lookup_exists >>
  (impl_tac >- simp[update_succ_phis_preserves_labels]) >> strip_tac >>
  (* Step 5: output MAP matches *)
  qexists_tac `bb'` >> simp[] >>
  qspecl_then [`update_succ_phis rs x.bb_label
      (replace_block x.bb_label (x with bb_instructions := insts') bbs) succs`,
    `replace_block x.bb_label (x with bb_instructions := insts') bbs`]
    mp_tac output_map_eq_lookup >>
  (impl_tac >- simp[update_succ_phis_preserves_labels]) >>
  disch_then (qspecl_then [`x.bb_label`, `bb'`,
    `x with bb_instructions := insts'`] mp_tac) >> simp[]
QED

(* rename_step preserves IH preconditions (lookup + colon_free) at labels ≠ s *)
Triviality rename_step_preserves_ih_precond:
  !s x insts' rs succs bbs labels.
    lookup_block s bbs = SOME x /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    ~MEM s labels /\
    (!lbl. MEM lbl labels ==> lookup_block lbl bbs <> NONE) /\
    (!lbl bb. MEM lbl labels /\ lookup_block lbl bbs = SOME bb ==>
       EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions) ==>
    let bbs' = update_succ_phis rs s
                 (replace_block s (x with bb_instructions := insts') bbs) succs in
    (!lbl. MEM lbl labels ==> lookup_block lbl bbs' <> NONE) /\
    (!lbl bb. MEM lbl labels /\ lookup_block lbl bbs' = SOME bb ==>
       EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
Proof
  rpt strip_tac >> simp[LET_THM] >>
  qspecl_then [`s`, `x`, `insts'`, `rs`, `succs`, `bbs`]
    mp_tac (SIMP_RULE std_ss [LET_THM] rename_step_props) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  conj_tac >| [
    (* Conjunct 1: lookup preservation *)
    rpt strip_tac >>
    qpat_x_assum `!l. l <> s /\ _ ==> _` (qspec_then `lbl` mp_tac) >>
    (impl_tac >- (conj_tac >- (CCONTR_TAC >> gvs[]) >> res_tac)) >>
    simp[],
    (* Conjunct 2: colon_free preservation *)
    rpt gen_tac >> strip_tac >>
    `lbl <> s` suffices_by (strip_tac >>
      Cases_on `lookup_block lbl bbs`
      >- (qpat_x_assum `!l. MEM l labels ==> _` drule >> gvs[]) >>
      rename1 `lookup_block lbl bbs = SOME bb_orig` >>
      qpat_x_assum `!l bo. l <> s /\ _ ==> _`
        (qspecl_then [`lbl`, `bb_orig`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >> gvs[] >>
      qpat_x_assum `!l b. MEM l labels /\ _ ==> _`
        (qspecl_then [`lbl`, `bb_orig`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      qspecl_then [`bb_orig.bb_instructions`, `bb.bb_instructions`]
        mp_tac output_map_eq_colon_free >> gvs[]) >>
    CCONTR_TAC >> gvs[]
  ]
QED

(* DNode helper for cross_distinct — takes children IH as hypothesis *)
Triviality dnode_cross_distinct:
  !children s rs bbs succ_map ctrs' bbs'.
    (* Children IH *)
    (!ctrs stacks bbs0 succ_map0 ctrs0' bbs0'.
      rename_children ctrs stacks bbs0 succ_map0 children = (ctrs0', bbs0') /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0) /\
      (!lbl. MEM lbl (FLAT (MAP dom_tree_labels children)) ==>
             lookup_block lbl bbs0 <> NONE) /\
      (!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels children)) /\
                lookup_block lbl bbs0 = SOME bb ==>
                EVERY (\i. EVERY colon_free i.inst_outputs)
                  bb.bb_instructions) /\
      ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) ==>
      ALL_DISTINCT (collect_outputs bbs0' (FLAT (MAP dom_tree_labels children))) /\
      (!x base ver.
         MEM x (collect_outputs bbs0' (FLAT (MAP dom_tree_labels children))) /\
         colon_free base /\ x = version_var base ver ==>
         ver >= (case ALOOKUP ctrs base of NONE => 0 | SOME n => n) /\
         ver < (case ALOOKUP ctrs0' base of NONE => 0 | SOME n => n)) /\
      (!x. MEM x (collect_outputs bbs0' (FLAT (MAP dom_tree_labels children))) ==>
           ?base ver. colon_free base /\ x = version_var base ver) /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0')) /\
    (* rename_blocks equation *)
    rename_blocks rs bbs succ_map (DNode s children) = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (!lbl. MEM lbl (dom_tree_labels (DNode s children)) ==>
           lookup_block lbl bbs <> NONE) /\
    (!lbl bb. MEM lbl (dom_tree_labels (DNode s children)) /\
              lookup_block lbl bbs = SOME bb ==>
              EVERY (\i. EVERY colon_free i.inst_outputs)
                bb.bb_instructions) /\
    ALL_DISTINCT (dom_tree_labels (DNode s children)) ==>
    ALL_DISTINCT (collect_outputs bbs' (dom_tree_labels (DNode s children))) /\
    (!x base ver. MEM x (collect_outputs bbs' (dom_tree_labels (DNode s children))) /\
                  colon_free base /\ x = version_var base ver ==>
                  ver >= get_counter rs base /\
                  ver < (case ALOOKUP ctrs' base of NONE => 0
                         | SOME n => n)) /\
    (!x. MEM x (collect_outputs bbs' (dom_tree_labels (DNode s children))) ==>
         ?base ver. colon_free base /\ x = version_var base ver) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs')
Proof
  rpt gen_tac >> strip_tac >>
  (* ---- Phase A: Derive bridge facts from dom_tree_labels (DNode s children) ---- *)
  (* A1: ~MEM s (FLAT ...) and ALL_DISTINCT (FLAT ...) *)
  `~MEM s (FLAT (MAP dom_tree_labels children)) /\
   ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by
    (qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
     simp[dom_tree_labels_def, ETA_THM]) >>
  (* A2: lookup transfer for FLAT members *)
  `!lbl. MEM lbl (FLAT (MAP dom_tree_labels children)) ==>
         lookup_block lbl bbs <> NONE` by
    (rpt strip_tac >>
     qpat_x_assum `!lbl. MEM lbl (dom_tree_labels _) ==> _`
       (qspec_then `lbl` mp_tac) >> simp[dom_tree_labels_def, ETA_THM]) >>
  `!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels children)) /\
            lookup_block lbl bbs = SOME bb ==>
            EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!lbl bb. MEM lbl (dom_tree_labels _) /\ _ ==> _`
       (qspecl_then [`lbl`, `bb`] mp_tac) >> simp[dom_tree_labels_def, ETA_THM]) >>
  (* ---- Phase B: Unfold rename_blocks for DNode ---- *)
  qpat_x_assum `rename_blocks _ _ _ (DNode _ _) = _` mp_tac >>
  ONCE_REWRITE_TAC[rename_blocks_def] >>
  Cases_on `lookup_block s bbs`
  >- (qpat_x_assum `!lbl. MEM lbl (dom_tree_labels (DNode s children)) ==> _`
        (qspec_then `s` mp_tac) >> simp[dom_tree_labels_def]) >>
  gvs[] >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
  qabbrev_tac `bbs_mid = update_succ_phis rs1 s
    (replace_block s (x with bb_instructions := insts') bbs) succs` >>
  (* ---- Phase C: Apply helpers with simple impl_tac ---- *)
  (* C1: rename_step_props for bbs_mid *)
  qspecl_then [`s`, `x`, `insts'`, `rs1`, `succs`, `bbs`]
    mp_tac (SIMP_RULE std_ss [LET_THM] rename_step_props) >>
  (impl_tac >- gvs[Abbr `succs`]) >> strip_tac >>
  (* C2: rename_step_self_lookup for block s in bbs_mid *)
  qspecl_then [`s`, `x`, `insts'`, `rs1`, `succs`, `bbs`]
    mp_tac rename_step_self_lookup >>
  (impl_tac >- gvs[Abbr `succs`]) >> strip_tac >>
  (* C3: IH preconditions transfer to bbs_mid *)
  qspecl_then [`s`, `x`, `insts'`, `rs1`, `succs`, `bbs`,
    `FLAT (MAP dom_tree_labels children)`]
    mp_tac (SIMP_RULE std_ss [LET_THM]
      rename_step_preserves_ih_precond) >>
  (impl_tac >- (rpt conj_tac \\ gvs[])) >>
  simp[Abbr `bbs_mid`] >> strip_tac >>
  (* C4: Apply children IH *)
  qpat_x_assum `!ctrs stacks bbs0 succ_map0 ctrs0' bbs0'. _`
    (qspecl_then [`FST rs1`, `SND rs1`,
      `update_succ_phis rs1 s
        (replace_block s (x with bb_instructions := insts') bbs) succs`,
      `succ_map`, `ctrs'`, `bbs'`] mp_tac) >>
  (impl_tac >- (rpt conj_tac \\ gvs[])) >> strip_tac >>
  (* C4b: Get label preservation and non-tree output facts from rename_children *)
  qspecl_then [`children`, `FST rs1`, `SND rs1`,
    `update_succ_phis rs1 s
      (replace_block s (x with bb_instructions := insts') bbs) succs`,
    `succ_map`, `ctrs'`, `bbs'`]
    mp_tac (CONJUNCT2 rename_blocks_preserves_non_tree_outputs) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* C4c: counter monotonicity: rs1 <= (ctrs', bbs') *)
  qspecl_then [`children`, `FST rs1`, `SND rs1`,
    `update_succ_phis rs1 s
      (replace_block s (x with bb_instructions := insts') bbs) succs`,
    `succ_map`, `ctrs'`, `bbs'`]
    mp_tac (SIMP_RULE std_ss [GREATER_EQ] (CONJUNCT2 rename_blocks_counter_mono)) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* C5: block s in bbs' via labels_eq_lookup_exists *)
  qspecl_then [`s`,
    `update_succ_phis rs1 s
      (replace_block s (x with bb_instructions := insts') bbs) succs`,
    `bbs'`] mp_tac labels_eq_lookup_exists >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* C6: colon_free for block s *)
  `EVERY (\i. EVERY colon_free i.inst_outputs) x.bb_instructions` by
    (qpat_x_assum `!lbl bb. MEM lbl (dom_tree_labels _) /\ _ ==> _`
       (qspecl_then [`s`, `x`] mp_tac) >>
     simp[dom_tree_labels_def]) >>
  (* ---- Phase D: Combine via ver_range_combine ---- *)
  (* D: Rewrite goal to collect_outputs form with ++ *)
  ONCE_REWRITE_TAC[dom_tree_labels_def] >>
  ONCE_REWRITE_TAC[collect_outputs_cons] >>
  ASM_SIMP_TAC bool_ss [ETA_THM, optionTheory.option_case_def] >>
  (* D1: output structure match for block s in bbs' *)
  qpat_x_assum `!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\ _ ==> _`
    (qspecl_then [`s`, `bb_s`, `bb'`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* D2: Derive all facts needed for ver_range_combine *)
  (* D2a: head ALL_DISTINCT *)
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts'))` by
    (qspecl_then [`x.bb_instructions`, `rs`, `rs1`, `insts'`]
       mp_tac rename_block_insts_distinct_outputs >>
     gvs[all_output_vars_def]) >>
  (* D2b: head version range *)
  `!y base ver. MEM y (FLAT (MAP (\i. i.inst_outputs) insts')) /\
     colon_free base /\ y = version_var base ver ==>
     ver >= get_counter rs base /\ ver < get_counter rs1 base` by
    (rpt strip_tac >>
     qspecl_then [`x.bb_instructions`, `rs`, `rs1`, `insts'`]
       mp_tac (REWRITE_RULE [all_output_vars_def] rename_block_insts_ver_range) >>
     (impl_tac >- gvs[]) >>
     disch_then drule_all >> gvs[]) >>
  (* D2c: head is_version_var *)
  `!y. MEM y (FLAT (MAP (\i. i.inst_outputs) insts')) ==>
     ?base ver. colon_free base /\ y = version_var base ver` by
    (rpt strip_tac >>
     qspecl_then [`x.bb_instructions`, `rs`, `rs1`, `insts'`]
       mp_tac (REWRITE_RULE [all_output_vars_def] rename_block_insts_is_version_var) >>
     (impl_tac >- gvs[]) >>
     disch_then drule >> strip_tac >> metis_tac[]) >>
  (* D2d: lo <= mid *)
  `!base. get_counter rs base <= get_counter rs1 base` by
    (gen_tac >>
     qspecl_then [`x.bb_instructions`, `rs`, `rs1`, `insts'`]
       mp_tac rename_block_insts_counter_mono >>
     gvs[GREATER_EQ, get_counter_def]) >>
  (* D2e: mid <= hi — use C4c counter_mono fact *)
  `!base. get_counter rs1 base <= get_counter (ctrs', bbs') base` by
    simp[get_counter_def] >>
  (* D2f: children version range — fold get_counter *)
  `!y base ver. MEM y (collect_outputs bbs' (FLAT (MAP dom_tree_labels children))) /\
     colon_free base /\ y = version_var base ver ==>
     ver >= get_counter rs1 base /\ ver < get_counter (ctrs', bbs') base` by
    simp[get_counter_def] >>
  (* D2g: children is_version_var — already available as assumption *)
  (* D3: fold case ALOOKUP ctrs' into get_counter, then apply ver_range_combine *)
  `!base. (case ALOOKUP ctrs' base of NONE => 0 | SOME n => n) =
          get_counter (ctrs', bbs') base` by simp[get_counter_def] >>
  REWRITE_TAC[all_output_vars_def] >>
  ASM_REWRITE_TAC[] >>
  MATCH_MP_TAC ver_range_combine >>
  qexists_tac `\base. get_counter rs1 base` >>
  BETA_TAC >> rpt conj_tac \\ gvs[]
QED

(* If per-label output lookups agree, collect_outputs agree *)
Triviality collect_outputs_eq:
  !labels bbs1 bbs2.
    (!lbl. MEM lbl labels ==>
       (case lookup_block lbl bbs1 of
          NONE => []
        | SOME bb => all_output_vars bb.bb_instructions) =
       (case lookup_block lbl bbs2 of
          NONE => []
        | SOME bb => all_output_vars bb.bb_instructions)) ==>
    collect_outputs bbs1 labels = collect_outputs bbs2 labels
Proof
  Induct >> rw[collect_outputs_def] >>
  last_x_assum (qspecl_then [`bbs1`, `bbs2`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> simp[collect_outputs_def]
QED

(* Cons helper for cross_distinct — takes P0 and P1 IH as hypotheses *)
Triviality cons_cross_distinct:
  !d rest ctrs stacks bbs succ_map ctrs' bbs'.
    (* P0 d IH *)
    (!rs0 bbs0 succ_map0 ctrs0' bbs0'.
      rename_blocks rs0 bbs0 succ_map0 d = (ctrs0', bbs0') /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0) /\
      (!lbl. MEM lbl (dom_tree_labels d) ==> lookup_block lbl bbs0 <> NONE) /\
      (!lbl bb. MEM lbl (dom_tree_labels d) /\ lookup_block lbl bbs0 = SOME bb ==>
                EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions) /\
      ALL_DISTINCT (dom_tree_labels d) ==>
      ALL_DISTINCT (collect_outputs bbs0' (dom_tree_labels d)) /\
      (!x base ver. MEM x (collect_outputs bbs0' (dom_tree_labels d)) /\
                    colon_free base /\ x = version_var base ver ==>
                    ver >= get_counter rs0 base /\
                    ver < (case ALOOKUP ctrs0' base of NONE => 0 | SOME n => n)) /\
      (!x. MEM x (collect_outputs bbs0' (dom_tree_labels d)) ==>
           ?base ver. colon_free base /\ x = version_var base ver) /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0')) /\
    (* P1 rest IH *)
    (!ctrs0 stacks0 bbs0 succ_map0 ctrs0' bbs0'.
      rename_children ctrs0 stacks0 bbs0 succ_map0 rest = (ctrs0', bbs0') /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0) /\
      (!lbl. MEM lbl (FLAT (MAP dom_tree_labels rest)) ==>
             lookup_block lbl bbs0 <> NONE) /\
      (!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels rest)) /\
                lookup_block lbl bbs0 = SOME bb ==>
                EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions) /\
      ALL_DISTINCT (FLAT (MAP dom_tree_labels rest)) ==>
      ALL_DISTINCT (collect_outputs bbs0' (FLAT (MAP dom_tree_labels rest))) /\
      (!x base ver. MEM x (collect_outputs bbs0' (FLAT (MAP dom_tree_labels rest))) /\
                    colon_free base /\ x = version_var base ver ==>
                    ver >= (case ALOOKUP ctrs0 base of NONE => 0 | SOME n => n) /\
                    ver < (case ALOOKUP ctrs0' base of NONE => 0 | SOME n => n)) /\
      (!x. MEM x (collect_outputs bbs0' (FLAT (MAP dom_tree_labels rest))) ==>
           ?base ver. colon_free base /\ x = version_var base ver) /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0')) /\
    (* Equation and preconditions *)
    rename_children ctrs stacks bbs succ_map (d::rest) = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (!lbl. MEM lbl (FLAT (MAP dom_tree_labels (d::rest))) ==>
           lookup_block lbl bbs <> NONE) /\
    (!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels (d::rest))) /\
              lookup_block lbl bbs = SOME bb ==>
              EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels (d::rest))) ==>
    ALL_DISTINCT (collect_outputs bbs' (FLAT (MAP dom_tree_labels (d::rest)))) /\
    (!x base ver.
       MEM x (collect_outputs bbs' (FLAT (MAP dom_tree_labels (d::rest)))) /\
       colon_free base /\ x = version_var base ver ==>
       ver >= (case ALOOKUP ctrs base of NONE => 0 | SOME n => n) /\
       ver < (case ALOOKUP ctrs' base of NONE => 0 | SOME n => n)) /\
    (!x. MEM x (collect_outputs bbs' (FLAT (MAP dom_tree_labels (d::rest)))) ==>
         ?base ver. colon_free base /\ x = version_var base ver) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs')
Proof
  rpt gen_tac >> strip_tac >>
  (* Unfold rename_children for d::rest *)
  qpat_x_assum `rename_children _ _ _ _ (d::rest) = _` mp_tac >>
  simp[Once rename_blocks_def, LET_THM] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  (* Now: rename_blocks (ctrs,stacks) bbs succ_map d = (ctrs'',bbs'')
     and  rename_children ctrs'' stacks bbs'' succ_map rest = (ctrs',bbs')
     Assumptions already have disjunctive MEM form from gvs[] *)
  (* Phase A: Bridge facts *)
  `ALL_DISTINCT (dom_tree_labels d)` by
    (imp_res_tac ALL_DISTINCT_APPEND) >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels rest))` by
    (imp_res_tac ALL_DISTINCT_APPEND) >>
  `!lbl. MEM lbl (dom_tree_labels d) ==> lookup_block lbl bbs <> NONE` by
    (rpt strip_tac >>
     qpat_x_assum `!lbl. MEM lbl (dom_tree_labels d) \/ _ ==> _`
       (qspec_then `lbl` mp_tac) >> simp[]) >>
  `!lbl. MEM lbl (FLAT (MAP dom_tree_labels rest)) ==> lookup_block lbl bbs <> NONE` by
    (rpt strip_tac >>
     qpat_x_assum `!lbl. MEM lbl (dom_tree_labels d) \/ _ ==> _`
       (qspec_then `lbl` mp_tac) >> simp[]) >>
  `!lbl bb. MEM lbl (dom_tree_labels d) /\ lookup_block lbl bbs = SOME bb ==>
     EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions` by
    (rpt strip_tac >>
     qpat_x_assum `!lbl bb. (_ \/ _) /\ _ ==> _`
       (qspecl_then [`lbl`, `bb`] mp_tac) >> simp[]) >>
  `!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels rest)) /\ lookup_block lbl bbs = SOME bb ==>
     EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions` by
    (rpt strip_tac >>
     qpat_x_assum `!lbl bb. (_ \/ _) /\ _ ==> _`
       (qspecl_then [`lbl`, `bb`] mp_tac) >> simp[]) >>
  (* Phase B: Apply P0 IH (rename_blocks d) *)
  qpat_x_assum `!rs0 bbs0 succ_map0 ctrs0' bbs0'.
    rename_blocks rs0 bbs0 succ_map0 d = (ctrs0', bbs0') /\ _ ==> _`
    (qspecl_then [`(ctrs, stacks)`, `bbs`, `succ_map`, `ctrs''`, `bbs''`] mp_tac) >>
  (impl_tac >- (rpt conj_tac \\ gvs[])) >>
  strip_tac >>
  (* Phase C: Transfer preconditions for rest from bbs to bbs'' *)
  (* C1: non-tree outputs preserved by rename_blocks d *)
  qspecl_then [`d`, `(ctrs, stacks)`, `bbs`, `succ_map`, `ctrs''`, `bbs''`]
    mp_tac (CONJUNCT1 rename_blocks_preserves_non_tree_outputs) >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  (* C2: counter monotonicity for d *)
  qspecl_then [`d`, `(ctrs, stacks)`, `bbs`, `succ_map`, `ctrs''`, `bbs''`]
    mp_tac (CONJUNCT1 rename_blocks_counter_mono) >>
  (impl_tac >- gvs[]) >>
  disch_then (ASSUME_TAC o SIMP_RULE std_ss [GREATER_EQ]) >>
  (* C3: disjointness: rest labels not in d's tree *)
  `!lbl. MEM lbl (FLAT (MAP dom_tree_labels rest)) ==> ~MEM lbl (dom_tree_labels d)` by
    (rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]) >>
  (* C4: lookup transfer for rest labels from bbs to bbs'' *)
  `!lbl. MEM lbl (FLAT (MAP dom_tree_labels rest)) ==>
    lookup_block lbl bbs'' <> NONE` by
    (rpt strip_tac >>
     `~MEM lbl (dom_tree_labels d)` by gvs[] >>
     `lookup_block lbl bbs <> NONE` by gvs[] >>
     drule_all labels_eq_lookup_exists >> simp[]) >>
  (* C5: colon_free transfer for rest labels from bbs to bbs'' *)
  `!lbl bb'. MEM lbl (FLAT (MAP dom_tree_labels rest)) /\
     lookup_block lbl bbs'' = SOME bb' ==>
     EVERY (\i. EVERY colon_free i.inst_outputs) bb'.bb_instructions` by
    (rpt gen_tac >> disch_tac >>
     `~MEM lbl (dom_tree_labels d)` by gvs[] >>
     `?bb_orig. lookup_block lbl bbs = SOME bb_orig` by
       (Cases_on `lookup_block lbl bbs` >> gvs[]) >>
     qpat_x_assum `!lbl bb bb'. ~MEM lbl (dom_tree_labels d) /\ _ ==> _`
       (qspecl_then [`lbl`, `bb_orig`, `bb'`] mp_tac) >>
     (impl_tac >- gvs[]) >> strip_tac >>
     `EVERY (\i. EVERY colon_free i.inst_outputs) bb_orig.bb_instructions` by
       (first_x_assum (qspecl_then [`lbl`, `bb_orig`] mp_tac) >> gvs[]) >>
     metis_tac[output_map_eq_colon_free]) >>
  (* Phase D: Apply P1 IH (rename_children rest) *)
  qpat_x_assum `!ctrs0 stacks0 bbs0 succ_map0 ctrs0' bbs0'.
    rename_children ctrs0 stacks0 bbs0 succ_map0 rest = (ctrs0', bbs0') /\ _ ==> _`
    (qspecl_then [`ctrs''`, `stacks`, `bbs''`, `succ_map`, `ctrs'`, `bbs'`] mp_tac) >>
  (impl_tac >- (rpt conj_tac \\ gvs[])) >>
  strip_tac >>
  (* Phase E: non-tree outputs preserved by rename_children rest *)
  qspecl_then [`rest`, `ctrs''`, `stacks`, `bbs''`, `succ_map`, `ctrs'`, `bbs'`]
    mp_tac (CONJUNCT2 rename_blocks_preserves_non_tree_outputs) >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  (* E1: d-labels disjoint from rest => outputs for d preserved bbs'' → bbs' *)
  `collect_outputs bbs' (dom_tree_labels d) =
   collect_outputs bbs'' (dom_tree_labels d)` by
    (MATCH_MP_TAC collect_outputs_eq >>
     rpt strip_tac >>
     `~MEM lbl (FLAT (MAP dom_tree_labels rest))` by
       (gvs[ALL_DISTINCT_APPEND]) >>
     Cases_on `lookup_block lbl bbs''`
     >- (* bbs'' NONE: label not in bbs'' → not in bbs' either *)
       (Cases_on `lookup_block lbl bbs'` >> simp[] >>
        `lookup_block lbl bbs'' <> NONE` by
          (qspecl_then [`lbl`, `bbs'`, `bbs''`] mp_tac labels_eq_lookup_exists >>
           gvs[]) >>
        gvs[])
     >- (* bbs'' SOME x: get corresponding block in bbs' *)
       (`lookup_block lbl bbs'' <> NONE` by gvs[] >>
        qspecl_then [`lbl`, `bbs''`, `bbs'`] mp_tac labels_eq_lookup_exists >>
        (impl_tac >- gvs[]) >> strip_tac >>
        gvs[] >>
        qpat_x_assum `!lbl bb bb'. ~MEM lbl (FLAT (MAP dom_tree_labels rest)) /\ _ ==> _`
          (qspecl_then [`lbl`, `x`, `bb'`] mp_tac) >>
        gvs[all_output_vars_def])) >>
  (* E2: counter monotonicity for rest *)
  qspecl_then [`rest`, `ctrs''`, `stacks`, `bbs''`, `succ_map`, `ctrs'`, `bbs'`]
    mp_tac (CONJUNCT2 rename_blocks_counter_mono) >>
  (impl_tac >- gvs[]) >>
  disch_then (ASSUME_TAC o SIMP_RULE std_ss [GREATER_EQ]) >>
  (* Phase F: unify to ALOOKUP form, apply ver_range_combine *)
  RULE_ASSUM_TAC (REWRITE_RULE [get_counter_def, pairTheory.FST]) >>
  qspecl_then
    [`collect_outputs bbs'' (dom_tree_labels d)`,
     `collect_outputs bbs' (FLAT (MAP dom_tree_labels rest))`,
     `\base. case ALOOKUP ctrs base of NONE => 0 | SOME n => n`,
     `\base. case ALOOKUP ctrs'' base of NONE => 0 | SOME n => n`,
     `\base. case ALOOKUP ctrs' base of NONE => 0 | SOME n => n`]
    mp_tac ver_range_combine >>
  BETA_TAC >>
  (impl_tac >- (rpt conj_tac \\ ASM_REWRITE_TAC[])) >>
  strip_tac >> simp[collect_outputs_append]
QED

Triviality rename_blocks_cross_distinct:
  (!dtree rs bbs succ_map ctrs' bbs'.
    rename_blocks rs bbs succ_map dtree = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (!lbl. MEM lbl (dom_tree_labels dtree) ==>
           lookup_block lbl bbs <> NONE) /\
    (!lbl bb. MEM lbl (dom_tree_labels dtree) /\
              lookup_block lbl bbs = SOME bb ==>
              EVERY (\i. EVERY colon_free i.inst_outputs)
                bb.bb_instructions) /\
    ALL_DISTINCT (dom_tree_labels dtree) ==>
    ALL_DISTINCT (collect_outputs bbs' (dom_tree_labels dtree)) /\
    (!x base ver. MEM x (collect_outputs bbs' (dom_tree_labels dtree)) /\
                  colon_free base /\ x = version_var base ver ==>
                  ver >= get_counter rs base /\
                  ver < (case ALOOKUP ctrs' base of NONE => 0
                         | SOME n => n)) /\
    (!x. MEM x (collect_outputs bbs' (dom_tree_labels dtree)) ==>
         ?base ver. colon_free base /\ x = version_var base ver) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs')) /\
  (!children ctrs stacks bbs succ_map ctrs' bbs'.
    rename_children ctrs stacks bbs succ_map children = (ctrs', bbs') /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (!lbl. MEM lbl (FLAT (MAP dom_tree_labels children)) ==>
           lookup_block lbl bbs <> NONE) /\
    (!lbl bb. MEM lbl (FLAT (MAP dom_tree_labels children)) /\
              lookup_block lbl bbs = SOME bb ==>
              EVERY (\i. EVERY colon_free i.inst_outputs)
                bb.bb_instructions) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) ==>
    ALL_DISTINCT (collect_outputs bbs' (FLAT (MAP dom_tree_labels children))) /\
    (!x base ver.
       MEM x (collect_outputs bbs' (FLAT (MAP dom_tree_labels children))) /\
       colon_free base /\ x = version_var base ver ==>
       ver >= (case ALOOKUP ctrs base of NONE => 0 | SOME n => n) /\
       ver < (case ALOOKUP ctrs' base of NONE => 0 | SOME n => n)) /\
    (!x. MEM x (collect_outputs bbs' (FLAT (MAP dom_tree_labels children))) ==>
         ?base ver. colon_free base /\ x = version_var base ver) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs'))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  >- ((* DNode s children *)
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    mp_tac (SPEC_ALL dnode_cross_distinct) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[])
  >- ((* [] *)
    simp[Once rename_blocks_def, collect_outputs_def])
  >- ((* d::rest *)
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qspecl_then [`dtree`, `children`, `ctrs`, `stacks`, `bbs`, `succ_map`,
                 `ctrs'`, `bbs'`]
      mp_tac cons_cross_distinct >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[])
QED

(* Key bridge: ALL_DISTINCT of FLAT(MAP f xs) means shared elements identify their source *)
Triviality all_distinct_flat_map_unique:
  !f xs x y v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM x xs /\ MEM y xs /\ MEM v (f x) /\ MEM v (f y) ==>
    x = y
Proof
  gen_tac >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  Cases_on `x = h` >> Cases_on `y = h` >> gvs[] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

(* Bridge: ALL_DISTINCT outputs of fn_insts => ssa_form *)
Triviality all_distinct_outputs_ssa_form:
  !func.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts func))) ==>
    ssa_form func
Proof
  simp[ssa_form_def]
QED

(* PERM of labels gives PERM of collect_outputs *)
Triviality collect_outputs_perm:
  !labels1 labels2 bbs.
    PERM labels1 labels2 ==>
    PERM (collect_outputs bbs labels1) (collect_outputs bbs labels2)
Proof
  simp[collect_outputs_def] >>
  metis_tac[PERM_MAP, PERM_FLAT]
QED

(* collect_outputs over own labels = fn_insts outputs *)
Triviality collect_outputs_eq_fn_insts_outputs:
  !bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    collect_outputs bbs (MAP (\bb. bb.bb_label) bbs) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))
Proof
  Induct >>
  simp[collect_outputs_nil, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  (* Peel head label *)
  ONCE_REWRITE_TAC[fn_insts_blocks_def] >>
  ONCE_REWRITE_TAC[collect_outputs_cons] >>
  (* lookup_block h.bb_label (h::bbs) = SOME h *)
  `lookup_block h.bb_label (h::bbs) = SOME h` by
    (irule MEM_lookup_block >> simp[]) >>
  ASM_SIMP_TAC bool_ss [optionTheory.option_case_def, all_output_vars_def] >>
  AP_TERM_TAC >>
  (* collect_outputs (h::bbs) (MAP bb_label bbs) = collect_outputs bbs (MAP bb_label bbs) *)
  `collect_outputs (h::bbs) (MAP (\bb. bb.bb_label) bbs) =
   collect_outputs bbs (MAP (\bb. bb.bb_label) bbs)` by
    (irule collect_outputs_eq >> rpt gen_tac >> strip_tac >>
     `lbl <> h.bb_label` by
       (CCONTR_TAC >> gvs[MEM_MAP] >> metis_tac[]) >>
     simp[lookup_block_def, FIND_thm]) >>
  ASM_REWRITE_TAC[] >>
  first_x_assum irule >> gvs[]
QED

(* build_phi_inst outputs are colon_free if var is colon_free *)
Triviality build_phi_inst_colon_free:
  !var preds. colon_free var ==>
    EVERY colon_free (build_phi_inst var preds).inst_outputs
Proof
  simp[build_phi_inst_def]
QED

(* block_assignments extracts from inst_outputs, so colon_free transfers *)
Triviality block_assignments_colon_free:
  !bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions ==>
       EVERY colon_free (block_assignments bb)
Proof
  rw[block_assignments_def, EVERY_MEM, MEM_nub, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[EVERY_MEM]
QED

(* process_frontiers preserves colon_free outputs *)
Triviality process_frontiers_colon_free:
  !var pred_map live_in bbs rest has_phi fs.
    colon_free var /\
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      bbs ==>
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      (FST (process_frontiers var pred_map live_in bbs rest has_phi fs))
Proof
  Induct_on `fs` >>
  simp[process_frontiers_def] >>
  rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM] >>
  first_x_assum irule >> simp[EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >>
  Cases_on `bb.bb_label = h` >>
  gvs[insert_phi_at_block_def, build_phi_inst_def, EVERY_MEM] >>
  metis_tac[]
QED

(* insert_phis_for_var preserves colon_free outputs *)
Triviality insert_phis_for_var_colon_free:
  !var dom_frontiers pred_map live_in bbs worklist has_phi.
    colon_free var /\
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      bbs ==>
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      (insert_phis_for_var var dom_frontiers pred_map live_in bbs
         worklist has_phi)
Proof
  ho_match_mp_tac insert_phis_for_var_ind >> rpt strip_tac >>
  ONCE_REWRITE_TAC[insert_phis_for_var_def] >>
  simp[] >> BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  `FST (process_frontiers var pred_map live_in bbs rest has_phi
     (case ALOOKUP dom_frontiers d of NONE => [] | SOME fs => fs)) = bbs'` by
    (Cases_on `process_frontiers var pred_map live_in bbs rest has_phi
       (case ALOOKUP dom_frontiers d of NONE => [] | SOME fs => fs)` >>
     Cases_on `r` >> gvs[]) >>
  metis_tac[process_frontiers_colon_free]
QED

(* add_phi_nodes preserves colon_free outputs *)
Triviality add_phi_nodes_colon_free:
  !defs df pred_map live_in bbs.
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      bbs /\
    EVERY (\p. colon_free (FST p)) defs ==>
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      (add_phi_nodes df pred_map live_in bbs defs)
Proof
  Induct_on `defs` >>
  simp[add_phi_nodes_def] >>
  rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[] >>
  simp[GSYM add_phi_nodes_def] >>
  first_x_assum irule >> simp[] >>
  irule insert_phis_for_var_colon_free >> simp[]
QED

(* alist_update_or_prepend preserves FST predicate *)
Triviality alist_update_or_prepend_preserves_fst:
  !k f d acc.
    P k /\ EVERY (\p. P (FST p)) acc ==>
    EVERY (\p. P (FST p)) (alist_update_or_prepend k f d acc)
Proof
  Induct_on `acc` >> simp[alist_update_or_prepend_def] >>
  rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[alist_update_or_prepend_def] >>
  Cases_on `h0 = k` >> gvs[]
QED

(* FOLDR of alist_update_or_prepend preserves FST predicate *)
Triviality foldr_aup_preserves_fst:
  !vars f d acc.
    EVERY P vars /\ EVERY (\p. P (FST p)) acc ==>
    EVERY (\p. P (FST p))
      (FOLDR (\var acc. alist_update_or_prepend var f d acc) acc vars)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  irule alist_update_or_prepend_preserves_fst >> simp[] >>
  first_x_assum irule >> simp[]
QED

(* compute_defs produces colon_free var names *)
Triviality compute_defs_colon_free:
  !bbs.
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      bbs ==>
    EVERY (\p. colon_free (FST p)) (compute_defs bbs)
Proof
  Induct >> simp[compute_defs_def] >> rpt strip_tac >> simp[LET_THM] >>
  irule foldr_aup_preserves_fst >> simp[] >>
  irule block_assignments_colon_free >> simp[]
QED

(* MEM in labels implies lookup exists *)
Triviality mem_labels_lookup_exists:
  !lbl bbs.
    MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs <> NONE
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >>
  simp[lookup_block_def]
QED

Triviality every_lookup_block:
  !bbs P.
    EVERY (\bb. P bb.bb_instructions) bbs ==>
    !lbl bb. lookup_block lbl bbs = SOME bb ==>
             P bb.bb_instructions
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `h.bb_label = lbl` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[lookup_block_def]
QED

(* ssa_form for make_ssa_fn *)
Theorem make_ssa_fn_ssa_form:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              EVERY colon_free inst.inst_outputs) ==>
    ssa_form (make_ssa_fn dom_frontiers dtree dom_post_order
                pred_map succ_map live_in func)
Proof
  rpt gen_tac >> strip_tac >>
  simp[make_ssa_fn_def] >>
  (* valid_dom_tree gives fn_entry_label = SOME entry *)
  `?entry children. dtree = DNode entry children /\
                    fn_entry_label func = SOME entry` by
    (gvs[valid_dom_tree_def] >> metis_tac[]) >>
  gvs[] >> simp[LET_THM] >>
  (* Name intermediate results *)
  qabbrev_tac `defs = compute_defs
    (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))` >>
  qabbrev_tac `bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                         func.fn_blocks defs` >>
  qabbrev_tac `rs0 = init_rename_state defs` >>
  Cases_on `rename_blocks rs0 bbs1 succ_map (DNode entry children)` >>
  rename1 `rename_blocks _ _ _ _ = (ctrs', bbs2)` >>
  simp[] >>
  (* === Phase A: Establish reusable intermediate facts === *)
  (* A1: label chain bbs2 = bbs1 = fn_blocks *)
  `MAP (\bb. bb.bb_label) bbs2 = MAP (\bb. bb.bb_label) bbs1` by
    (`bbs2 = SND (rename_blocks rs0 bbs1 succ_map (DNode entry children))` by
       simp[] >>
     metis_tac[rename_blocks_preserves_labels]) >>
  `MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) func.fn_blocks` by
    metis_tac[add_phi_nodes_preserves_labels] >>
  (* A2: ALL_DISTINCT labels *)
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs2)` by
    gvs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    gvs[wf_function_def, fn_labels_def] >>
  (* A3: dtree facts from valid_dom_tree (forward, non-destructive) *)
  `ALL_DISTINCT (dom_tree_labels (DNode entry children))` by
    (qpat_x_assum `valid_dom_tree _ _ _ _` mp_tac >>
     simp[valid_dom_tree_def]) >>
  `set (dom_tree_labels (DNode entry children)) = set (fn_labels func)` by
    (qpat_x_assum `valid_dom_tree _ _ _ _` mp_tac >>
     simp[valid_dom_tree_def]) >>
  (* A4: PERM dtree_labels ~ MAP bb_label bbs2 *)
  `PERM (dom_tree_labels (DNode entry children))
        (MAP (\bb. bb.bb_label) bbs2)` by
    (irule PERM_ALL_DISTINCT >> simp[] >>
     gvs[fn_labels_def, EXTENSION] >> metis_tac[]) >>
  (* A5: colon_free for bbs1 *)
  `EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
           bb.bb_instructions) func.fn_blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[EVERY_MEM]) >>
  `EVERY (\p. colon_free (FST p)) defs` by
    (qunabbrev_tac `defs` >> irule compute_defs_colon_free >>
     gvs[EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
     rpt strip_tac >>
     Cases_on `lookup_block lbl func.fn_blocks` >> gvs[] >>
     imp_res_tac lookup_block_MEM >>
     gvs[EVERY_MEM] >> res_tac >> gvs[EVERY_MEM]) >>
  `EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
           bb.bb_instructions) bbs1` by
    (qunabbrev_tac `bbs1` >>
     irule add_phi_nodes_colon_free >> simp[]) >>
  (* A6: lookup exists for dtree labels in bbs1 *)
  `!lbl. MEM lbl (dom_tree_labels (DNode entry children)) ==>
         lookup_block lbl bbs1 <> NONE` by
    (rpt gen_tac >> disch_tac >>
     irule mem_labels_lookup_exists >>
     `MEM lbl (fn_labels func)` by
       (qpat_x_assum `set _ = set (fn_labels _)` mp_tac >>
        simp[EXTENSION] >> metis_tac[]) >>
     gvs[fn_labels_def]) >>
  (* === Phase B: Apply the chain === *)
  irule all_distinct_outputs_ssa_form >>
  `collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2) =
   FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs2))` by
    (irule collect_outputs_eq_fn_insts_outputs >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  (* A7: colon_free for bbs1 blocks via lookup *)
  `!lbl bb. lookup_block lbl bbs1 = SOME bb ==>
            EVERY (\i. EVERY colon_free i.inst_outputs)
              bb.bb_instructions` by
    metis_tac[every_lookup_block] >>
  (* B1: rename_blocks_cross_distinct *)
  qspecl_then [`DNode entry children`, `rs0`, `bbs1`, `succ_map`,
     `ctrs'`, `bbs2`]
     mp_tac (CONJUNCT1 rename_blocks_cross_distinct) >>
  simp[] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  (* B2: PERM transfer *)
  `PERM (collect_outputs bbs2 (dom_tree_labels (DNode entry children)))
        (collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2))` by
    (irule collect_outputs_perm >> simp[]) >>
  `ALL_DISTINCT (collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2))`
    by metis_tac[ALL_DISTINCT_PERM] >>
  gvs[fn_insts_def]
QED
