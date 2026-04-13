(*
 * CFG Normalization Pass -- Iteration and Main Theorem
 *
 * Depends on cfgNormProof for invariant preservation lemmas.
 *)

Theory cfgNormIter
Ancestors
  cfgNormProof cfgNormBase cfgNormDefs cfgNormSim cfgTransformProofs
  stateEquiv stateEquivProps venomExecSemantics execEquivProofs venomWf
  venomExecProps venomInstProps venomExecProofs prevBbIndep
Libs
  cfgNormProofTheory cfgNormBaseTheory cfgNormDefsTheory cfgNormSimTheory
  cfgTransformTheory cfgTransformProofsTheory stateEquivTheory
  stateEquivPropsTheory venomExecSemanticsTheory venomInstPropsTheory
  venomInstTheory venomStateTheory venomWfTheory venomExecPropsTheory
  venomExecProofsTheory prevBbIndepTheory finite_mapTheory

(* Helper: When two "A ++ _split_ ++ B ++ _fwd_ ++ var" strings are equal,
   and A,B,C,D are original labels (no _split_ substr, no _fwd 4-char substr,
   TAKE 6 <> "split_", and no "_split" suffix), then A=C and B=D.
   The no-"_split"-suffix condition (C19) is needed to kill the d=6 border case.
   CE without it: A="", B="split", C="_split", D="fwd", var="fwd_X", w="X". *)
Theorem split_fwd_cancel[local]:
  !A B C D var w.
    (!x y. A <> STRCAT x (STRCAT "_split_" y)) /\
    (!x y. B <> STRCAT x (STRCAT "_fwd" y)) /\
    (!x y. C <> STRCAT x (STRCAT "_split_" y)) /\
    (!x y. D <> STRCAT x (STRCAT "_fwd" y)) /\
    TAKE 6 B <> "split_" /\ TAKE 6 D <> "split_" /\
    (!x. A <> STRCAT x "_split") /\
    (!x. C <> STRCAT x "_split") /\
    STRCAT A (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var))) =
    STRCAT C (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w))) ==>
    A = C /\ B = D
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive STRLEN equation *)
  `STRLEN A + 7 + STRLEN B + 5 + STRLEN var =
   STRLEN C + 7 + STRLEN D + 5 + STRLEN w` by (
    qpat_x_assum `STRCAT A _ = STRCAT C _` (mp_tac o AP_TERM ``STRLEN``) >>
    simp[stringTheory.STRLEN_CAT, EVAL ``STRLEN "_split_"``,
         EVAL ``STRLEN "_fwd_"``]) >>
  (* Show |A| = |C| then use suffix cancellation *)
  `STRLEN A = STRLEN C` suffices_by (
    strip_tac >>
    `STRLEN (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var))) =
     STRLEN (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w)))` by
      simp[stringTheory.STRLEN_CAT] >>
    `A = C` by metis_tac[listTheory.APPEND_LENGTH_EQ] >>
    qpat_x_assum `STRCAT A _ = STRCAT C _` mp_tac >>
    qpat_x_assum `A = C` SUBST_ALL_TAC >>
    simp[stringTheory.STRCAT_11] >> strip_tac >>
    `STRCAT B (STRCAT "_fwd_" var) = STRCAT D (STRCAT "_fwd_" w)` by
      fs[stringTheory.STRCAT_11] >>
    mp_tac (Q.SPECL [`B`, `D`, `var`, `w`] fwd_cancel_right) >>
    simp[]) >>
  (* Proof by contradiction + case analysis on |A| vs |C| *)
  SPOSE_NOT_THEN ASSUME_TAC >>
  `STRLEN A < STRLEN C \/ STRLEN C < STRLEN A` by simp[]
  >- (
    (* |A| < |C|: DROP |A| from both sides *)
    `STRLEN A <= STRLEN C` by simp[] >>
    `DROP (STRLEN A) (STRCAT A (STRCAT "_split_"
       (STRCAT B (STRCAT "_fwd_" var)))) =
     STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var))` by
      simp[listTheory.DROP_APPEND1] >>
    `DROP (STRLEN A) (STRCAT C (STRCAT "_split_"
       (STRCAT D (STRCAT "_fwd_" w)))) =
     STRCAT (DROP (STRLEN A) C) (STRCAT "_split_"
       (STRCAT D (STRCAT "_fwd_" w)))` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var)) =
     STRCAT (DROP (STRLEN A) C) (STRCAT "_split_"
       (STRCAT D (STRCAT "_fwd_" w)))` by metis_tac[] >>
    qabbrev_tac `d = STRLEN C - STRLEN A` >>
    `STRLEN (DROP (STRLEN A) C) = d /\ d > 0` by
      simp[Abbr `d`] >>
    Cases_on `d >= 7`
    >- (
      (* d >= 7: C has "_split_" substring -- contradiction *)
      `TAKE d (STRCAT (DROP (STRLEN A) C) (STRCAT "_split_"
         (STRCAT D (STRCAT "_fwd_" w)))) =
       DROP (STRLEN A) C` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var))) =
       DROP (STRLEN A) C` by metis_tac[] >>
      `7 <= d` by simp[] >>
      `TAKE 7 (TAKE d (STRCAT "_split_"
         (STRCAT B (STRCAT "_fwd_" var)))) =
       TAKE 7 (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var)))` by
        simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 7 (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var))) =
       "_split_"` by (EVAL_TAC >> simp[]) >>
      `TAKE 7 (DROP (STRLEN A) C) = "_split_"` by metis_tac[] >>
      `DROP (STRLEN A) C =
       STRCAT (TAKE 7 (DROP (STRLEN A) C)) (DROP 7 (DROP (STRLEN A) C))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `C = STRCAT (TAKE (STRLEN A) C) (DROP (STRLEN A) C)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      (* 1 <= d <= 6 *)
      `d <= 6` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN C - STRLEN A) (STRCAT (DROP (STRLEN A) C)
         (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w)))) =
       DROP (STRLEN A) C` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN C - STRLEN A) (STRCAT "_split_"
         (STRCAT B (STRCAT "_fwd_" var))) =
       DROP (STRLEN A) C` by metis_tac[] >>
      `TAKE (STRLEN C - STRLEN A) (STRCAT "_split_"
         (STRCAT B (STRCAT "_fwd_" var))) =
       TAKE (STRLEN C - STRLEN A) "_split_"` by
        (irule listTheory.TAKE_APPEND1 >>
         simp[EVAL ``STRLEN "_split_"``]) >>
      `DROP (STRLEN A) C =
       TAKE (STRLEN C - STRLEN A) "_split_"` by metis_tac[] >>
      Cases_on `STRLEN C - STRLEN A = 6`
      >- (
        (* d=6: C = TAKE |A| C ++ "_split", contradicts no-suffix condition *)
        `C = STRCAT (TAKE (STRLEN A) C) (DROP (STRLEN A) C)` by
          metis_tac[listTheory.TAKE_DROP] >>
        `C = STRCAT (TAKE (STRLEN A) C) (TAKE 6 "_split_")` by
          metis_tac[] >>
        `TAKE 6 "_split_" = "_split"` by EVAL_TAC >>
        metis_tac[])
      >- (
        (* d = 1..5: char mismatch via EVAL *)
        `STRLEN C - STRLEN A = 1 \/ STRLEN C - STRLEN A = 2 \/
         STRLEN C - STRLEN A = 3 \/ STRLEN C - STRLEN A = 4 \/
         STRLEN C - STRLEN A = 5` by simp[] >>
        fs[])))
  >- (
    (* |A| > |C|: symmetric *)
    `STRLEN C < STRLEN A` by simp[] >>
    `STRLEN C <= STRLEN A` by simp[] >>
    `DROP (STRLEN C) (STRCAT C (STRCAT "_split_"
       (STRCAT D (STRCAT "_fwd_" w)))) =
     STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w))` by
      simp[listTheory.DROP_APPEND1] >>
    `DROP (STRLEN C) (STRCAT A (STRCAT "_split_"
       (STRCAT B (STRCAT "_fwd_" var)))) =
     STRCAT (DROP (STRLEN C) A) (STRCAT "_split_"
       (STRCAT B (STRCAT "_fwd_" var)))` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w)) =
     STRCAT (DROP (STRLEN C) A) (STRCAT "_split_"
       (STRCAT B (STRCAT "_fwd_" var)))` by metis_tac[] >>
    qabbrev_tac `d = STRLEN A - STRLEN C` >>
    `STRLEN (DROP (STRLEN C) A) = d /\ d > 0` by
      simp[Abbr `d`] >>
    Cases_on `d >= 7`
    >- (
      (* d >= 7: A has "_split_" substring -- contradiction *)
      `TAKE d (STRCAT (DROP (STRLEN C) A) (STRCAT "_split_"
         (STRCAT B (STRCAT "_fwd_" var)))) =
       DROP (STRLEN C) A` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w))) =
       DROP (STRLEN C) A` by metis_tac[] >>
      `7 <= d` by simp[] >>
      `TAKE 7 (TAKE d (STRCAT "_split_"
         (STRCAT D (STRCAT "_fwd_" w)))) =
       TAKE 7 (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w)))` by
        simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 7 (STRCAT "_split_" (STRCAT D (STRCAT "_fwd_" w))) =
       "_split_"` by (EVAL_TAC >> simp[]) >>
      `TAKE 7 (DROP (STRLEN C) A) = "_split_"` by metis_tac[] >>
      `DROP (STRLEN C) A =
       STRCAT (TAKE 7 (DROP (STRLEN C) A)) (DROP 7 (DROP (STRLEN C) A))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `A = STRCAT (TAKE (STRLEN C) A) (DROP (STRLEN C) A)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      (* 1 <= d <= 6 *)
      `d <= 6` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN A - STRLEN C) (STRCAT (DROP (STRLEN C) A)
         (STRCAT "_split_" (STRCAT B (STRCAT "_fwd_" var)))) =
       DROP (STRLEN C) A` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN A - STRLEN C) (STRCAT "_split_"
         (STRCAT D (STRCAT "_fwd_" w))) =
       DROP (STRLEN C) A` by metis_tac[] >>
      `TAKE (STRLEN A - STRLEN C) (STRCAT "_split_"
         (STRCAT D (STRCAT "_fwd_" w))) =
       TAKE (STRLEN A - STRLEN C) "_split_"` by
        (irule listTheory.TAKE_APPEND1 >>
         simp[EVAL ``STRLEN "_split_"``]) >>
      `DROP (STRLEN C) A =
       TAKE (STRLEN A - STRLEN C) "_split_"` by metis_tac[] >>
      Cases_on `STRLEN A - STRLEN C = 6`
      >- (
        (* d=6: A = TAKE |C| A ++ "_split", contradicts no-suffix condition *)
        `A = STRCAT (TAKE (STRLEN C) A) (DROP (STRLEN C) A)` by
          metis_tac[listTheory.TAKE_DROP] >>
        `A = STRCAT (TAKE (STRLEN C) A) (TAKE 6 "_split_")` by
          metis_tac[] >>
        `TAKE 6 "_split_" = "_split"` by EVAL_TAC >>
        metis_tac[])
      >- (
        (* d = 1..5: char mismatch via EVAL *)
        `STRLEN A - STRLEN C = 1 \/ STRLEN A - STRLEN C = 2 \/
         STRLEN A - STRLEN C = 3 \/ STRLEN A - STRLEN C = 4 \/
         STRLEN A - STRLEN C = 5` by simp[] >>
        fs[])))
QED

(* C11: variable freshness for fwd vars after insert_split.
   Uses insert_split_all_var_source to reduce to two cases:
   (1) var in fn_all_vars func -> IH from cfg_norm_inv
   (2) var has fwd form -> fwd_cancel_right *)
Theorem insert_split_fwd_var_inv[local]:
  !func0 func pred_bb target_bb id_base pred_lbl tgt_lbl var.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    num_succs pred_bb > 1 /\
    LENGTH (block_preds func target_bb.bb_label) > 1 /\
    MEM pred_lbl (fn_labels func0) /\ MEM tgt_lbl (fn_labels func0) /\
    MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
        (fn_all_vars (insert_split func pred_bb target_bb id_base)) ==>
    MEM (split_block_name pred_lbl tgt_lbl)
        (fn_labels (insert_split func pred_bb target_bb id_base))
Proof
  rpt strip_tac >>
  `MEM pred_bb.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`] pred_original) >> simp[]) >>
  `MEM target_bb.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `target_bb`] target_original) >> simp[]) >>
  `pred_bb.bb_label <> target_bb.bb_label` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_no_self_loop) >> simp[]) >>
  `ALL_DISTINCT (fn_labels func)` by (imp_res_tac cfg_norm_inv_labels_distinct) >>
  (* fn_labels func' = fn_labels func ++ [split_lbl] *)
  qabbrev_tac `split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label` >>
  (* Use insert_split_all_var_source to get disjunction — keep as assumption *)
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var`]
    insert_split_all_var_source) >>
  simp[] >> disch_tac >>
  (* Establish fn_labels of insert_split ONCE before case split *)
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    cfgNormSimTheory.fn_labels_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> simp[] >> strip_tac >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  simp[listTheory.MEM_APPEND, listTheory.MEM] >>
  (* Now case split on the disjunction *)
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  (* Case 1: var in fn_all_vars func -> IH gives split_lbl in fn_labels func *)
  >- (DISJ1_TAC >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_lbl`, `tgt_lbl`, `var`]
        cfg_norm_inv_var_fresh) >> simp[])
  (* Case 2: fwd form -> use split_fwd_cancel *)
  >> (DISJ2_TAC >>
      (* Extract all string conditions from cfg_norm_inv *)
      mp_tac (Q.SPECL [`func0`, `func`, `pred_lbl`] cfg_norm_inv_fwd_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `tgt_lbl`] cfg_norm_inv_fwd_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`] cfg_norm_inv_fwd_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `target_bb.bb_label`] cfg_norm_inv_fwd_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_lbl`] cfg_norm_inv_sep_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `tgt_lbl`] cfg_norm_inv_sep_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`] cfg_norm_inv_sep_clean) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `target_bb.bb_label`] cfg_norm_inv_sep_clean) >>
      simp[] >> strip_tac >>
      `split_labels_fresh split_block_name func0` by (
        qpat_x_assum `cfg_norm_inv _ _` mp_tac >> simp[cfg_norm_inv_def]) >>
      `!a b. pred_lbl <> STRCAT a (STRCAT "_split_" b)` by (
        rpt strip_tac >>
        mp_tac (Q.SPECL [`func0`, `pred_lbl`, `a`, `b`] original_no_split_substr) >>
        simp[]) >>
      `!a b. pred_bb.bb_label <> STRCAT a (STRCAT "_split_" b)` by (
        rpt strip_tac >>
        mp_tac (Q.SPECL [`func0`, `pred_bb.bb_label`, `a`, `b`] original_no_split_substr) >>
        simp[]) >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_lbl`] cfg_norm_inv_no_split_suffix) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`] cfg_norm_inv_no_split_suffix) >>
      simp[] >> strip_tac >>
      (* Rewrite equation to expose split_fwd structure *)
      qpat_x_assum `_ = STRCAT (STRCAT split_lbl _) _` mp_tac >>
      simp[Abbr `split_lbl`] >> strip_tac >>
      pop_assum mp_tac >>
      REWRITE_TAC[cfgNormDefsTheory.split_block_name_def,
                  GSYM stringTheory.STRCAT_ASSOC] >>
      strip_tac >>
      mp_tac (Q.SPECL [`pred_lbl`, `tgt_lbl`, `pred_bb.bb_label`,
        `target_bb.bb_label`, `var`, `w`] split_fwd_cancel) >>
      (impl_tac >- (
        RULE_ASSUM_TAC (REWRITE_RULE [GSYM stringTheory.STRCAT_ASSOC]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      simp[cfgNormDefsTheory.split_block_name_def])
QED

(* When both old and new labels have NONE for resolve_phi, update_phi_ops
   preserves NONE for the new label *)
Theorem resolve_phi_update_phi_ops_none[local]:
  !old_label new_label var_repls ops.
    resolve_phi old_label ops = NONE /\
    resolve_phi new_label ops = NONE ==>
    resolve_phi new_label
      (update_phi_ops old_label new_label var_repls ops) = NONE
Proof
  recInduct cfgNormDefsTheory.update_phi_ops_ind >>
  rw[cfgNormDefsTheory.update_phi_ops_def,
     venomExecSemanticsTheory.resolve_phi_def, LET_THM]
QED

(* C4: PHI non-interference for the target' block after insert_split.
   This is the key case: update_phis_for_split modifies PHI operands.
   Three sub-cases on the prev label (other/old/new). *)
Theorem phi_non_interfering_target[local]:
  !func pred_bb target_bb id_base split_bb var_repls
   inst1 inst2 out pred_lbl v.
    fn_phis_non_interfering func /\
    fn_phi_preds_closed func /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    (!var. ~MEM (STRCAT (STRCAT
        (split_block_name pred_bb.bb_label target_bb.bb_label) "_fwd_") var)
        (fn_all_vars func)) /\
    MEM inst1 (update_phis_for_split pred_bb.bb_label
      (split_block_name pred_bb.bb_label target_bb.bb_label)
      var_repls target_bb).bb_instructions /\
    inst1.inst_opcode = PHI /\
    MEM inst2 (update_phis_for_split pred_bb.bb_label
      (split_block_name pred_bb.bb_label target_bb.bb_label)
      var_repls target_bb).bb_instructions /\
    inst2.inst_opcode = PHI /\
    inst1 <> inst2 /\
    MEM out inst1.inst_outputs /\
    resolve_phi pred_lbl inst2.inst_operands = SOME (Var v) ==>
    out <> v
Proof
  rpt strip_tac >>
  (* Decompose inst1 to original *)
  `?inst1_0. MEM inst1_0 target_bb.bb_instructions /\
     inst1_0.inst_opcode = PHI /\
     inst1.inst_operands = update_phi_ops pred_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) var_repls
       inst1_0.inst_operands /\
     inst1.inst_outputs = inst1_0.inst_outputs /\
     inst1.inst_id = inst1_0.inst_id` by (
    mp_tac (Q.SPECL [`pred_bb.bb_label`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `var_repls`, `target_bb`, `inst1`] target_phi_operands) >>
    simp[]) >>
  (* Decompose inst2 to original *)
  `?inst2_0. MEM inst2_0 target_bb.bb_instructions /\
     inst2_0.inst_opcode = PHI /\
     inst2.inst_operands = update_phi_ops pred_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) var_repls
       inst2_0.inst_operands /\
     inst2.inst_outputs = inst2_0.inst_outputs /\
     inst2.inst_id = inst2_0.inst_id` by (
    mp_tac (Q.SPECL [`pred_bb.bb_label`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `var_repls`, `target_bb`, `inst2`] target_phi_operands) >>
    simp[]) >>
  (* inst1_0 <> inst2_0 *)
  `inst1_0 <> inst2_0` by (
    spose_not_then strip_assume_tac >>
    gvs[venomInstTheory.instruction_component_equality]) >>
  (* resolve_phi new_lbl on originals = NONE *)
  `resolve_phi (split_block_name pred_bb.bb_label target_bb.bb_label)
     inst2_0.inst_operands = NONE` by (
    CCONTR_TAC >> fs[] >>
    `MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
       (fn_labels func)` by (
      fs[cfgNormBaseTheory.fn_phi_preds_closed_def] >> res_tac) >>
    metis_tac[]) >>
  (* old_lbl <> new_lbl *)
  `pred_bb.bb_label <> split_block_name pred_bb.bb_label
     target_bb.bb_label` by
    simp[cfgNormDefsTheory.split_block_name_def] >>
  (* Case split: 3 meaningful cases *)
  Cases_on `pred_lbl = pred_bb.bb_label` >>
  Cases_on `pred_lbl = split_block_name pred_bb.bb_label
                                         target_bb.bb_label` >>
  rw[]
  >> TRY (
    (* Case old=new: impossible *)
    fs[cfgNormDefsTheory.split_block_name_def] >> NO_TAC)
  >> TRY (
    (* Case pred_lbl = old, <> new *)
    `resolve_phi pred_bb.bb_label
       (update_phi_ops pred_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label) var_repls
         inst2_0.inst_operands) = NONE` by
      metis_tac[resolve_phi_update_phi_ops_old] >>
    fs[] >> NO_TAC)
  >> TRY (
    (* Case pred_lbl <> old, <> new: resolve_phi unchanged *)
    `resolve_phi pred_lbl inst2_0.inst_operands = SOME (Var out)` by (
      `resolve_phi pred_lbl (update_phi_ops pred_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label) var_repls
         inst2_0.inst_operands) =
       resolve_phi pred_lbl inst2_0.inst_operands` by
        metis_tac[cfgNormSimTheory.resolve_phi_update_phi_ops_other] >>
      fs[]) >>
    `MEM out inst1_0.inst_outputs` by fs[] >>
    qpat_x_assum `fn_phis_non_interfering func`
      (ASSUME_TAC o REWRITE_RULE [cfgNormBaseTheory.fn_phis_non_interfering_def]) >>
    qpat_x_assum `!bb' inst1' inst2' out' pred_lbl' v'. _`
      (qspecl_then [`target_bb`, `inst1_0`, `inst2_0`,
        `out`, `pred_lbl`, `out`] mp_tac) >>
    simp[] >> NO_TAC)
  >> (
    (* Case pred_lbl = new, <> old *)
    `resolve_phi pred_bb.bb_label inst2_0.inst_operands <> NONE` by (
      CCONTR_TAC >> fs[] >>
      `resolve_phi (split_block_name pred_bb.bb_label target_bb.bb_label)
         (update_phi_ops pred_bb.bb_label
           (split_block_name pred_bb.bb_label target_bb.bb_label) var_repls
           inst2_0.inst_operands) = NONE` by
        metis_tac[resolve_phi_update_phi_ops_none] >>
      fs[]) >>
    `?val_op. resolve_phi pred_bb.bb_label
       inst2_0.inst_operands = SOME val_op` by
      (Cases_on `resolve_phi pred_bb.bb_label inst2_0.inst_operands` >>
       fs[]) >>
    mp_tac (Q.SPECL [`pred_bb.bb_label`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `var_repls`, `inst2_0.inst_operands`, `val_op`]
      cfgNormSimTheory.resolve_phi_update_phi_ops_match) >>
    (impl_tac >- simp[]) >> strip_tac >> fs[] >>
    Cases_on `val_op` >> fs[] >>
    Cases_on `ALOOKUP var_repls s` >> fs[]
    >- (
      (* ALOOKUP = NONE: s = out, original non-interference *)
      qpat_x_assum `s = out` SUBST_ALL_TAC >>
      qpat_x_assum `fn_phis_non_interfering func`
        (ASSUME_TAC o REWRITE_RULE [cfgNormBaseTheory.fn_phis_non_interfering_def]) >>
      pop_assum (qspecl_then [`target_bb`, `inst1_0`, `inst2_0`,
        `out`, `pred_bb.bb_label`, `out`] mp_tac) >>
      simp[])
    >> (
      (* ALOOKUP = SOME x: x = out, freshness contradiction *)
      qpat_x_assum `x = out` SUBST_ALL_TAC >>
      mp_tac (Q.SPECL [`func`, `target_bb`, `inst1_0`, `out`]
        inst_output_in_fn_all_vars) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
        `split_bb`, `var_repls`, `s`, `out`]
        cfgNormBaseTheory.var_repls_new_not_in_fn_all_vars) >>
      simp[]))
QED

(* C4: PHI non-interference after insert_split *)
Theorem insert_split_phi_non_interfering_inv[local]:
  !func0 func pred_bb target_bb id_base.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    num_succs pred_bb > 1 /\
    LENGTH (block_preds func target_bb.bb_label) > 1 ==>
    fn_phis_non_interfering (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  `MEM pred_bb.bb_label (fn_labels func0)` by (
    imp_res_tac pred_original >> fs[]) >>
  `MEM target_bb.bb_label (fn_labels func0)` by (
    imp_res_tac target_original >> fs[]) >>
  `pred_bb.bb_label <> target_bb.bb_label` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_no_self_loop) >> simp[]) >>
  `~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
        (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_edge_fresh) >> simp[]) >>
  `fn_phis_non_interfering func` by (imp_res_tac cfg_norm_inv_phi_noninterf) >>
  `fn_phi_preds_closed func` by (imp_res_tac cfg_norm_inv_phi_preds) >>
  `?split_bb var_repls. build_split_block pred_bb target_bb id_base =
     (split_bb, var_repls)` by metis_tac[pairTheory.PAIR] >>
  (* fwd var freshness *)
  `!var. ~MEM (STRCAT (STRCAT
      (split_block_name pred_bb.bb_label target_bb.bb_label) "_fwd_") var)
      (fn_all_vars func)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`,
      `target_bb.bb_label`, `var`] cfg_norm_inv_var_fresh) >>
    simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels func)` by
    (imp_res_tac cfg_norm_inv_labels_distinct) >>
  simp[cfgNormBaseTheory.fn_phis_non_interfering_def] >>
  rpt strip_tac >>
  CCONTR_TAC >> fs[] >>
  (* Decompose MEM bb into 4 cases via MEM_insert_split *)
  (SUBGOAL_THEN ``bb = split_bb \/
   (bb = subst_label_terminator target_bb.bb_label
      split_bb.bb_label pred_bb) \/
   (bb = update_phis_for_split pred_bb.bb_label
      split_bb.bb_label var_repls target_bb) \/
   (MEM bb func.fn_blocks /\ bb.bb_label <> pred_bb.bb_label /\
    bb.bb_label <> target_bb.bb_label)``
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))
  >- (mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
        MEM_insert_split) >>
      simp[LET_THM] >> metis_tac[])
  >- (imp_res_tac split_bb_no_phi >> gvs[])
  >- (
    imp_res_tac cfgNormProofTheory.pred_phi_mem_original >>
    qpat_x_assum `fn_phis_non_interfering func`
      (ASSUME_TAC o REWRITE_RULE [cfgNormBaseTheory.fn_phis_non_interfering_def]) >>
    pop_assum (qspecl_then [`pred_bb`, `inst1`, `inst2`,
        `v`, `pred_lbl`, `v`] mp_tac) >>
    simp[])
  >- (
    imp_res_tac cfgNormSimTheory.build_split_block_label >>
    fs[] >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
      `split_bb`, `var_repls`, `inst1`, `inst2`, `v`, `pred_lbl`, `v`]
      phi_non_interfering_target) >>
    simp[])
  >> (
    qpat_x_assum `fn_phis_non_interfering func`
      (ASSUME_TAC o REWRITE_RULE [cfgNormBaseTheory.fn_phis_non_interfering_def]) >>
    pop_assum (qspecl_then [`bb`, `inst1`, `inst2`,
        `v`, `pred_lbl`, `v`] mp_tac) >>
    simp[]))
QED

(* insert_split preserves cfg_norm_inv -- core lemma *)
Theorem insert_split_preserves_inv[local]:
  !func0 func pred_bb target_bb id_base.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    num_succs pred_bb > 1 /\
    LENGTH (block_preds func target_bb.bb_label) > 1 ==>
    cfg_norm_inv func0 (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  (* Derive shared facts *)
  `MEM pred_bb.bb_label (fn_labels func0)` by (
    imp_res_tac pred_original >> fs[]) >>
  `MEM target_bb.bb_label (fn_labels func0)` by (
    imp_res_tac target_original >> fs[]) >>
  `pred_bb.bb_label <> target_bb.bb_label` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
                      `target_bb.bb_label`] cfg_norm_inv_no_self_loop) >>
    simp[]) >>
  `~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
        (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
                      `target_bb.bb_label`] cfg_norm_inv_edge_fresh) >>
    simp[]) >>
  (* Extract non-universal facts from cfg_norm_inv *)
  `wf_function_no_ids func` by (imp_res_tac cfg_norm_inv_wf) >>
  `fn_inst_wf func` by (imp_res_tac cfg_norm_inv_inst_wf) >>
  `fn_phi_preds_closed func` by (imp_res_tac cfg_norm_inv_phi_preds) >>
  `fn_phi_labels_distinct func` by (imp_res_tac cfg_norm_inv_phi_distinct) >>
  `ALL_DISTINCT (fn_labels func)` by (imp_res_tac cfg_norm_inv_labels_distinct) >>
  `fn_succs_closed func` by (
    imp_res_tac cfg_norm_inv_wf >> fs[wf_function_no_ids_def]) >>
  `fn_entry_label func = fn_entry_label func0` by (
    imp_res_tac cfg_norm_inv_entry) >>
  irule cfg_norm_inv_intro >>
  rpt conj_tac >>
  TRY (mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_split_fresh) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    insert_split_wf_no_ids) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    insert_split_phi_labels_distinct) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    insert_split_fn_inst_wf) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_sep_clean) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_fwd_clean) >> simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_no_split_suffix) >> simp[] >> NO_TAC) >>
  TRY (
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
      cfgNormSimTheory.fn_labels_insert_split) >>
    simp[LET_THM] >> pairarg_tac >> fs[] >>
    imp_res_tac cfgNormSimTheory.build_split_block_label >>
    rw[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM] >> rw[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func`, `func0`, `pred_bb`, `target_bb`,
      `id_base`, `lbl`] insert_split_label_origin) >>
    impl_tac >- (
      simp[] >> rpt strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `lbl'`]
        cfg_norm_inv_label_origin) >> simp[]
    ) >> simp[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `p1`, `t1`, `p2`, `t2`]
      cfg_norm_inv_inj) >> simp[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `lbl`, `bb1`, `bb2`] insert_split_unique_pred_inv) >>
    simp[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `bb`] insert_split_block_ids_inv) >>
    simp[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `bb`] insert_split_no_self_loop_inv) >>
    simp[] >> metis_tac[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `bb`] insert_split_nonoriginal_1succ_inv) >>
    simp[] >> NO_TAC) >>
  TRY (
    `func.fn_blocks <> []` by
      fs[wf_function_no_ids_def, venomWfTheory.fn_has_entry_def] >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
      fn_entry_label_insert_split) >> simp[] >> NO_TAC) >>
  TRY (
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
      insert_split_phi_preds_closed) >> simp[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`] insert_split_edge_fresh_inv) >>
    simp[] >> metis_tac[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `pred_lbl`, `tgt_lbl`, `var`] insert_split_fwd_var_inv) >>
    simp[] >> NO_TAC) >>
  TRY (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`] insert_split_phi_non_interfering_inv) >>
    simp[] >> NO_TAC)
QED


(* One round preserves the invariant *)
Theorem cfg_norm_round_preserves_inv[local]:
  !func func0 id_base func' id_base'.
    cfg_norm_inv func0 func /\
    cfg_norm_round func id_base = (func', T, id_base') ==>
    cfg_norm_inv func0 func'
Proof
  rpt gen_tac >> strip_tac >>
  fs[cfg_norm_round_def] >>
  irule find_and_split_preserves >>
  qexistsl_tac [`func.fn_blocks`, `func`, `id_base`, `id_base'`] >>
  simp[listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  irule insert_split_preserves_inv >>
  simp[]
QED

(* Helper: derive fwd var freshness from edge freshness + restricted C11 *)
Theorem fwd_var_fresh_from_edge_fresh[local]:
  !func func0 p t.
    MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
    ~MEM (split_block_name p t) (fn_labels func) /\
    (!pred_lbl tgt_lbl var.
       MEM pred_lbl (fn_labels func0) /\ MEM tgt_lbl (fn_labels func0) /\
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==>
       MEM (split_block_name pred_lbl tgt_lbl) (fn_labels func)) ==>
    !var. ~MEM (STRCAT (STRCAT (split_block_name p t) "_fwd_") var)
              (fn_all_vars func)
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >> res_tac
QED

(* Helper: cfg_norm_inv discharges insert_split_correct preconditions *)
Theorem insert_split_correct_from_inv[local]:
  !func0 func pred_bb target_bb id_base.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label) (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label target_bb.bb_label)
                         "_fwd_") var) (fn_all_vars func)) ==>
    let func' = insert_split func pred_bb target_bb id_base;
        split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label
    in
      !fuel ctx s.
        ~s.vs_halted /\
        s.vs_current_bb <> split_lbl /\
        s.vs_inst_idx = 0 /\
        s.vs_labels = FEMPTY /\
        (s.vs_current_bb = target_bb.bb_label ==>
         s.vs_prev_bb <> SOME pred_bb.bb_label /\
         s.vs_prev_bb <> SOME split_lbl) ==>
        ?fuel'. fuel' >= fuel /\
          result_equiv UNIV (run_blocks fuel ctx func s)
            (run_blocks fuel' ctx func' s)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    cfgNormBaseTheory.insert_split_correct) >>
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  (impl_tac >- (
    imp_res_tac cfg_norm_inv_wf >> imp_res_tac cfg_norm_inv_inst_wf >>
    imp_res_tac cfg_norm_inv_phi_preds >> imp_res_tac cfg_norm_inv_phi_noninterf >>
    imp_res_tac cfg_norm_inv_phi_distinct >> imp_res_tac cfg_norm_inv_labels_distinct >>
    `!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by (
      rpt strip_tac >>
      mp_tac (Q.SPECL [`func0`, `func`, `bb`] cfg_norm_inv_block_ids) >> simp[]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  metis_tac[]
QED

(* find_and_split correctness: scanning the block list and performing
   insert_split preserves semantics via cfg_norm_inv *)
Theorem find_and_split_correct[local]:
  !func0 func id_base bbs func' id_base' s fuel ctx.
    cfg_norm_inv func0 func /\
    EVERY (\bb. MEM bb func.fn_blocks) bbs /\
    fn_entry_label func = SOME s.vs_current_bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_labels = FEMPTY /\
    find_and_split func id_base bbs = (func', T, id_base') ==>
    ?fuel'.
      result_equiv UNIV
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  Induct_on `bbs` >> rpt gen_tac
  >- (strip_tac >> fs[find_and_split_def])
  >- (
  simp[Once find_and_split_def] >>
  strip_tac >>
  `EVERY (\bb. MEM bb func.fn_blocks) bbs` by fs[listTheory.EVERY_DEF] >>
  `MEM h func.fn_blocks` by fs[listTheory.EVERY_DEF] >>
  Cases_on `LENGTH (block_preds func h.bb_label) <= 1` >> fs[]
  >- (
  last_x_assum (qspecl_then [`func0`, `func`, `id_base`, `func'`, `id_base'`,
                               `s`, `fuel`, `ctx`] mp_tac) >>
  simp[])
  >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds func h.bb_label)` >> fs[]
  >- (
  last_x_assum (qspecl_then [`func0`, `func`, `id_base`, `func'`, `id_base'`,
                               `s`, `fuel`, `ctx`] mp_tac) >>
  simp[])
  >>
  rename1 `FIND _ _ = SOME pred_bb` >>
  `MEM pred_bb (block_preds func h.bb_label)` by
    (imp_res_tac venomExecPropsTheory.FIND_MEM) >>
  `MEM pred_bb func.fn_blocks /\ MEM h.bb_label (bb_succs pred_bb)` by
    (fs[cfgTransformTheory.block_preds_def, listTheory.MEM_FILTER]) >>
  `pred_bb.bb_label <> h.bb_label` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `h.bb_label`]
      cfg_norm_inv_no_self_loop) >> simp[] >> metis_tac[]) >>
  `num_succs pred_bb > 1` by (
    imp_res_tac venomExecPropsTheory.FIND_P >> fs[]) >>
  `~MEM (split_block_name pred_bb.bb_label h.bb_label) (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `h.bb_label`]
      cfg_norm_inv_edge_fresh) >> simp[]) >>
  `MEM pred_bb.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`] pred_original) >> simp[]) >>
  `MEM h.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `h`] target_original) >> simp[]) >>
  `!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label h.bb_label) "_fwd_") var)
              (fn_all_vars func)` by (
    rpt strip_tac >> CCONTR_TAC >> fs[] >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`, `h.bb_label`, `var`]
      cfg_norm_inv_var_fresh) >> simp[]) >>
  (* Apply insert_split_correct via cfg_norm_inv helper *)
  `MEM s.vs_current_bb (fn_labels func)` by (
    imp_res_tac cfg_norm_inv_wf >> imp_res_tac entry_in_fn_labels >> simp[]) >>
  `s.vs_current_bb <> split_block_name pred_bb.bb_label h.bb_label` by
    (imp_res_tac MEM_not_MEM_neq >> simp[]) >>
  mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `h`, `id_base`]
    insert_split_correct_from_inv) >>
  simp[LET_THM] >> DISCH_TAC >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `fuel'` >> simp[])
QED

(* One round preserves semantics *)
Theorem cfg_norm_round_correct[local]:
  !func func0 id_base func' id_base' s fuel ctx.
    cfg_norm_inv func0 func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_labels = FEMPTY /\
    cfg_norm_round func id_base = (func', T, id_base') ==>
    ?fuel'.
      result_equiv UNIV
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  rpt strip_tac >>
  fs[cfg_norm_round_def] >>
  mp_tac (Q.SPECL [`func0`, `func`, `id_base`, `func.fn_blocks`, `func'`,
    `id_base'`, `s`, `fuel`, `ctx`] find_and_split_correct) >>
  simp[listTheory.EVERY_MEM]
QED


(* find_and_split preserves entry label *)
Theorem find_and_split_preserves_entry[local]:
  !func id_base bbs func' changed id_base'.
    func.fn_blocks <> [] /\
    find_and_split func id_base bbs = (func', changed, id_base') ==>
    fn_entry_label func' = fn_entry_label func
Proof
  Induct_on `bbs` >>
  rw[find_and_split_def, LET_THM] >>
  BasicProvers.every_case_tac >> fs[] >>
  metis_tac[fn_entry_label_insert_split]
QED

(* One round preserves entry label *)
Theorem cfg_norm_round_preserves_entry[local]:
  !func id_base func' changed id_base'.
    cfg_norm_round func id_base = (func', changed, id_base') ==>
    fn_entry_label func' = fn_entry_label func
Proof
  rw[cfg_norm_round_def] >>
  Cases_on `func.fn_blocks` >-
  fs[find_and_split_def] >>
  mp_tac (Q.SPECL [`func`, `id_base`, `func.fn_blocks`, `func'`,
    `changed`, `id_base'`] find_and_split_preserves_entry) >>
  simp[]
QED



(* ================================================================
   Section 7: cfg_norm_iter correctness -- iteration preserves semantics
   ================================================================ *)

Theorem cfg_norm_iter_preserves_entry[local]:
  !n func id_base.
    fn_entry_label (cfg_norm_iter n func id_base) = fn_entry_label func
Proof
  Induct_on `n` >> rw[cfg_norm_iter_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  Cases_on `changed` >> fs[] >>
  imp_res_tac cfg_norm_round_preserves_entry >> simp[]
QED

Theorem cfg_norm_iter_correct[local]:
  !n func func0 id_base s fuel ctx.
    cfg_norm_inv func0 func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_labels = FEMPTY ==>
    let func' = cfg_norm_iter n func id_base in
    ?fuel'.
      result_equiv UNIV
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  Induct_on `n` >>
  rw[cfg_norm_iter_def, LET_THM] >-
  (qexists_tac `fuel` >> simp[result_equiv_UNIV_refl]) >>
  pairarg_tac >> fs[] >>
  Cases_on `changed` >> fs[] >-
  ((* changed = T: one round happened, then iterate *)
   rename1 `cfg_norm_round func id_base = (func1, T, id_base1)` >>
   (* Step 1: one round preserves semantics *)
   `?fuel1. result_equiv UNIV
      (run_blocks fuel ctx func s)
      (run_blocks fuel1 ctx func1 s)` by
     (mp_tac (Q.SPECL [`func`, `func0`, `id_base`, `func1`,
        `id_base1`, `s`, `fuel`, `ctx`] cfg_norm_round_correct) >>
      simp[]) >>
   (* Step 2: one round preserves invariant *)
   `cfg_norm_inv func0 func1` by
     (mp_tac (Q.SPECL [`func`, `func0`, `id_base`, `func1`, `id_base1`]
        cfg_norm_round_preserves_inv) >>
      simp[]) >>
   (* Step 3: entry label preserved *)
   `fn_entry_label func1 = fn_entry_label func` by
     (mp_tac (Q.SPECL [`func`, `id_base`, `func1`, `T`, `id_base1`]
        cfg_norm_round_preserves_entry) >>
      simp[cfg_norm_round_def]) >>
   (* Step 4: IH gives iteration correctness *)
   `?fuel2. result_equiv UNIV
      (run_blocks fuel1 ctx func1 s)
      (run_blocks fuel2 ctx (cfg_norm_iter n func1 id_base1) s)` by
     (first_x_assum (qspecl_then [`func1`, `func0`, `id_base1`, `s`,
        `fuel1`, `ctx`] mp_tac) >> simp[]) >>
   (* Step 5: transitivity *)
   qexists_tac `fuel2` >>
   mp_tac (Q.SPECL [`run_blocks fuel ctx func s`,
     `run_blocks fuel1 ctx func1 s`,
     `run_blocks fuel2 ctx (cfg_norm_iter n func1 id_base1) s`]
     result_equiv_UNIV_trans) >>
   simp[]) >>
  (* changed = F: no change *)
  qexists_tac `fuel` >> simp[result_equiv_UNIV_refl]
QED

(* ================================================================
   Section 8: Main theorem
   ================================================================ *)

(* Added preconditions:
   - execution starts at entry block (justified: Venom pipeline)
   - prev_bb = NONE (justified: initial state)
   - no self-loop critical edges (justified: Venom generates acyclic blocks)
   - no "_split_" in labels (justified: Venom labels are "global", "bb0", etc) *)

Theorem cfg_norm_inv_initial[local]:
  !func.
    wf_function func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    (!bb lbl. MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
       ~MEM (split_block_name bb.bb_label lbl) (fn_labels func)) /\
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==> F) /\
    split_labels_fresh split_block_name func /\
    (!p1 t1 p2 t2.
       MEM p1 (fn_labels func) /\ MEM t1 (fn_labels func) /\
       MEM p2 (fn_labels func) /\ MEM t2 (fn_labels func) /\
       split_block_name p1 t1 = split_block_name p2 t2 ==>
       p1 = p2 /\ t1 = t2) /\
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    (!L. MEM L (fn_labels func) ==> TAKE 6 L <> "split_") /\
    (!L. MEM L (fn_labels func) ==> !a b. L <> STRCAT a (STRCAT "_fwd" b)) /\
    (!L. MEM L (fn_labels func) ==> !x. L <> STRCAT x "_split") ==>
    cfg_norm_inv func func
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels func)` by fs[wf_function_def] >>
  `fn_succs_closed func` by fs[wf_function_def] >>
  `wf_function_no_ids func` by (imp_res_tac wf_function_imp_no_ids) >>
  `!bb. MEM bb func.fn_blocks ==>
     ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (rpt strip_tac >> imp_res_tac wf_function_block_inst_ids_distinct) >>
  irule cfg_norm_inv_intro >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> imp_res_tac mem_block_mem_fn_labels >>
  TRY (fs[] >> NO_TAC) >>
  fs[fn_succs_closed_def] >> res_tac
QED

Theorem cfg_norm_fn_correct:
  !func s fuel ctx.
    wf_function func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==> F) /\
    split_labels_fresh split_block_name func /\
    (* split_block_name injective on original labels *)
    (!p1 t1 p2 t2.
       MEM p1 (fn_labels func) /\ MEM t1 (fn_labels func) /\
       MEM p2 (fn_labels func) /\ MEM t2 (fn_labels func) /\
       split_block_name p1 t1 = split_block_name p2 t2 ==>
       p1 = p2 /\ t1 = t2) /\
    (* No self-loop critical edges *)
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    (* No original label starts with "split_" *)
    (!L. MEM L (fn_labels func) ==> TAKE 6 L <> "split_") /\
    (* No original label contains "_fwd" (4-char) substring *)
    (!L. MEM L (fn_labels func) ==> !a b. L <> STRCAT a (STRCAT "_fwd" b)) /\
    (* No original label ends with "_split" *)
    (!L. MEM L (fn_labels func) ==> !x. L <> STRCAT x "_split") /\
    fn_entry_label func = SOME s.vs_current_bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_labels = FEMPTY ==>
    let func' = cfg_norm_fn func in
    ?fresh fuel'.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  rpt strip_tac >>
  simp[LET_THM] >>
  qexists_tac `UNIV` >>
  `ALL_DISTINCT (fn_labels func)` by fs[wf_function_def] >>
  `!bb lbl. MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
     ~MEM (split_block_name bb.bb_label lbl) (fn_labels func)` by
    fs[venomWfTheory.split_labels_fresh_def] >>
  mp_tac (Q.SPEC `func` cfg_norm_inv_initial) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  mp_tac (Q.SPECL [`2 * LENGTH func.fn_blocks`, `func`, `func`,
    `0`, `s`, `fuel`, `ctx`] cfg_norm_iter_correct) >>
  simp[cfg_norm_fn_def, LET_THM] >>
  strip_tac >>
  (* Bridge: unfold run_function to run_blocks *)
  `fn_entry_label (cfg_norm_iter (2 * LENGTH func.fn_blocks) func 0) =
   fn_entry_label func`
    by simp[cfg_norm_iter_preserves_entry] >>
  qexists_tac `fuel'` >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[cfg_norm_fn_def, LET_THM] >>
  `s with <|vs_current_bb := s.vs_current_bb; vs_inst_idx := 0|> = s`
    by simp[venomStateTheory.venom_state_component_equality] >>
  gvs[]
QED
