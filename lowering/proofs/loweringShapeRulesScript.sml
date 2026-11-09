(*
 * Rules for the shape judgment of the raw lowering (S2 of #626).
 *
 * Hoare-style rules for shape_step (loweringShapeDefs): one per way of
 * composing compile actions and one per monad primitive that appends code.
 * The proofs of the generators in loweringShapeProps are built from them.
 *
 * TOP-LEVEL:
 *   shape_step_* rules           — composition and monad primitives
 *   *_append_ok                  — appending one instruction keeps the
 *                                  invariant, by operand kind
 *   opaque_insts_ok_opaque_use_ok — the invariant gives opaque_use_ok
 *   label_sfx_distinct            — fresh labels with different suffixes
 *                                  differ
 *)
Theory loweringShapeRules
Ancestors
  list rich_list compileEnv loweringStateRelDefs emitHelper emitHelperProps fragExec venomInst
  unitShapeDefs loweringShapeDefs context
Libs
  monadsyntax dep_rewrite

(* ===== Composition rules ===== *)

Theorem shape_step_bind:
  !internal LP P m f Q R.
    shape_step internal LP P m Q /\
    (!x. shape_step internal LP (Q x) (f x) R) ==>
    shape_step internal LP P (comp_bind m f) R
Proof
  rw[shape_step_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[shape_extends_trans]
QED

Theorem shape_step_ignore_bind:
  !internal LP P m f Q R.
    shape_step internal LP P m Q /\
    (!x. shape_step internal LP (Q x) f R) ==>
    shape_step internal LP P (comp_ignore_bind m f) R
Proof
  rw[comp_ignore_bind_def] >> irule shape_step_bind >> metis_tac[]
QED

Theorem shape_step_return:
  !internal LP P Q x.
    (!st. P st ==> Q x st) ==>
    shape_step internal LP P (comp_return x) Q
Proof
  rw[shape_step_def, comp_return_def, shape_extends_refl]
QED

Theorem shape_extends_LP_mono:
  !internal LP LP' st st'.
    shape_extends internal LP st st' /\ (!l. LP l ==> LP' l) ==>
    shape_extends internal LP' st st'
Proof
  rw[shape_extends_def, EVERY_MEM]
QED

Theorem shape_step_conseq:
  !internal LP LP' P P' m Q Q'.
    shape_step internal LP P m Q /\ (!st. P' st ==> P st) /\
    (!x st. Q x st ==> Q' x st) /\ (!l. LP l ==> LP' l) ==>
    shape_step internal LP' P' m Q'
Proof
  rw[shape_step_def] >> `P st` by res_tac >>
  qpat_x_assum `!st x st'. _` drule_all >> strip_tac >>
  metis_tac[shape_extends_LP_mono]
QED

Theorem shape_step_comp_get:
  !internal LP P.
    shape_step internal LP P comp_get (\x st'. x = st' /\ P st')
Proof
  rw[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem shape_stable_conj:
  !R R'. shape_stable R /\ shape_stable R' ==>
         shape_stable (\st. R st /\ R' st)
Proof
  rw[shape_stable_def] >> metis_tac[]
QED

Theorem shape_stable_plain_operands:
  !ops. shape_stable (\st. EVERY (plain_operand st) ops)
Proof
  rw[shape_stable_def, EVERY_MEM] >> metis_tac[plain_operand_mono]
QED

Theorem shape_stable_label_or_plains:
  !ops. shape_stable (\st. EVERY (label_or_plain st) ops)
Proof
  rw[shape_stable_def, EVERY_MEM] >> metis_tac[label_or_plain_mono]
QED

Theorem shape_step_frame:
  !internal LP P m Q R.
    shape_step internal LP P m Q /\ shape_stable R ==>
    shape_step internal LP (\st. R st /\ P st) m (\x st. R st /\ Q x st)
Proof
  rw[shape_step_def, shape_stable_def] >> metis_tac[]
QED

(* Base-state algebra for the unchecked interval of a call template. *)
Theorem shape_base_step_bind:
  !internal LP P m f Q R.
    shape_base_step internal LP P m Q /\
    (!x. shape_base_step internal LP (Q x) (f x) R) ==>
    shape_base_step internal LP P (comp_bind m f) R
Proof
  rw[shape_base_step_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[shape_extends_trans]
QED

Theorem shape_base_step_ignore_bind:
  !internal LP P m f Q R.
    shape_base_step internal LP P m Q /\
    (!x. shape_base_step internal LP (Q x) f R) ==>
    shape_base_step internal LP P (comp_ignore_bind m f) R
Proof
  rw[comp_ignore_bind_def] >> irule shape_base_step_bind >> metis_tac[]
QED

Theorem shape_base_step_return:
  !internal LP P Q x.
    (!st. P st ==> Q x st) ==>
    shape_base_step internal LP P (comp_return x) Q
Proof
  rw[shape_base_step_def, comp_return_def, shape_extends_refl]
QED

Theorem shape_base_step_conseq:
  !internal LP LP' P P' m Q Q'.
    shape_base_step internal LP P m Q /\ (!st. P' st ==> P st) /\
    (!x st. Q x st ==> Q' x st) /\ (!l. LP l ==> LP' l) ==>
    shape_base_step internal LP' P' m Q'
Proof
  rw[shape_base_step_def] >> `P st` by res_tac >>
  qpat_x_assum `!st x st'. _` drule_all >> strip_tac >>
  metis_tac[shape_extends_LP_mono]
QED

Theorem shape_base_step_frame:
  !internal LP P m Q R.
    shape_base_step internal LP P m Q /\ shape_stable R ==>
    shape_base_step internal LP (\st. R st /\ P st) m (\x st. R st /\ Q x st)
Proof
  rw[shape_base_step_def, shape_stable_def] >> metis_tac[]
QED

(* ===== Monad primitives ===== *)

Theorem shape_extends_same_code:
  !internal LP st st'.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts /\
    st.cs_next_var <= st'.cs_next_var ==>
    shape_extends internal LP st st'
Proof
  rpt strip_tac >>
  `state_insts st' = state_insts st /\ all_blocks st' = all_blocks st`
    by gs[state_insts_def, all_blocks_def] >>
  `cs_extends st st'` by (irule cs_extends_same_block >> gs[]) >>
  gs[shape_extends_def, added_insts_def, added_labels_def, DROP_LENGTH_NIL,
     DROP_LENGTH_TOO_LONG]
QED

Theorem shape_state_same_code:
  !st st'.
    shape_state st /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts /\
    st.cs_next_var <= st'.cs_next_var ==>
    shape_state st'
Proof
  rpt strip_tac >>
  `state_insts st' = state_insts st`
    by gs[state_insts_def, all_blocks_def] >>
  `all_blocks st' = all_blocks st` by simp[all_blocks_def] >>
  `raw_checked_state st'` by
    gvs[raw_checked_state_def, all_blocks_def, shape_state_def] >>
  gs[shape_state_def, shape_base_state_def] >> metis_tac[not_fresh_at_mono]
QED

(* The output of emit_op / fresh_var is a new compiler variable. *)
Theorem fresh_output_props:
  !st st'. st'.cs_next_var = st.cs_next_var + 1 ==>
    ~not_fresh_at st (STRING #"%" (toString st.cs_next_var)) /\
    not_fresh_at st' (STRING #"%" (toString st.cs_next_var))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL])
  >> rw[not_fresh_at_def] >> irule fresh_var_distinct >> gs[]
QED

Theorem shape_step_fresh_var:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R fresh_var
      (\x st'. R st' /\ plain_operand st' (Var x))
Proof
  simp[shape_step_def, fresh_var_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  `st1.cs_next_var = st.cs_next_var + 1` by simp[Abbr `st1`] >>
  drule fresh_output_props >> strip_tac >>
  `state_insts st1 = state_insts st`
    by simp[Abbr `st1`, state_insts_def, all_blocks_def] >>
  `R st1` by metis_tac[shape_stable_def] >>
  gs[plain_operand_def, stackPlanTypesTheory.is_label_operand_def, shape_state_def, shape_base_state_def,
     opaque_out_def] >>
  metis_tac[]
QED

Theorem shape_step_fresh_id:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R fresh_id (\x st'. R st')
Proof
  simp[shape_step_def, fresh_id_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_step_fresh_label:
  !internal LP R sfx.
    shape_stable R ==>
    shape_step internal LP R (fresh_label sfx)
      (\l st'. R st' /\ compiler_label l)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >> gvs[fresh_label_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  simp[compiler_label_def, fresh_label_output_in_future] >>
  metis_tac[shape_stable_def]
QED

Theorem shape_step_fresh_label_sfx:
  !internal LP R sfx.
    shape_stable R ==>
    shape_step internal LP R (fresh_label sfx)
      (\l st'. R st' /\ compiler_label l /\ label_sfx sfx l)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >> gvs[fresh_label_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  simp[compiler_label_def, fresh_label_output_in_future, label_sfx_def] >>
  metis_tac[shape_stable_def]
QED

Theorem label_sfx_distinct:
  label_sfx s1 l1 /\ label_sfx s2 l2 /\ s1 <> s2 ==> l1 <> l2
Proof
  rw[label_sfx_def] >> metis_tac[fresh_label_output_inj]
QED

Theorem DROP_LENGTH_MAP_APPEND[local]:
  !f l m. DROP (LENGTH l) (MAP f l ++ m) = m
Proof
  rpt gen_tac >>
  `LENGTH l = LENGTH (MAP f l)` by simp[] >>
  pop_assum SUBST1_TAC >> simp[DROP_LENGTH_APPEND]
QED

(* The labels steps may start are never internal entry labels. *)
Theorem compiler_label_not_internal[simp]:
  !l. compiler_label l ==> ~internal_label_ok l
Proof
  rw[compiler_label_def, compiler_labels_future_def, fresh_label_output_def,
     internal_label_ok_def] >> simp[TypeBase.case_def_of ``:string``]
QED

Theorem jump_label_ok_not_internal[simp]:
  !l. jump_label_ok l ==> ~internal_label_ok l
Proof
  rw[jump_label_ok_def] >- metis_tac[compiler_label_not_internal] >>
  Cases_on `l` >>
  gvs[internal_label_ok_def, IS_PREFIX_APPEND, TypeBase.case_def_of ``:string``]
QED

Theorem rets_scoped_append_empty:
  !bbs lbl. rets_scoped bbs ==>
    rets_scoped (bbs ++ [<| bb_label := lbl; bb_instructions := [] |>])
Proof
  rw[rets_scoped_def] >>
  Cases_on `post` using SNOC_CASES >>
  gvs[SNOC_APPEND, APPEND_ASSOC] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem shape_step_new_block:
  !internal LP R lbl.
    shape_stable R /\ LP lbl /\ ~internal_label_ok lbl ==>
    shape_step internal LP R (new_block lbl) (\x st'. R st')
Proof
  simp[shape_step_def, new_block_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `new_block lbl st = (st.cs_current_bb, st1)`
    by simp[new_block_def, Abbr `st1`] >>
  drule cs_extends_new_block >> strip_tac >>
  `all_blocks st1 =
     all_blocks st ++ [<| bb_label := lbl; bb_instructions := [] |>]`
    by simp[Abbr `st1`, all_blocks_def] >>
  `st1.cs_next_var = st.cs_next_var` by simp[Abbr `st1`] >>
  `state_insts st1 = state_insts st` by gs[state_insts_def] >>
  `added_labels st st1 = [lbl]`
    by gs[added_labels_def, DROP_LENGTH_MAP_APPEND] >>
  `added_insts st st1 = []` by gs[added_insts_def, DROP_LENGTH_NIL] >>
  `shape_extends internal LP st st1` by gs[shape_extends_def] >>
  `raw_checked_state st1` by
    (irule raw_checked_state_cs_extends >> qexists_tac `st` >>
     gvs[shape_state_def]) >>
  `shape_state st1`
    by (gs[shape_state_def, shape_base_state_def] >>
        conj_tac >- (irule rets_scoped_append_empty >> simp[]) >>
        metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_REFL]) >>
  metis_tac[shape_stable_def]
QED

Theorem opaque_out_snoc:
  !opc insts inst x.
    opaque_out opc (insts ++ [inst]) x <=>
    opaque_out opc insts x \/ (inst.inst_opcode = opc /\ MEM x inst.inst_outputs)
Proof
  rw[opaque_out_def] >> metis_tac[]
QED

Theorem opaque_insts_ok_snoc:
  !st st' insts inst.
    opaque_insts_ok insts /\
    (!i x. MEM i insts /\ MEM (Var x) i.inst_operands ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out RETPC_PARAM (insts ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front. inst.inst_operands = front ++ [Var x] /\
                  ~MEM (Var x) front)) ==>
    opaque_insts_ok (insts ++ [inst])
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once opaque_insts_ok_def] >> qx_genl_tac [`i`, `y`] >> strip_tac
  >- (`not_fresh_at st y` by metis_tac[] >>
      `MEM y inst.inst_outputs ==>
       inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM`
        by (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      qpat_x_assum `opaque_insts_ok _`
        (qspecl_then [`i`, `y`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
      Cases_on `MEM y inst.inst_outputs` >> gvs[opaque_out_snoc])
  >> gvs[] >>
  qpat_x_assum `!x. MEM (Var x) inst.inst_operands ==> _`
    (qspec_then `y` mp_tac) >>
  simp[]
QED

Theorem operands_not_fresh_snoc[local]:
  !st st' insts inst.
    st.cs_next_var <= st'.cs_next_var /\
    (!i x. MEM i insts /\ MEM (Var x) i.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) ==>
    !i x. MEM i (insts ++ [inst]) /\ MEM (Var x) i.inst_operands ==>
          not_fresh_at st' x
Proof
  rw[] >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[] >>
  metis_tac[]
QED

Theorem outputs_not_fresh_snoc[local]:
  !st st' insts inst.
    st.cs_next_var <= st'.cs_next_var /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> not_fresh_at st x) /\
    (!x. MEM x inst.inst_outputs ==> not_fresh_at st' x) ==>
    !i x. MEM i (insts ++ [inst]) /\ MEM x i.inst_outputs ==>
          not_fresh_at st' x
Proof
  rw[] >> metis_tac[not_fresh_at_mono]
QED

(* Only RETPC_PARAM writes a return-PC variable. *)
Theorem retpc_outputs_snoc[local]:
  !st insts inst.
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> not_fresh_at st x) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\
           opaque_out RETPC_PARAM insts x ==> i.inst_opcode = RETPC_PARAM) /\
    (inst.inst_opcode = RETPC_PARAM ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x) /\
    (!x. MEM x inst.inst_outputs /\ not_fresh_at st x ==>
         ~opaque_out RETPC_PARAM insts x) ==>
    !i x. MEM i (insts ++ [inst]) /\ MEM x i.inst_outputs /\
          opaque_out RETPC_PARAM (insts ++ [inst]) x ==>
          i.inst_opcode = RETPC_PARAM
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[opaque_out_snoc] >> strip_tac >> gvs[] >>
  metis_tac[opaque_out_def]
QED

(* A RETPC_PARAM output has no other writer. *)
Theorem retpc_writer_unique_snoc[local]:
  !st insts inst.
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==> not_fresh_at st x) /\
    (!i j x. MEM i insts /\ MEM j insts /\ i.inst_opcode = RETPC_PARAM /\
             MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j) /\
    (inst.inst_opcode = RETPC_PARAM ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x) /\
    (!x. MEM x inst.inst_outputs /\ not_fresh_at st x ==>
         ~opaque_out RETPC_PARAM insts x) ==>
    !i j x. MEM i (insts ++ [inst]) /\ MEM j (insts ++ [inst]) /\
            i.inst_opcode = RETPC_PARAM /\
            MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  rw[] >> gvs[] >> metis_tac[opaque_out_def]
QED

Theorem rets_scoped_append_inst:
  !bbs bb inst.
    rets_scoped (bbs ++ [bb]) /\
    (inst.inst_opcode = RET ==>
      ?front x. inst.inst_operands = front ++ [Var x] /\
        opaque_out RETPC_PARAM (fn_entry_insts (bbs ++ [bb])) x) ==>
    rets_scoped (bbs ++ [bb with bb_instructions := bb.bb_instructions ++ [inst]])
Proof
  rw[rets_scoped_def] >>
  Cases_on `post` using SNOC_CASES >>
  gvs[SNOC_APPEND, APPEND_ASSOC] >-
    (rename1 `MEM ret bb.bb_instructions` >>
     qpat_x_assum `!pre' bb'' post inst''. _`
       (qspecl_then [`bbs`, `bb`, `[]`, `ret`] mp_tac) >>
     simp[] >> strip_tac >>
     qexistsl_tac [`front`, `x`] >> simp[] >>
     fs[opaque_out_def] >>
     rename1 `MEM seed (fn_entry_insts _)` >>
     qexists_tac `seed` >> simp[] >>
     irule fn_entry_insts_last_update >> goal_assum (drule_at Any) >> simp[]) >>
  fs[opaque_out_def] >>
  rename1 `MEM seed (fn_entry_insts _)` >>
  qexists_tac `seed` >> simp[] >>
  irule fn_entry_insts_last_update >> goal_assum (drule_at Any) >> simp[]
QED

(* Appending one instruction to the open block. *)
Theorem shape_base_append_inst:
  !internal LP st st' inst.
    shape_base_state st /\ lowered_inst_ok internal inst /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    st.cs_next_var <= st'.cs_next_var /\
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) /\
    (!x. MEM x inst.inst_outputs ==>
       not_fresh_at st' x /\
       (not_fresh_at st x ==> ~opaque_out RETPC_PARAM (state_insts st) x)) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front. inst.inst_operands = front ++ [Var x] /\
                  ~MEM (Var x) front)) /\
    (inst.inst_opcode = RET ==>
       ?front x. inst.inst_operands = front ++ [Var x] /\
                 opaque_out RETPC_PARAM (cur_entry_insts st) x) ==>
    shape_extends internal LP st st' /\ shape_base_state st'
Proof
  rpt gen_tac >> strip_tac >>
  `state_insts st' = state_insts st ++ [inst]`
    by gs[state_insts_def, all_blocks_def] >>
  `added_insts st st' = [inst]`
    by gs[added_insts_def, DROP_LENGTH_APPEND] >>
  `added_labels st st' = []`
    by gs[added_labels_def, all_blocks_def, DROP_LENGTH_TOO_LONG] >>
  `cs_extends st st'` by (irule cs_extends_same_block >> gs[]) >>
  qpat_x_assum `shape_base_state st`
    (strip_assume_tac o REWRITE_RULE [shape_base_state_def]) >>
  conj_tac
  >- (simp[shape_extends_def] >>
      qpat_assum `added_insts _ _ = _` (fn th => simp[th]) >>
      qpat_assum `added_labels _ _ = _` (fn th => simp[th]) >>
      rpt strip_tac >> gs[]) >>
  REWRITE_TAC [shape_state_def, shape_base_state_def] >>
  qpat_assum `state_insts st' = _` (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac
  >- (match_mp_tac (Q.SPECL [`st`, `st'`] opaque_insts_ok_snoc) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (`rets_scoped (REVERSE st.cs_blocks ++
          [<|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++ [inst]|>])`
        suffices_by simp[all_blocks_def] >>
      qspecl_then [`REVERSE st.cs_blocks`,
        `<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>`,
        `inst`] mp_tac rets_scoped_append_inst >>
      fs[all_blocks_def, cur_entry_insts_def])
  >- (match_mp_tac (Q.SPECL [`st`, `st'`] operands_not_fresh_snoc) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (match_mp_tac (Q.SPECL [`st`, `st'`] outputs_not_fresh_snoc) >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      metis_tac[])
  >- (match_mp_tac (Q.SPECL [`st`] retpc_outputs_snoc) >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
      >- (strip_tac >>
          qpat_x_assum `MEM inst.inst_opcode [GAS; RETPC_PARAM] ==> _` mp_tac >>
          simp[])
      >> metis_tac[])
  >> match_mp_tac (Q.SPECL [`st`] retpc_writer_unique_snoc) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (strip_tac >>
      qpat_x_assum `MEM inst.inst_opcode [GAS; RETPC_PARAM] ==> _` mp_tac >>
      simp[])
  >> metis_tac[]
QED

Theorem shape_append_inst:
  !internal LP st st' inst.
    shape_state st /\ lowered_inst_ok internal inst /\
    ~MEM inst.inst_opcode [CALL; STATICCALL] /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    st.cs_next_var <= st'.cs_next_var /\
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) /\
    (!x. MEM x inst.inst_outputs ==>
       not_fresh_at st' x /\
       (not_fresh_at st x ==> ~opaque_out RETPC_PARAM (state_insts st) x)) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front. inst.inst_operands = front ++ [Var x] /\
                  ~MEM (Var x) front)) /\
    (inst.inst_opcode = RET ==>
       ?front x. inst.inst_operands = front ++ [Var x] /\
                 opaque_out RETPC_PARAM (cur_entry_insts st) x) ==>
    shape_extends internal LP st st' /\ shape_state st'
Proof
  rpt gen_tac >> strip_tac >>
  `shape_base_state st` by gvs[shape_state_def] >>
  drule_all shape_base_append_inst >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  `state_insts st' = state_insts st ++ [inst]` by
    gvs[state_insts_def, all_blocks_def] >>
  `added_insts st st' = [inst]` by
    gvs[added_insts_def, DROP_LENGTH_APPEND] >>
  simp[shape_state_def] >>
  irule raw_checked_state_cs_extends >> qexists_tac `st` >>
  gvs[shape_extends_def, shape_state_def]
QED

(* Outputs that are plain variables already. *)
Theorem plain_outputs_ok:
  !st st' outs.
    st.cs_next_var <= st'.cs_next_var /\
    EVERY (plain_operand st) (MAP Var outs) ==>
    !x. MEM x outs ==>
        not_fresh_at st' x /\
        (not_fresh_at st x ==> ~opaque_out RETPC_PARAM (state_insts st) x)
Proof
  rw[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> first_x_assum drule >>
  rw[plain_operand_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem plain_operand_not_opaque:
  !st op x. plain_operand st op /\ op = Var x ==>
    not_fresh_at st x /\
    ~opaque_out RETPC_PARAM (state_insts st) x
Proof
  rw[plain_operand_def]
QED

(* Operands that are labels or plain, appended by a non-opaque opcode. *)
Theorem plain_append_ok:
  !st inst.
    EVERY (label_or_plain st) inst.inst_operands /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
         ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)
Proof
  rpt gen_tac >> strip_tac >> simp[opaque_out_snoc] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> res_tac >>
  gvs[label_or_plain_def, plain_operand_def,
      stackPlanTypesTheory.is_label_operand_def]
QED

(* A call whose head operand may be a GAS value. *)
Theorem call_append_ok:
  !st g rest inst.
    MEM inst.inst_opcode [CALL; STATICCALL] /\
    inst.inst_operands = g :: rest /\
    (gas_operand st g \/ plain_operand st g) /\
    EVERY (plain_operand st) rest ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `!x. MEM (Var x) rest ==>
       not_fresh_at st x /\
       ~opaque_out RETPC_PARAM (state_insts st) x`
    by (gvs[EVERY_MEM] >> metis_tac[plain_operand_not_opaque]) >>
  `!x. g = Var x ==>
       not_fresh_at st x /\ ~opaque_out RETPC_PARAM (state_insts st) x`
    by (rw[] >> gvs[gas_operand_def, plain_operand_def] >> metis_tac[]) >>
  simp[opaque_out_snoc] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A RET whose last operand may be the return PC. *)
Theorem ret_append_ok:
  !st front r inst.
    inst.inst_opcode = RET /\ inst.inst_operands = front ++ [r] /\
    retpc_operand st r /\
    EVERY (plain_operand st) front ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front'. inst.inst_operands = front' ++ [Var x] /\
                   ~MEM (Var x) front'))
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM (Var x) front ==>
       not_fresh_at st x /\
       ~opaque_out RETPC_PARAM (state_insts st) x`
    by (gvs[EVERY_MEM] >> metis_tac[plain_operand_not_opaque]) >>
  `!x. r = Var x ==> not_fresh_at st x`
    by (rw[] >> gvs[retpc_operand_def, plain_operand_def] >> metis_tac[]) >>
  simp[opaque_out_snoc] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A fresh output of a non-opaque instruction is plain. *)
Theorem fresh_out_plain:
  !st st1 inst out.
    shape_base_state st /\ ~not_fresh_at st out /\ not_fresh_at st1 out /\
    state_insts st1 = state_insts st ++ [inst] /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM ==>
    plain_operand st1 (Var out)
Proof
  rpt gen_tac >> strip_tac >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       opaque_out_snoc] >>
  gvs[shape_state_def, shape_base_state_def, opaque_out_def] >> metis_tac[]
QED

(* A fresh output of GAS or RETPC_PARAM is opaque of exactly that kind. *)
Theorem fresh_out_opaque:
  !st st1 inst out.
    shape_state st /\ ~not_fresh_at st out /\
    state_insts st1 = state_insts st ++ [inst] /\
    MEM out inst.inst_outputs ==>
    opaque_out inst.inst_opcode (state_insts st1) out /\
    (!opc. MEM opc [GAS; RETPC_PARAM] /\ opc <> inst.inst_opcode ==>
           ~opaque_out opc (state_insts st1) out)
Proof
  rpt gen_tac >> strip_tac >> simp[opaque_out_snoc] >>
  rpt strip_tac >> gvs[shape_state_def, shape_base_state_def, opaque_out_def] >> metis_tac[]
QED

Theorem shape_step_emit:
  !internal LP R inst.
    shape_stable R /\ lowered_inst_ok internal inst /\
    ~MEM inst.inst_opcode [GAS; RETPC_PARAM; RET; CALL; STATICCALL] ==>
    shape_step internal LP
      (\st. R st /\ EVERY (label_or_plain st) inst.inst_operands /\
            EVERY (plain_operand st) (MAP Var inst.inst_outputs))
      (emit inst) (\x st'. R st')
Proof
  simp[shape_step_def, emit_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  qspecl_then [`st`, `st1`, `inst.inst_outputs`] mp_tac plain_outputs_ok >>
  (impl_tac >- simp[Abbr `st1`]) >> strip_tac >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem emit_op_eq:
  !opc ops st.
    emit_op opc ops st =
      (Var (STRING #"%" (toString st.cs_next_var)),
       st with <| cs_next_id := st.cs_next_id + 1;
                  cs_next_var := st.cs_next_var + 1;
                  cs_current_insts := st.cs_current_insts ++
                    [mk_inst st.cs_next_id opc ops
                       [STRING #"%" (toString st.cs_next_var)]] |>)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def]
QED

Theorem emit_inst_eq:
  !opc ops outs st.
    emit_inst opc ops outs st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                      cs_current_insts := st.cs_current_insts ++
                        [mk_inst st.cs_next_id opc ops outs] |>)
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem emit_void_eq:
  !opc ops st.
    emit_void opc ops st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                      cs_current_insts := st.cs_current_insts ++
                        [mk_inst st.cs_next_id opc ops []] |>)
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def]
QED

(* The state after emit_op, its new instruction and its output. *)
Theorem emit_op_facts:
  !opc ops st x st1.
    emit_op opc ops st = (x, st1) ==>
    ?out. x = Var out /\ st1.cs_next_var = st.cs_next_var + 1 /\
          ~not_fresh_at st out /\ not_fresh_at st1 out /\
          st1.cs_blocks = st.cs_blocks /\
          st1.cs_current_bb = st.cs_current_bb /\
          st1.cs_current_insts = st.cs_current_insts ++
            [mk_inst st.cs_next_id opc ops [out]] /\
          state_insts st1 =
            state_insts st ++ [mk_inst st.cs_next_id opc ops [out]]
Proof
  rw[emit_op_eq] >> simp[state_insts_def, all_blocks_def] >>
  irule fresh_output_props >> simp[]
QED

Theorem shape_step_emit_op:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal LP (\st. R st /\ EVERY (label_or_plain st) ops)
      (emit_op opc ops) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> simp[shape_step_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops [out]` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   inst.inst_outputs = [out] /\ lowered_inst_ok internal inst`
    by fs[Abbr `inst`, mk_inst_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (label_or_plain st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  gvs[] >> match_mp_tac (Q.SPECL [`st`, `st'`, `inst`] fresh_out_plain) >> gs[shape_state_def]
QED

Theorem shape_step_emit_inst:
  !internal LP R opc ops outs.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal LP
      (\st. R st /\ EVERY (label_or_plain st) ops /\
            EVERY (plain_operand st) (MAP Var outs))
      (emit_inst opc ops outs) (\x st'. R st')
Proof
  rpt strip_tac >> simp[shape_step_def, emit_inst_eq] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops outs` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   inst.inst_outputs = outs /\ lowered_inst_ok internal inst`
    by fs[Abbr `inst`, mk_inst_def] >>
  qspecl_then [`st`, `st1`, `outs`] mp_tac plain_outputs_ok >>
  (impl_tac >- simp[Abbr `st1`]) >> strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (label_or_plain st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_step_emit_void:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops [])) ==>
    shape_step internal LP (\st. R st /\ EVERY (label_or_plain st) ops)
      (emit_void opc ops) (\x st'. R st')
Proof
  rpt strip_tac >>
  `emit_void opc ops = emit_inst opc ops []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  qspecl_then [`internal`, `LP`, `R`, `opc`, `ops`, `[]`] mp_tac
    shape_step_emit_inst >>
  simp[]
QED

Theorem shape_step_fresh_vars:
  !n internal LP R.
    shape_stable R ==>
    shape_step internal LP R (fresh_vars n)
      (\vs st'. R st' /\ EVERY (plain_operand st') (MAP Var vs))
Proof
  Induct >> rpt strip_tac >> REWRITE_TAC [fresh_vars_def]
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_bind >>
  qexists_tac `\x st'. R st' /\ plain_operand st' (Var x)` >>
  reverse conj_tac >- (irule shape_step_fresh_var >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `v` >> BETA_TAC >>
  first_x_assum (qspecl_then [`internal`, `LP`,
    `\st'. R st' /\ plain_operand st' (Var v)`] mp_tac) >>
  impl_tac
  >- (fs[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  disch_then (assume_tac o BETA_RULE) >>
  irule shape_step_bind >> first_assum (irule_at Any) >>
  gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]
QED

(* Multi-return INVOKE: every output is a plain variable. *)
Theorem shape_step_emit_multi_op:
  !internal LP R opc ops n.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal LP (\st. R st /\ EVERY (label_or_plain st) ops)
      (emit_multi_op opc ops n)
      (\xs st'. R st' /\ EVERY (plain_operand st') xs)
Proof
  rpt strip_tac >> REWRITE_TAC [emit_multi_op_def] >>
  qspecl_then [`n`, `internal`, `LP`,
    `\st. R st /\ EVERY (label_or_plain st) ops`]
    mp_tac shape_step_fresh_vars >>
  impl_tac
  >- (fs[shape_stable_def, EVERY_MEM] >> metis_tac[label_or_plain_mono]) >>
  disch_then (assume_tac o BETA_RULE) >>
  irule shape_step_bind >> first_assum (irule_at Any) >>
  qx_gen_tac `outs` >> BETA_TAC >>
  qspecl_then [`internal`, `LP`,
    `\st. R st /\ EVERY (plain_operand st) (MAP Var outs)`, `opc`, `ops`,
    `outs`] mp_tac shape_step_emit_inst >>
  impl_tac
  >- (rpt conj_tac
      >- (fs[shape_stable_def, EVERY_MEM] >> metis_tac[plain_operand_mono]) >>
      gs[]) >>
  disch_then (assume_tac o BETA_RULE) >>
  irule shape_step_ignore_bind >>
  qexists_tac `\x st'. R st' /\ EVERY (plain_operand st') (MAP Var outs)` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> first_assum (irule_at Any) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]
QED

(* GAS feeds only the gas slot of a call. *)
Theorem shape_step_emit_op_gas:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R (emit_op GAS [])
      (\x st'. R st' /\ gas_operand st' x)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id GAS [] [out]` >>
  `inst.inst_opcode = GAS /\ inst.inst_operands = [] /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok internal inst` by (simp[Abbr `inst`] >> EVAL_TAC) >>
  `shape_extends internal LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  qspecl_then [`st`, `st'`, `inst`, `out`] mp_tac fresh_out_opaque >>
  gs[gas_operand_def]
QED

Theorem shape_step_emit_op_gas_plain:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R (emit_op GAS [])
      (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> irule shape_step_conseq >>
  drule shape_step_emit_op_gas >>
  disch_then (qspecl_then [`internal`, `LP`] (irule_at Any)) >>
  qexists_tac `LP` >>
  rw[gas_operand_def, plain_operand_def,
     stackPlanTypesTheory.is_label_operand_def] >>
  gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shape_base_emit_op_call:
  !internal LP opc g rest st x st'.
    MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) /\
    (gas_operand st g \/ plain_operand st g) /\
    EVERY (plain_operand st) rest /\ shape_base_state st /\
    emit_op opc (g :: rest) st = (x, st') ==>
    shape_extends internal LP st st' /\ shape_base_state st' /\
    plain_operand st' x
Proof
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc (g :: rest) [out]` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = g :: rest /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok internal inst`
    by (simp[Abbr `inst`] >> qpat_x_assum `!id outs. lowered_inst_ok _ _` MATCH_ACCEPT_TAC) >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM /\
   inst.inst_opcode <> RET`
    by (Cases_on `opc = CALL` >> gvs[]) >>
  `(!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
   (!x. MEM (Var x) inst.inst_operands ==>
      ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)`
    by (match_mp_tac (Q.SPECL [`st`, `g`, `rest`, `inst`] call_append_ok) >>
        ASM_REWRITE_TAC[]) >>
  `shape_extends internal LP st st' /\ shape_base_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_base_append_inst) >>
        gs[] >> rpt strip_tac >> res_tac >> gs[]) >>
  gvs[] >> match_mp_tac (Q.SPECL [`st`, `st'`, `inst`] fresh_out_plain) >> gs[]
QED

Theorem shape_base_emit_inst:
  !internal LP opc ops outs st u st'.
    shape_base_state st /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    EVERY (label_or_plain st) ops /\ EVERY (plain_operand st) (MAP Var outs) /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) /\
    emit_inst opc ops outs st = (u, st') ==>
    shape_extends internal LP st st' /\ shape_base_state st'
Proof
  rpt gen_tac >> strip_tac >> gvs[emit_inst_eq] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops outs` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   inst.inst_outputs = outs /\ lowered_inst_ok internal inst`
    by gvs[Abbr `inst`, mk_inst_def] >>
  qspecl_then [`st`, `st1`, `outs`] mp_tac plain_outputs_ok >>
  (impl_tac >- simp[Abbr `st1`]) >> strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (label_or_plain st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st1`, `inst`] shape_base_append_inst) >>
  gvs[Abbr `st1`]
QED

Theorem shape_base_emit_op:
  !internal LP opc ops st x st'.
    shape_base_state st /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    EVERY (label_or_plain st) ops /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) /\
    emit_op opc ops st = (x, st') ==>
    shape_extends internal LP st st' /\ shape_base_state st' /\
    plain_operand st' x
Proof
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops [out]` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   inst.inst_outputs = [out] /\ lowered_inst_ok internal inst`
    by fs[Abbr `inst`, mk_inst_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (label_or_plain st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st' /\ shape_base_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_base_append_inst) >>
        gs[]) >>
  gvs[] >> match_mp_tac (Q.SPECL [`st`, `st'`, `inst`] fresh_out_plain) >> gs[]
QED

Theorem shape_base_new_block:
  !internal LP lbl st u st'.
    shape_base_state st /\ LP lbl /\ ~internal_label_ok lbl /\
    new_block lbl st = (u, st') ==>
    shape_extends internal LP st st' /\ shape_base_state st'
Proof
  rpt gen_tac >> strip_tac >>
  drule cs_extends_new_block >> strip_tac >> gvs[new_block_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `all_blocks st1 =
     all_blocks st ++ [<| bb_label := lbl; bb_instructions := [] |>]`
    by simp[Abbr `st1`, all_blocks_def] >>
  `st1.cs_next_var = st.cs_next_var` by simp[Abbr `st1`] >>
  `state_insts st1 = state_insts st` by gs[state_insts_def] >>
  `added_labels st st1 = [lbl]`
    by gs[added_labels_def, DROP_LENGTH_MAP_APPEND] >>
  `added_insts st st1 = []` by gs[added_insts_def, DROP_LENGTH_NIL] >>
  conj_tac >- gs[shape_extends_def] >>
  gs[shape_base_state_def] >>
  conj_tac >- (irule rets_scoped_append_empty >> simp[]) >>
  metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem shape_base_step_emit_op_call:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) ==>
    shape_base_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (emit_op opc (g :: rest)) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt gen_tac >> strip_tac >> simp[shape_base_step_def] >>
  rpt gen_tac >> strip_tac >>
  `shape_extends internal LP st st' /\ shape_base_state st' /\
   plain_operand st' x` by
    (irule shape_base_emit_op_call >> simp[] >>
     qexistsl [`g`, `opc`, `rest`] >> fs[]) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_emit_op:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_base_step internal LP (\st. R st /\ EVERY (label_or_plain st) ops)
      (emit_op opc ops) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> rw[shape_base_step_def] >>
  drule_all shape_base_emit_op >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_emit_inst:
  !internal LP R opc ops outs.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_base_step internal LP
      (\st. R st /\ EVERY (label_or_plain st) ops /\
            EVERY (plain_operand st) (MAP Var outs))
      (emit_inst opc ops outs) (\x st'. R st')
Proof
  rpt strip_tac >> rw[shape_base_step_def] >>
  drule_all shape_base_emit_inst >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_emit_void:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops [])) ==>
    shape_base_step internal LP (\st. R st /\ EVERY (label_or_plain st) ops)
      (emit_void opc ops) (\x st'. R st')
Proof
  rpt strip_tac >>
  `emit_void opc ops = emit_inst opc ops []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  qspecl_then [`internal`, `LP`, `R`, `opc`, `ops`, `[]`] mp_tac
    shape_base_step_emit_inst >>
  simp[]
QED

Theorem shape_base_step_new_block:
  !internal LP R lbl.
    shape_stable R /\ LP lbl /\ ~internal_label_ok lbl ==>
    shape_base_step internal LP R (new_block lbl) (\x st'. R st')
Proof
  rpt strip_tac >> rw[shape_base_step_def] >>
  drule_all shape_base_new_block >> strip_tac >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_state_same_code:
  !st st'.
    shape_base_state st /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts /\
    st.cs_next_var <= st'.cs_next_var ==>
    shape_base_state st'
Proof
  rpt strip_tac >>
  `state_insts st' = state_insts st` by gs[state_insts_def, all_blocks_def] >>
  `all_blocks st' = all_blocks st` by simp[all_blocks_def] >>
  gs[shape_base_state_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem shape_base_step_fresh_label:
  !internal LP R sfx.
    shape_stable R ==>
    shape_base_step internal LP R (fresh_label sfx)
      (\l st'. R st' /\ compiler_label l)
Proof
  simp[shape_base_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >> gvs[fresh_label_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_base_state st1`
    by (irule shape_base_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  simp[compiler_label_def, fresh_label_output_in_future] >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_fresh_label_sfx:
  !internal LP R sfx.
    shape_stable R ==>
    shape_base_step internal LP R (fresh_label sfx)
      (\l st'. R st' /\ compiler_label l /\ label_sfx sfx l)
Proof
  simp[shape_base_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >> gvs[fresh_label_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_base_state st1`
    by (irule shape_base_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  simp[compiler_label_def, fresh_label_output_in_future, label_sfx_def] >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_alloc_buffer_zero:
  !internal LP R.
    shape_stable R ==>
    shape_base_step internal LP R (compile_alloc_buffer 0)
      (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_alloc_buffer_def] >>
  irule shape_base_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_base_step_return >> simp[]) >>
  irule shape_base_step_conseq >>
  qexistsl [`LP`, `\st. R st /\ EVERY (label_or_plain st) [Lit 0w]`,
            `\op st. R st /\ plain_operand st op`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def,
                  stackPlanTypesTheory.is_label_operand_def] >>
  conj_tac >- simp[] >>
  match_mp_tac (BETA_RULE (Q.SPECL [`internal`, `LP`, `R`]
    shape_base_step_emit_op)) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, label_positions_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shape_base_step_emit_op_guarded:
  !internal LP P opc ops.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
    shape_base_step internal LP P (emit_op opc ops)
      (\x st. P st /\ plain_operand st x)
Proof
  rpt gen_tac >> strip_tac >> rw[shape_base_step_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all shape_base_emit_op >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_emit_inst_guarded:
  !internal LP P opc ops outs.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM; RET] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      EVERY (plain_operand st) (MAP Var outs) /\
      (!id. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
    shape_base_step internal LP P (emit_inst opc ops outs) (\x st. P st)
Proof
  rpt gen_tac >> strip_tac >> rw[shape_base_step_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all shape_base_emit_inst >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_base_step_extcall_revert:
  !internal LP R.
    shape_stable R ==>
    shape_base_step internal LP R
      (do rds <- emit_op RETURNDATASIZE [];
          buf <- compile_alloc_buffer 0;
          emit_void RETURNDATACOPY [buf.buf_operand; Lit 0w; rds];
          emit_inst REVERT [buf.buf_operand; rds] []
       od) (\u st. R st)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_base_step_bind >>
  qexists_tac `\rds st. R st /\ plain_operand st rds` >>
  reverse conj_tac
  >- (irule shape_base_step_emit_op_guarded >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
        mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
        is_terminator_def, is_param_opcode_def, is_read0_opcode_def]) >>
  qx_gen_tac `rds` >> BETA_TAC >>
  `shape_stable (\st. R st /\ plain_operand st rds)` by
    (rw[shape_stable_def] >> metis_tac[shape_stable_def, plain_operand_mono]) >>
  irule shape_base_step_bind >>
  qexists_tac `\buf st. (R st /\ plain_operand st rds) /\
                           plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_alloc_buffer_zero >> simp[]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  `shape_stable (\st. (R st /\ plain_operand st rds) /\
                       plain_operand st buf.buf_operand)` by
    (rw[shape_stable_def] >> metis_tac[shape_stable_def, plain_operand_mono]) >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. (R st /\ plain_operand st rds) /\
                         plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >>
    irule shape_base_step_conseq >>
    irule_at Any shape_base_step_emit_inst_guarded >>
    qexistsl [`\st. (R st /\ plain_operand st rds) /\
                       plain_operand st buf.buf_operand`, `LP`] >>
    simp[label_or_plain_def, lowered_inst_ok_def, raw_opcode_ok_def,
      inst_shape_ok_def, mk_inst_def, label_positions_ok_def,
      inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
      is_read0_opcode_def, stackPlanTypesTheory.is_label_operand_def] >>
    rpt strip_tac >> gvs[plain_operand_def] >>
    metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `emit_void RETURNDATACOPY [buf.buf_operand; Lit 0w; rds] =
   emit_inst RETURNDATACOPY [buf.buf_operand; Lit 0w; rds] []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  simp[] >> ho_match_mp_tac shape_base_step_emit_inst_guarded >>
  simp[label_or_plain_def, plain_operand_def, lowered_inst_ok_def,
    raw_opcode_ok_def, inst_shape_ok_def, mk_inst_def, label_positions_ok_def,
    inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
    is_read0_opcode_def, stackPlanTypesTheory.is_label_operand_def]
QED

(* Exact unchecked interval in ExtCall, ending at the checked continuation.
   This proof abbreviation changes no lowering definition. *)
Definition checked_extcall_def:
  checked_extcall opc g rest =
    do success <- emit_op opc (g :: rest);
       fail_lbl <- fresh_label "extcall_fail";
       cont_lbl <- fresh_label "extcall_cont";
       emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       rds <- emit_op RETURNDATASIZE [];
       fail_buf_alloc <- compile_alloc_buffer 0;
       let fail_buf = fail_buf_alloc.buf_operand in
       do emit_void RETURNDATACOPY [fail_buf; Lit 0w; rds];
          emit_inst REVERT [fail_buf; rds] []
       od;
       new_block cont_lbl;
       return success
    od
End

(* Consumer rewrite: the final return in the proof abbreviation disappears
   against the actual ExtCall continuation, for either call opcode. *)
Theorem checked_extcall_bind:
  comp_bind (checked_extcall opc g rest) f =
    do success <- emit_op opc (g :: rest);
       fail_lbl <- fresh_label "extcall_fail";
       cont_lbl <- fresh_label "extcall_cont";
       emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       rds <- emit_op RETURNDATASIZE [];
       fail_buf_alloc <- compile_alloc_buffer 0;
       let fail_buf = fail_buf_alloc.buf_operand in
       do emit_void RETURNDATACOPY [fail_buf; Lit 0w; rds];
          emit_inst REVERT [fail_buf; rds] []
       od;
       new_block cont_lbl;
       f success
    od
Proof
  rewrite_tac[checked_extcall_def, comp_ignore_bind_def] >>
  simp[comp_bind_assoc] >>
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem checked_extcall_grouped[local]:
  checked_extcall opc g rest =
    do success <- emit_op opc (g :: rest);
       fail_lbl <- fresh_label "extcall_fail";
       cont_lbl <- fresh_label "extcall_cont";
       emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       (do rds <- emit_op RETURNDATASIZE [];
           buf <- compile_alloc_buffer 0;
           emit_void RETURNDATACOPY [buf.buf_operand; Lit 0w; rds];
           emit_inst REVERT [buf.buf_operand; rds] [] od);
       new_block cont_lbl;
       return success
    od
Proof
  simp[checked_extcall_def, comp_ignore_bind_def, comp_bind_assoc,
       comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem shape_base_step_pure_pre[local]:
  !internal LP b P m Q.
    (b ==> shape_base_step internal LP P m Q) ==>
    shape_base_step internal LP (\st. b /\ P st) m Q
Proof
  rw[shape_base_step_def] >> metis_tac[]
QED

Theorem shape_base_step_checked_extcall:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) /\
    (!lbl. compiler_label lbl ==> LP lbl) ==>
    shape_base_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (checked_extcall opc g rest) (\x st. R st /\ plain_operand st x)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[checked_extcall_grouped] >>
  irule shape_base_step_bind >>
  qexists_tac `\success st. R st /\ plain_operand st success` >>
  reverse conj_tac >- (irule shape_base_step_emit_op_call >> simp[]) >>
  qx_gen_tac `success` >> BETA_TAC >>
  `shape_stable (\st. R st /\ plain_operand st success)` by
    (rw[shape_stable_def] >> metis_tac[shape_stable_def, plain_operand_mono]) >>
  irule shape_base_step_bind >>
  qexists_tac `\fail st. (R st /\ plain_operand st success) /\ compiler_label fail /\
                          label_sfx "extcall_fail" fail` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_fresh_label_sfx >> simp[]) >>
  qx_gen_tac `fail_lbl` >> BETA_TAC >>
  irule shape_base_step_bind >>
  qexists_tac `\cont st. ((R st /\ plain_operand st success) /\
                          compiler_label fail_lbl /\ label_sfx "extcall_fail" fail_lbl) /\
                         compiler_label cont /\ label_sfx "extcall_cont" cont` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_fresh_label_sfx >>
    ho_match_mp_tac shape_stable_conj >> conj_tac >- simp[] >>
    simp[shape_stable_def]) >>
  qx_gen_tac `cont` >> BETA_TAC >> suspend "tail"
QED

Resume shape_base_step_checked_extcall[tail]:
  qpat_x_assum `MEM opc _` kall_tac >>
  qpat_x_assum `!id outs. lowered_inst_ok _ _` kall_tac >>
  irule shape_base_step_conseq >>
  qexistsl [`LP`, `\st. (compiler_label fail_lbl /\ compiler_label cont /\
                          label_sfx "extcall_fail" fail_lbl /\ label_sfx "extcall_cont" cont) /\
                         (R st /\ plain_operand st success)`,
            `\x st. R st /\ plain_operand st x`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac shape_base_step_pure_pre >> strip_tac >>
  `cont <> fail_lbl` by
    (`"extcall_cont" <> "extcall_fail"` by EVAL_TAC >> metis_tac[label_sfx_distinct]) >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st success` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_emit_inst_guarded >>
    simp[label_or_plain_def, lowered_inst_ok_def, raw_opcode_ok_def,
      inst_shape_ok_def, mk_inst_def, label_positions_ok_def,
      inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
      is_read0_opcode_def, stackPlanTypesTheory.is_label_operand_def] >>
    rpt strip_tac >> gvs[plain_operand_def, jump_label_ok_def] >>
    metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st success` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_new_block >> simp[]) >>
  gen_tac >> BETA_TAC >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st success` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_extcall_revert >> simp[]) >>
  gen_tac >> BETA_TAC >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st success` >>
  reverse conj_tac >- (ho_match_mp_tac shape_base_step_new_block >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_base_step_return >> simp[]
QED

Finalise shape_base_step_checked_extcall

Theorem checked_extcall_layout:
  checked_extcall opc g rest st = (success, st') ==>
  ?v call guard rbb cont.
    success = Var v /\
    all_blocks st' = REVERSE st.cs_blocks ++
      [<| bb_label := st.cs_current_bb;
          bb_instructions := st.cs_current_insts ++ [call; guard] |>;
       rbb; cont] /\
    call.inst_outputs = [v] /\
    guard.inst_opcode = JNZ /\
    guard.inst_operands = [Var v; Label cont.bb_label; Label rbb.bb_label] /\
    compiler_label rbb.bb_label /\ rbb.bb_instructions <> [] /\
    EVERY (\j. j.inst_opcode <> INVOKE) rbb.bb_instructions /\
    (LAST rbb.bb_instructions).inst_opcode = REVERT /\
    EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) rbb.bb_instructions /\
    cont.bb_instructions = []
Proof
  simp[checked_extcall_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, emit_inst_def, emit_def, new_block_def, fresh_var_def, fresh_id_def,
       fresh_label_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[all_blocks_def] >>
  simp[compiler_label_def, fresh_label_output_in_future]
QED

Theorem checked_extcall_raw_checked_state:
  raw_checked_state st /\ checked_extcall opc g rest st = (success, st') ==>
  raw_checked_state st'
Proof
  strip_tac >> drule checked_extcall_layout >> strip_tac >>
  `raw_checked_blocks (REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts |>])`
    by gvs[raw_checked_state_def, all_blocks_def] >>
  drule raw_checked_blocks_splice_branch >>
  simp[raw_checked_state_def] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem shape_step_emit_op_call_branch:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) /\
    (!lbl. compiler_label lbl ==> LP lbl) ==>
    shape_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (checked_extcall opc g rest) (\x st. R st /\ plain_operand st x)
Proof
  rpt gen_tac >> strip_tac >> drule_all shape_base_step_checked_extcall >>
  simp[shape_base_step_def, shape_step_def, shape_state_def] >>
  metis_tac[checked_extcall_raw_checked_state]
QED

Theorem checked_extcall_then:
  comp_bind (checked_extcall opc g rest) (\success. (k : 'a compiler)) =
    do success <- emit_op opc (g :: rest);
       fail_lbl <- fresh_label "extcall_fail";
       cont_lbl <- fresh_label "extcall_cont";
       emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       rds <- emit_op RETURNDATASIZE [];
       fail_buf_alloc <- compile_alloc_buffer 0;
       (do emit_void RETURNDATACOPY [fail_buf_alloc.buf_operand; Lit 0w; rds];
           emit_inst REVERT [fail_buf_alloc.buf_operand; rds] [] od);
       new_block cont_lbl;
       k
    od
Proof
  rewrite_tac[checked_extcall_bind] >> simp[]
QED

Theorem shape_step_checked_extcall_then:
  shape_stable B /\ MEM opc [CALL; STATICCALL] /\
  (!st id outs. B st /\ (gas_operand st g \/ plain_operand st g) /\
       EVERY (plain_operand st) rest ==>
       lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) /\
  shape_step internal compiler_label B k Q ==>
  shape_step internal compiler_label
    (\st. B st /\ (gas_operand st g \/ plain_operand st g) /\
          EVERY (plain_operand st) rest)
    (do success <- emit_op opc (g :: rest);
        fail_lbl <- fresh_label "extcall_fail";
        cont_lbl <- fresh_label "extcall_cont";
        emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [];
        new_block fail_lbl;
        rds <- emit_op RETURNDATASIZE [];
        fail_buf_alloc <- compile_alloc_buffer 0;
        (do emit_void RETURNDATACOPY [fail_buf_alloc.buf_operand; Lit 0w; rds];
            emit_inst REVERT [fail_buf_alloc.buf_operand; rds] [] od);
        new_block cont_lbl;
        k
     od) Q
Proof
  strip_tac >> rewrite_tac[GSYM checked_extcall_then, shape_step_def] >>
  rpt gen_tac >> strip_tac >>
  `!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)`
    by metis_tac[] >>
  `shape_step internal compiler_label
     (\st. B st /\ (gas_operand st g \/ plain_operand st g) /\
           EVERY (plain_operand st) rest)
     (comp_bind (checked_extcall opc g rest) (\success. k)) Q` by
    (irule shape_step_bind >>
     qexists_tac `\v st. B st /\ plain_operand st v` >> reverse conj_tac
     >- (irule shape_step_emit_op_call_branch >> simp[]) >>
     gen_tac >> irule shape_step_conseq >>
     qexistsl [`compiler_label`, `B`, `Q`] >> simp[]) >>
  gvs[shape_step_def] >> metis_tac[]
QED

Theorem shape_step_emit_op_call_assert:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) ==>
    shape_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (comp_bind (emit_op opc (g :: rest))
        (\success. comp_ignore_bind (emit_inst ASSERT [success] [])
           (comp_return success)))
      (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> simp[shape_step_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `emit_op opc (g :: rest) st` >>
  rename1 `emit_op opc (g :: rest) st = (success, mid)` >>
  `shape_base_state st` by gvs[shape_state_def] >>
  `shape_extends internal LP st mid /\ shape_base_state mid /\
   plain_operand mid success` by
    (irule shape_base_emit_op_call >> simp[] >>
     qexistsl [`g`, `opc`, `rest`] >> fs[]) >>
  drule emit_op_facts >> strip_tac >>
  Cases_on `emit_inst ASSERT [success] [] mid` >> gvs[] >>
  qmatch_goalsub_rename_tac `shape_extends internal LP st last` >>
  `EVERY (label_or_plain mid) [Var out]` by
    gvs[label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >>
  `!id. lowered_inst_ok internal (mk_inst id ASSERT [Var out] [])` by
    (simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
       inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
       stackPlanTypesTheory.is_label_operand_def]) >>
  drule_all (SRULE [] (Q.GEN `ops` (Q.SPECL [`internal`, `LP`, `ASSERT`, `ops`, `[]`]
    shape_base_emit_inst))) >>
  disch_then (qspec_then `LP` strip_assume_tac) >>
  `shape_extends internal LP st last` by metis_tac[shape_extends_trans] >>
  `R last` by metis_tac[shape_stable_def] >>
  `plain_operand last (Var out)` by metis_tac[plain_operand_mono, shape_extends_def] >>
  simp[shape_state_def] >>
  `raw_checked_blocks (REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts |>])`
    by gvs[shape_state_def, raw_checked_state_def, all_blocks_def] >>
  qmatch_asmsub_abbrev_tac `mid.cs_current_insts = _ ++ [call]` >>
  `call.inst_outputs = [out]` by gvs[Abbr `call`, mk_inst_def] >>
  drule raw_checked_blocks_splice_assert >>
  disch_then (qspecl_then [`out`,
    `mk_inst mid.cs_next_id ASSERT [Var out] []`, `call`] mp_tac) >>
  simp[mk_inst_def] >> strip_tac >>
  gvs[raw_checked_state_def, all_blocks_def, emit_inst_eq, APPEND_ASSOC, mk_inst_def] >>
  qpat_x_assum `raw_checked_blocks _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

(* The return PC exists only in internal-function code. *)
Theorem shape_step_emit_op_retpc:
  !LP R w.
    shape_stable R ==>
    shape_step T LP (\st. R st /\ internal_label_ok st.cs_current_bb)
      (emit_op RETPC_PARAM [Lit w])
      (\x st'. R st' /\ retpc_operand st' x)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id RETPC_PARAM [Lit w] [out]` >>
  `inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit w] /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok T inst` by (simp[Abbr `inst`] >> EVAL_TAC) >>
  `shape_extends T LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`T`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  qspecl_then [`st`, `st'`, `inst`, `out`] mp_tac fresh_out_opaque >>
  gs[retpc_operand_def] >> strip_tac >>
  simp[opaque_out_def] >> qexists_tac `inst` >> simp[] >>
  simp[cur_entry_insts_def, all_blocks_def] >>
  DEP_REWRITE_TAC[fn_entry_insts_internal_last] >> gs[]
QED

Theorem shape_step_emit_inst_ret:
  !LP R front r.
    shape_stable R /\
    (!id. lowered_inst_ok T (mk_inst id RET (front ++ [r]) [])) ==>
    shape_step T LP
      (\st. R st /\ EVERY (plain_operand st) front /\ retpc_operand st r)
      (emit_inst RET (front ++ [r]) []) (\x st'. R st')
Proof
  rpt strip_tac >> simp[shape_step_def, emit_inst_eq] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id RET (front ++ [r]) []` >>
  `inst.inst_opcode = RET /\ inst.inst_operands = front ++ [r] /\
   inst.inst_outputs = []`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok T inst`
    by (simp[Abbr `inst`] >> qpat_x_assum `!id. lowered_inst_ok _ _` MATCH_ACCEPT_TAC) >>
  `(!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
   (!x. MEM (Var x) inst.inst_operands ==>
      (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
         inst.inst_opcode = RET /\
         ?front'. inst.inst_operands = front' ++ [Var x] /\
                  ~MEM (Var x) front'))`
    by (match_mp_tac (Q.SPECL [`st`, `front`, `r`, `inst`] ret_append_ok) >>
        ASM_REWRITE_TAC[]) >>
  `shape_extends T LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`T`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`, retpc_operand_def] >> rpt strip_tac >> res_tac >> gs[]) >>
  metis_tac[shape_stable_def]
QED

(* ===== From the invariant to opaque_use_ok ===== *)

Theorem copy_phi_var_retpc_opaque_out:
  !fn x.
    copy_phi_var RETPC_PARAM fn x ==>
    !insts. opaque_insts_ok insts /\
            (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
            opaque_out RETPC_PARAM insts x
Proof
  `!origin fn x. copy_phi_var origin fn x ==>
    origin = RETPC_PARAM ==>
    !insts. opaque_insts_ok insts /\
      (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
      opaque_out origin insts x` suffices_by metis_tac[] >>
  Induct_on `copy_phi_var` >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  disch_then SUBST_ALL_TAC >> rpt gen_tac >> strip_tac
  >- (simp[opaque_out_def] >> metis_tac[])
  >> rename1 `copy_phi_var RETPC_PARAM fn y` >>
  `opaque_out RETPC_PARAM insts y` by (first_x_assum irule >> gs[]) >>
  `MEM inst insts` by res_tac >>
  qpat_x_assum `opaque_insts_ok _`
    (qspecl_then [`inst`, `y`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
  gvs[]
QED

Theorem opaque_insts_ok_opaque_use_ok:
  !insts fn.
    opaque_insts_ok insts /\
    (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
    opaque_use_ok fn
Proof
  rpt strip_tac >> simp[opaque_use_ok_def, retpc_var_def] >>
  rpt strip_tac >>
  `MEM inst insts` by res_tac >>
  drule copy_phi_var_retpc_opaque_out >>
  disch_then (qspec_then `insts` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  qpat_x_assum `opaque_insts_ok _`
    (qspecl_then [`inst`, `x`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
  simp[retpc_use_ok_def] >> metis_tac[]
QED

(* Runtime data labels are legal only in CODECOPY's source position. *)
Theorem shape_step_emit_runtime_codecopy:
  !internal LP R dst sz.
    shape_stable R ==>
    shape_step internal LP
      (\st. R st /\ EVERY (plain_operand st) [dst; sz])
      (emit_void CODECOPY [dst; Label "runtime_begin"; sz])
      (\u st. R st /\ EVERY (plain_operand st) [dst; sz])
Proof
  rpt strip_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`internal`, `LP`,
    `\st. R st /\ EVERY (plain_operand st) [dst; sz]`,
    `CODECOPY`, `[dst; Label "runtime_begin"; sz]`] shape_step_emit_void) >>
  (impl_tac >-
    (conj_tac >- simp[shape_stable_conj, shape_stable_plain_operands] >>
     simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
       inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def] >>
     gvs[plain_operand_def] >> Cases_on `dst` >> Cases_on `sz` >>
     gvs[stackPlanTypesTheory.is_label_operand_def])) >>
  simp[shape_step_def] >>
  disch_then (qspecl_then [`st`, `st'`] mp_tac) >>
  simp[label_or_plain_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shape_step_emit_entry_return:
  !LP dst sz.
    shape_step F LP (\st. EVERY (plain_operand st) [dst; sz])
      (emit_inst RETURN [dst; sz] []) (\u st. T)
Proof
  rpt gen_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`F`, `LP`, `\st. T`, `RETURN`, `[dst; sz]`, `[]`]
    shape_step_emit_inst) >>
  (impl_tac >-
    (simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
       inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def] >>
     gvs[plain_operand_def] >> Cases_on `dst` >> Cases_on `sz` >>
     gvs[stackPlanTypesTheory.is_label_operand_def])) >>
  simp[shape_step_def, label_or_plain_def] >> metis_tac[]
QED

Theorem opaque_insts_ok_retpc_shape_ok:
  !insts fn.
    opaque_insts_ok insts /\ fn.fn_blocks <> [] /\
    (!i. MEM i (fn_insts fn) ==> MEM i insts) /\
    (!i. MEM i (fn_insts fn) ==>
         i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET) /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode = RET ==>
      ?front x. i.inst_operands = front ++ [Var x] /\
        opaque_out RETPC_PARAM (HD fn.fn_blocks).bb_instructions x) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\
           opaque_out RETPC_PARAM insts x ==> i.inst_opcode = RETPC_PARAM) /\
    (!i j x. MEM i insts /\ MEM j insts /\ i.inst_opcode = RETPC_PARAM /\
             MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j) ==>
    retpc_shape_ok fn
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[retpc_shape_ok_def] >>
  `!x. retpc_var fn x ==> opaque_out RETPC_PARAM insts x`
    by (rpt strip_tac >> fs[retpc_var_def] >>
        drule copy_phi_var_retpc_opaque_out >>
        disch_then (qspec_then `insts` mp_tac) >> simp[]) >>
  `!x. retpc_var (reachable_fn fn) x ==> opaque_out RETPC_PARAM insts x`
    by metis_tac[reachable_retpc_var] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `inst.inst_opcode <> PHI` by gvs[] >>
      `MEM inst (fn_insts fn)` by metis_tac[reachable_fn_insts_nonphi] >>
      `inst.inst_opcode = RET`
        by (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >> res_tac >>
            simp[]) >>
      qpat_x_assum `!i. MEM i (fn_insts fn) /\ i.inst_opcode = RET ==> _`
        drule >> simp[] >> strip_tac >>
      qexistsl_tac [`front`, `x`] >> simp[retpc_var_def] >>
      gvs[opaque_out_def] >> irule copy_phi_var_seed >>
      qexists_tac `inst'` >> simp[] >>
      irule entry_insts_reachable >> simp[])
  >- (rpt strip_tac >>
      qspecl_then [`fn`, `inst`, `Var x`] mp_tac reachable_fn_insts_operand >>
      simp[] >> strip_tac >>
      `opaque_out RETPC_PARAM insts x /\ MEM i insts` by (res_tac >> simp[]) >>
      qpat_x_assum `opaque_insts_ok _`
        (qspecl_then [`i`, `x`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >> disj1_tac >> first_x_assum irule >> metis_tac[])
  >> rpt strip_tac >>
  `opaque_out RETPC_PARAM insts x` by metis_tac[] >>
  `MEM i insts /\ MEM j insts` by metis_tac[] >>
  `i.inst_opcode = RETPC_PARAM` by metis_tac[] >>
  metis_tac[]
QED
