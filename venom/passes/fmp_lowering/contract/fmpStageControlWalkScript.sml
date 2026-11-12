(* Exact code positions in the indexed lowering walk. *)
Theory fmpStageControlWalk
Ancestors
  fmpLowerDefs fmpLowerIndexedProps fmpStepRewrite fmpLowerSequenceExec finite_map list arithmetic

Theorem fmp_control_inst_length:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  LENGTH out = if inst.inst_opcode = DALLOCA then 4 else 1
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (strip_tac >> drule_all fmp_lower_inst_dalloca_shape >>
      strip_tac >> simp[]) >>
  strip_tac >> drule fmp_lower_inst_ids >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem fmp_control_emit_length:
  !bases s out s'. fmp_emit_restores runner s bases = (out,s') ==>
  LENGTH out = LENGTH bases
Proof
  Induct >> simp[fmp_emit_restores_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem fmp_control_select_distinct:
  !rs p bases later.
  fmp_select_point_restores p rs = (bases,later) /\
  ALL_DISTINCT (MAP FST rs) ==>
  ALL_DISTINCT (MAP FST later) /\
  LENGTH bases = if MEM p (MAP FST rs) then 1 else 0
Proof
  Induct >> simp[fmp_select_point_restores_def] >>
  gen_tac >> Cases_on `h` >> rpt gen_tac >>
  Cases_on `fmp_select_point_restores p rs` >>
  Cases_on `q = p` >>
  simp[fmp_select_point_restores_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  simp[] >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac >>
  Cases_on `MEM p (MAP FST rs)` >> gvs[] >>
  gvs[MEM_MAP] >> metis_tac[pairTheory.PAIR, pairTheory.FST, pairTheory.SND]
QED

Theorem fmp_control_select_plan:
  fmp_select_point_restores (lbl,k) rs = (bases,later) /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) ==>
  ALL_DISTINCT (MAP FST later) /\
  LENGTH bases = (if (lbl,k) IN FDOM plan then 1 else 0) /\
  (!j b. MEM ((lbl,j),b) later <=> SUC k <= j /\ FLOOKUP plan (lbl,j) = SOME b)
Proof
  rpt strip_tac >> drule_all fmp_control_select_distinct >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac
  >- (`(MEM (lbl,k) (MAP FST rs)) <=> (lbl,k) IN FDOM plan` by
        (simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
         qpat_x_assum `!j b. MEM ((lbl,j),b) rs <=> _`
           (qspec_then `k` mp_tac) >>
         simp[flookup_thm] >> metis_tac[]) >>
      gvs[]) >>
  first_x_assum (qspecl_then [`(lbl,j)`,`b`] mp_tac) >> simp[] >>
  Cases_on `j = k` >> simp[] >>
  `k <= j <=> SUC k <= j` by decide_tac >> simp[]
QED

(* Why: the lowering only takes fresh names, so a name the supply has
   used stays used along the walk. *)
Theorem fmp_control_inst_vars_mono:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[irSupplyTheory.fresh_inst_id_def] >>
  metis_tac[irSupplyTheory.fresh_ir_var_preserves_old]
QED

Theorem fmp_control_emit_vars_mono:
  !bases s out s'. fmp_emit_restores runner s bases = (out,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Induct >> simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[irSupplyTheory.fresh_inst_id_def] >> first_x_assum drule >> simp[]
QED

Theorem fmp_control_indexed_vars_mono:
  !insts k s rs out left s'.
  fmp_lower_indexed infos ctx runner lbl k s rs insts = SOME (out,left,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >>
  metis_tac[fmp_control_emit_vars_mono, fmp_control_inst_vars_mono]
QED

Theorem fmp_control_walk_suffix:
  !n xs k s rs out left s'.
  fmp_lower_indexed infos ctx runner lbl k s rs xs = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  n <= LENGTH xs ==>
  ?rsn sn tail.
    (!v. MEM v s.irs_used_vars ==> MEM v sn.irs_used_vars) /\
    ALL_DISTINCT (MAP FST rsn) /\
    (!j b. MEM ((lbl,j),b) rsn <=> k+n <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
    fmp_lower_indexed infos ctx runner lbl (k+n) sn rsn (DROP n xs) = SOME (tail,left,s') /\
    DROP (SUM (GENLIST (\j. (if (lbl,k+j) IN FDOM plan then 1 else 0) +
          (if (EL j xs).inst_opcode = DALLOCA then 4 else 1)) n)) out = tail
Proof
  Induct >- (rpt strip_tac >> qexistsl [`rs`,`s`,`out`] >> simp[]) >>
  Cases_on `xs` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[fmp_lower_indexed_cons] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  drule fmp_control_inst_length >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl [`rsn`,`sn`] >>
  conj_tac
  >- metis_tac[fmp_control_emit_vars_mono, fmp_control_inst_vars_mono] >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ (n + SUC k) _ _ _ = _` mp_tac >>
  simp[Once GENLIST_CONS, combinTheory.o_DEF] >>
  simp[Once ADD_COMM, NoAsms] >>
  `LENGTH prefix + LENGTH head =
    (if h.inst_opcode = DALLOCA then 4 else 1) +
    (if (lbl,k) IN FDOM plan then 1 else 0)` by metis_tac[ADD_COMM] >>
  pop_assum (SUBST1_TAC o GSYM) >>
  simp[NoAsms, DROP_APPEND2, GSYM ADD_ASSOC] >>
  `k + SUC n = n + SUC k` by decide_tac >>
  `!x. k + SUC x = x + SUC k` by (gen_tac >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem fmp_control_walk_kept_head:
  fmp_lower_indexed infos ctx runner lbl k s rs (inst::xs) = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  ~MEM inst.inst_opcode [DALLOCA; DRET; GETFMP; SETFMP; RETFMP; INVOKE] ==>
  (if (lbl,k) IN FDOM plan then 1 else 0) < LENGTH out /\
  EL (if (lbl,k) IN FDOM plan then 1 else 0) out = inst
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  `head = [inst]` by
    (qpat_x_assum `fmp_lower_inst _ _ _ _ _ = _` mp_tac >>
     simp[fmp_lower_inst_ordinary] >>
     Cases_on `is_raw_fmp_opcode inst.inst_opcode` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST1_TAC o GSYM) >>
  simp[EL_APPEND_EQN]
QED
