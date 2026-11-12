(* The first restore and its bounded straight-line execution. *)
Theory fmpStageFmpStepsRestoreControl
Ancestors
  fmpStageControl fmpStageRel fmpLowerIndexedProps fmpLowerReclaimPlan
  fmpLowerRestoreExec fmpLowerDefs analysisSimDefs venomExecSemantics venomState venomInst
  finite_map list rich_list

(* Only the head is needed: membership does not assert list uniqueness. *)
Theorem fmp_restore_indexed_head:
  fmp_lower_indexed infos ctx runner lbl idx sp restores (inst::insts) =
    SOME (code,leftover,sp') /\
  (!b. MEM ((lbl,idx),b) restores <=> FLOOKUP plan (lbl,idx) = SOME b) /\
  FLOOKUP plan (lbl,idx) = SOME (target:string) ==>
  ?id tail. code = mk_inst id ASSIGN [Var target] [runner] :: tail
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >>
  drule_all fmp_select_point_plan >> strip_tac >>
  `bases <> [] /\ EVERY (\b. b = target) bases` by metis_tac[] >>
  Cases_on `bases` >> gvs[] >>
  gvs[fmp_emit_restores_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_restore_target_run:
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx < LENGTH bb'.bb_instructions /\
  EL t.vs_inst_idx bb'.bb_instructions =
    mk_inst id ASSIGN [Var target] [runner] /\
  lookup_var target t = SOME value ==>
  (!fuel. fmp_target_run fuel C' name t 1
    ((update_var runner value t) with vs_inst_idx := SUC t.vs_inst_idx)) /\
  (EL t.vs_inst_idx bb'.bb_instructions).inst_opcode = ASSIGN
Proof
  strip_tac >> simp[mk_inst_def] >> gen_tac >>
  simp[fmp_target_run_def, run_insts_def, step_inst_non_invoke,
       mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
       arithmeticTheory.ADD1]
QED

Theorem fmp_restore_target_run_zero:
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx <= LENGTH bb'.bb_instructions ==>
  !fuel. fmp_target_run fuel C' name t 0 t
Proof
  rpt strip_tac >> simp[fmp_target_run_def, run_insts_def]
QED

Theorem fmp_restore_lowered_code:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx < LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) /\
  FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,idx) = SOME target ==>
  ?bb' id.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx <
      LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx)
       bb'.bb_instructions = mk_inst id ASSIGN [Var target] [runner]
Proof
  strip_tac >>
  `idx <= LENGTH bb.bb_instructions` by simp[] >>
  drule fmp_stage_tidx_code >>
  disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!b. MEM ((bb.bb_label,idx),b) restores <=>
       FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,idx) = SOME b`
    by simp[] >>
  `DROP idx bb.bb_instructions =
     EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions`
    by simp[DROP_CONS_EL] >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once DROP_CONS_EL] >> strip_tac >>
  drule_all fmp_restore_indexed_head >> strip_tac >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn)
     (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx <
     LENGTH bb'.bb_instructions` by
    (qpat_x_assum `DROP _ bb'.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  qexists `id` >> simp[] >>
  qpat_x_assum `DROP _ bb'.bb_instructions = _` (mp_tac o AP_TERM ``HD : instruction list -> instruction``) >>
  simp[HD_DROP]
QED

Theorem fmp_restore_lowered_run:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx < LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) /\
  FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,idx) = SOME target /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  t.vs_current_bb = bb.bb_label /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx /\
  lookup_var target t = SOME value ==>
  (!fuel. fmp_target_run fuel C' name t 1
    ((update_var runner value t) with vs_inst_idx := SUC t.vs_inst_idx)) /\
  ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    t.vs_inst_idx < LENGTH bb'.bb_instructions /\
    (EL t.vs_inst_idx bb'.bb_instructions).inst_opcode = ASSIGN
Proof
  rpt gen_tac >> disch_tac >>
  `?bb' id.
     lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
     t.vs_inst_idx < LENGTH bb'.bb_instructions /\
     EL t.vs_inst_idx bb'.bb_instructions =
       mk_inst id ASSIGN [Var target] [runner]` by
    metis_tac[fmp_restore_lowered_code] >>
  metis_tac[fmp_restore_target_run]
QED

Theorem fmp_restore_unlowered_run_zero:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
           (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx <= LENGTH bb.bb_instructions /\
  t.vs_current_bb = lbl /\
  t.vs_inst_idx = idx ==>
  !fuel. fmp_target_run fuel C' name t 0 t
Proof
  strip_tac >> drule_all fmp_stage_unlowered >> strip_tac >>
  irule fmp_restore_target_run_zero >> metis_tac[]
QED

(* In particular this covers user PARAM instructions before the root. *)
Theorem fmp_restore_kept_run_zero:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ inst = EL idx bb.bb_instructions /\
  ~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM] /\
  pre_fmp_opcode inst.inst_opcode /\
  t.vs_current_bb = lbl /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx ==>
  !fuel. fmp_target_run fuel C' name t 0 t
Proof
  strip_tac >> drule_all fmp_stage_kept_inst >> strip_tac >>
  irule fmp_restore_target_run_zero >>
  qexistsl [`bb'`, `fn'`] >> simp[] >>
  qpat_x_assum `_ + _ < LENGTH bb'.bb_instructions` mp_tac >>
  decide_tac
QED
