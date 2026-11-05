(* Definition locations and paths for OFFSET liveness. *)
Theory fnBlockPlanStaticOffsetLive
Ancestors
  fnFrameStepsRevertForward venomExecProofs rich_list list stackPlanGen venomWf pair

Theorem ready_output_location_unique:
  !fn db k ub j v.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ j < LENGTH ub.bb_instructions /\
    MEM v (EL j ub.bb_instructions).inst_outputs ==>
    db = ub /\ k = j
Proof
  rpt strip_tac >>
  `ssa_form fn /\ fn_inst_ids_distinct fn` by
    gvs[codegen_ready_fn_def, wf_function_def] >>
  drule_all ssa_output_location >> strip_tac >>
  metis_tac[PAIR_EQ]
QED

Theorem ready_output_available:
  !fn db k ub uopt v.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    def_available_at fn ub uopt v ==>
    fn_dominates fn db.bb_label ub.bb_label /\
    (ub = db ==> !use. uopt = SOME use ==>
      ?j. k < j /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = use)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `?p. p < LENGTH def_bb.bb_instructions /\
       EL p def_bb.bb_instructions = def_inst` by metis_tac[MEM_EL] >>
  `db = def_bb /\ k = p` by
    (irule ready_output_location_unique >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  `i < LENGTH db.bb_instructions` by decide_tac >>
  `k = i` by (irule (cj 2 ready_output_location_unique) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem fn_path_last_visit:
  !path fn d. is_fn_path fn path /\ MEM d path ==>
    ?tail. is_fn_path fn (d :: tail) /\
           LAST (d :: tail) = LAST path /\ ~MEM d tail
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (a :: rest)` >> strip_tac >>
  Cases_on `MEM d rest`
  >- (`is_fn_path fn rest` by
        (Cases_on `rest` >> gvs[is_fn_path_def]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `tail` >> Cases_on `rest` >> gvs[]) >>
  `d = a` by gvs[] >> qexists_tac `rest` >> simp[]
QED

Theorem fn_path_member_reachable:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\ MEM lbl path ==>
    fn_reachable fn lbl
Proof
  rpt strip_tac >> drule_all is_fn_path_prefix >> strip_tac >>
  `RTC (fn_cfg_edge fn) (HD path) lbl` by
    (drule is_fn_path_rtc >> simp[]) >>
  gvs[fn_reachable_def] >>
  metis_tac[relationTheory.RTC_RTC]
QED

Theorem fn_dominates_last_visit:
  !fn d n. fn_dominates fn d n ==>
    ?tail. is_fn_path fn (d :: tail) /\ LAST (d :: tail) = n /\
           ~MEM d tail /\ EVERY (fn_reachable fn) (d :: tail)
Proof
  rpt strip_tac >>
  `fn_reachable fn n` by gvs[fn_dominates_def] >>
  `?entry. fn_entry_label fn = SOME entry /\
     RTC (fn_cfg_edge fn) entry n` by gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM d path` by (gvs[fn_dominates_def] >> metis_tac[]) >>
  drule_all fn_path_last_visit >> strip_tac >>
  qexists_tac `tail` >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule fn_path_member_reachable >>
  qexists_tac `d :: tail` >> simp[] >>
  metis_tac[fn_dominates_dom_reachable]
QED

Theorem ready_output_other_location:
  !fn db k v ub j.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ j < LENGTH ub.bb_instructions /\
    (db <> ub \/ k <> j) ==>
    ~MEM v (EL j ub.bb_instructions).inst_outputs
Proof
  metis_tac[ready_output_location_unique]
QED
