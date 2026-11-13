Theory readonlyInvokeCopyFwdHeterogeneousMapOrigins
Ancestors
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdOperationalMapOrigins
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryStackAlignment
  readonlyInvokeCopyFwdProtection readonlyInvokeCopyFwdReadonlyReach
  o1LowerDloadOccurrence ptrDiscipline venomExecSemantics venomState
  finite_map list rich_list pred_set arithmetic

Definition ricf_heterogeneous_map_origins_def:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites <=>
    !key tr. FLOOKUP sites key = SOME tr ==>
      ?ctxP logP. ricf_aligned_translation_origin vs C ctxP logP
        stk PG G tn fn inst s U B key tr
End

(* Saved maps keep live exit histories. Their anchor is older than the
   saved frame, so returning that frame cannot exhaust its translations. *)
Definition ricf_heterogeneous_saved_map_origins_def:
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps <=>
    LENGTH maps = LENGTH stk /\ LENGTH U = LENGTH stk /\
    (!j key tr. j < LENGTH stk /\ FLOOKUP (EL j maps) key = SOME tr ==>
      ?ctxP logP p pre anchor tail atn.
        SUC j <= LENGTH pre /\
        ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U B
          key tr p pre anchor tail atn)
End

Theorem ricf_heterogeneous_map_origins_empty[simp]:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B FEMPTY
Proof
  simp[ricf_heterogeneous_map_origins_def]
QED

Theorem ricf_heterogeneous_saved_map_origins_nil[simp]:
  ricf_heterogeneous_saved_map_origins vs C [] PG G tn fn inst s [] B []
Proof
  simp[ricf_heterogeneous_saved_map_origins_def]
QED

Theorem ricf_heterogeneous_map_origins_update:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  ricf_aligned_translation_origin vs C ctxP logP stk PG G tn fn inst s U B key tr ==>
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B
    (sites |+ (key,tr))
Proof
  simp[ricf_heterogeneous_map_origins_def, FLOOKUP_UPDATE] >> strip_tac >>
  qx_gen_tac `lookup_key` >> qx_gen_tac `lookup_tr` >>
  Cases_on `lookup_key = key` >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem ricf_heterogeneous_map_origins_next:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_heterogeneous_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites
Proof
  rw[ricf_heterogeneous_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_next >> metis_tac[]
QED

Theorem ricf_heterogeneous_saved_map_origins_next:
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_heterogeneous_saved_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B maps
Proof
  rw[ricf_heterogeneous_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_next >> metis_tac[]
QED

Theorem ricf_heterogeneous_map_origins_block:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_heterogeneous_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B sites
Proof
  rw[ricf_heterogeneous_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_block >> metis_tac[]
QED

Theorem ricf_heterogeneous_saved_map_origins_block:
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_heterogeneous_saved_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B maps
Proof
  rw[ricf_heterogeneous_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_block >> metis_tac[]
QED

Theorem ricf_aligned_origin_sites_step[local]:
  ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U B
    key tr p pre anchor tail atn /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) key tr p pre anchor tail atn
Proof
  rw[ricf_aligned_origin_at_def] >> metis_tac[occurrence_sites_step_preserves]
QED

Theorem ricf_heterogeneous_map_origins_sites_step:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) sites
Proof
  rw[ricf_heterogeneous_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_sites_step >> metis_tac[]
QED

Theorem ricf_heterogeneous_saved_map_origins_sites_step:
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) maps
Proof
  rw[ricf_heterogeneous_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_sites_step >> metis_tac[]
QED

Theorem ricf_heterogeneous_map_origins_call:
  ricf_heterogeneous_map_origins vs C stk PG G tn caller callinst s U B sites /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ==>
  ricf_heterogeneous_map_origins vs C (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B sites
Proof
  rw[ricf_heterogeneous_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
    `anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_call >> metis_tac[]
QED

Theorem ricf_heterogeneous_saved_map_origins_call:
  ricf_heterogeneous_map_origins vs C stk PG G tn caller callinst s U B sites /\
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn caller callinst s U B maps /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ==>
  ricf_heterogeneous_saved_map_origins vs C (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B (sites::maps)
Proof
  rw[ricf_heterogeneous_saved_map_origins_def] >> Cases_on `j`
  >- (gvs[ricf_heterogeneous_map_origins_def] >>
      first_x_assum drule >> rw[ricf_aligned_translation_origin_def] >>
      qexistsl_tac [`ctxP`,`logP`,`p`,
        `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
        `anchor`,`tail`,`atn`] >> simp[] >>
      irule ricf_aligned_origin_call >> metis_tac[]) >>
  gvs[] >> rename1 `FLOOKUP (EL depth maps) key = SOME tr` >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`depth`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
    `anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_call >> metis_tac[]
QED

Theorem ricf_aligned_origin_restrict_owner[local]:
  ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U B
    key tr p pre anchor tail atn /\ p.rpe_owner <> a ==>
  ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U
    (DRESTRICT B {id | FST id <> a}) key tr p pre anchor tail atn
Proof
  simp[ricf_aligned_origin_at_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ricf_aligned_origin_owner_old[local]:
  ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U B
    key tr p pre anchor tail atn /\
  ALL_DISTINCT (a::MAP (\u. u.of_owner) U) ==>
  p.rpe_owner <> a
Proof
  rw[ricf_aligned_origin_at_def] >>
  `MEM p.rpe_owner (MAP (\u. u.of_owner) U)` by
    (simp[MEM_MAP] >> qexists_tac `EL (LENGTH pre) U` >> simp[EL_MEM]) >>
  fs[] >> metis_tac[]
QED

Theorem ricf_heterogeneous_saved_map_origins_return:
  ricf_heterogeneous_saved_map_origins vs C (f::stk) PG G tn fn rinst s
    (u::U) B (sites::maps) /\
  occ_frame_reachable vs C (f::stk) PG G tn fn rinst s n a (u::U) B HP H /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_heterogeneous_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) sites /\
  ricf_heterogeneous_saved_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) maps
Proof
  strip_tac >> drule occ_frame_reachable_owner_fresh >> strip_tac >>
  fs[ricf_heterogeneous_saved_map_origins_def] >>
  conj_tac
  >- (rw[ricf_heterogeneous_map_origins_def] >>
      qpat_x_assum `!j key tr. _` (qspecl_then [`0`,`key`,`tr`] mp_tac) >>
      simp[] >> strip_tac >>
      `p.rpe_owner <> a` by
        (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
         metis_tac[ricf_aligned_origin_owner_old]) >>
      Cases_on `pre` >> gvs[] >>
      rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (inner::rest) _ _ _` >>
      `inner = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
      gvs[] >>
      qexistsl_tac [`ctxP`,`logP`] >>
      simp[ricf_aligned_translation_origin_def] >>
      qexistsl_tac [`p`,`rest`,`anchor`,`tail`,`atn`] >>
      irule ricf_aligned_origin_restrict_owner >> simp[] >>
      drule_all ricf_aligned_origin_nested_return >>
      simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]) >>
  rw[ricf_heterogeneous_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`SUC j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  `p.rpe_owner <> a` by
        (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
         metis_tac[ricf_aligned_origin_owner_old]) >>
  Cases_on `pre` >> gvs[] >>
  rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (inner::rest) _ _ _` >>
  `inner = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
  gvs[] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`rest`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_restrict_owner >> simp[] >>
  drule_all ricf_aligned_origin_nested_return >>
      simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem ricf_heterogeneous_map_origins_selected_call:
  ricf_heterogeneous_map_origins vs C stk PG G tn caller callinst s U B sites /\
  ricf_history_cursor vs C ctx0 log p [] PG G tn caller s /\
  frame_reachable vs C stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  FLOOKUP s.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP s.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size) /\
  0 < p.rpe_size /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  a = p.rpe_owner /\ s.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx /\
  callinst = EL s.vs_inst_idx p.rpe_block.bb_instructions ==>
  ricf_heterogeneous_map_origins vs C
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (sites |+ ((p.rpe_db,p.rpe_size),(p.rpe_db,p.rpe_sb,p.rpe_size)))
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`ctxP` |-> `ctx0`, `logP` |-> `log`]
    (SPEC_ALL ricf_heterogeneous_map_origins_update)) >> conj_tac
  >- (irule ricf_heterogeneous_map_origins_call >> metis_tac[]) >>
  simp[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`p`,`[]`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>`,`stk`,`tn`] >>
  gvs[] >> irule ricf_aligned_origin_selected >> metis_tac[]
QED

Theorem ricf_heterogeneous_map_origins_return_classify:
  ricf_heterogeneous_map_origins vs C (f::stk) PG G tn fn rinst s
    (u::U) B sites /\
  occ_frame_reachable vs C (f::stk) PG G tn fn rinst s n a (u::U) B HP H /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  !key tr. FLOOKUP sites key = SOME tr ==>
    (?ctxP logP. ricf_aligned_translation_origin vs C ctxP logP stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
      (DRESTRICT B {id | FST id <> a}) key tr) \/
    (?ctxP logP p.
      key = (p.rpe_db,p.rpe_size) /\ tr = (p.rpe_db,p.rpe_sb,p.rpe_size) /\
      p.rpe_owner = u.of_owner /\
      ricf_history_cursor vs C ctxP logP p [] f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
Proof
  strip_tac >> drule occ_frame_reachable_owner_fresh >> strip_tac >>
  fs[ricf_heterogeneous_map_origins_def] >> rw[] >>
  qpat_x_assum `!key tr. _` (qspecl_then [`key`,`tr`] mp_tac) >>
  simp[] >> rw[ricf_aligned_translation_origin_def] >> Cases_on `pre`
  >- (`anchor = f /\ tail = stk` by fs[ricf_aligned_origin_at_def] >>
      gvs[] >> disj2_tac >> qexistsl_tac [`ctxP`,`logP`,`p`] >>
      `key = (p.rpe_db,p.rpe_size) /\ tr = (p.rpe_db,p.rpe_sb,p.rpe_size) /\
       p.rpe_owner = u.of_owner` by fs[ricf_aligned_origin_at_def] >> simp[] >>
      irule ricf_aligned_origin_matching_return >> metis_tac[]) >>
  rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (inner::rest) _ _ _` >>
  `p.rpe_owner <> a` by
        (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
         metis_tac[ricf_aligned_origin_owner_old]) >>
  `inner = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
  gvs[] >> disj1_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`rest`,`anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_restrict_owner >> simp[] >>
  drule_all ricf_aligned_origin_nested_return >>
      simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED
