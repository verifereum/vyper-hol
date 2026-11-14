Theory readonlyInvokeCopyFwdHistoryStackAlignment
Ancestors
  readonlyInvokeCopyFwdHistoryPhase o1LowerDloadOccurrence
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdProtectionOrigin
  finite_map list pred_set

Definition ricf_phase_push_def:
  ricf_phase_push f ledger = MAP (\(p,pre). (p,f::pre)) ledger
End

Definition ricf_phase_pop_def:
  ricf_phase_pop ledger =
    MAP (\(p,pre). (p,TL pre)) (FILTER (\(p,pre). pre <> []) ledger)
End

Theorem ricf_phase_entry_call:
  ricf_phase_entry vs C ctx0 log stk PG G tn caller s a U B (p,pre) /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 ==>
  ricf_phase_entry vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1 n
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (p,<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre)
Proof
  simp[ricf_phase_entry_def] >> rpt strip_tac
  >- (irule ricf_history_cursor_call >> metis_tac[])
  >> Cases_on `pre` >> gvs[]
QED

Theorem ricf_source_ledger_call:
  ricf_source_ledger vs C ctx0 log stk PG G tn caller callinst s n a U B HP H ledger /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_source_ledger vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
    B (MAP (op_prov H) ops) FEMPTY
    (ricf_phase_push
      <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ledger)
Proof
  simp[ricf_source_ledger_def, ricf_phase_push_def, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac
  >- (irule occ_frame_reachable_call >> metis_tac[]) >>
  gvs[MEM_MAP] >> rename1 `MEM entry ledger` >>
  Cases_on `entry` >> gvs[] >>
  irule ricf_phase_entry_call >> metis_tac[]
QED

Theorem ricf_history_cursor_endpoint_owners:
  ricf_history_cursor vs C ctx0 log p pre PG G tn fn s ==>
  FST p.rpe_dst = p.rpe_owner /\ FST p.rpe_src = p.rpe_owner
Proof
  simp[ricf_history_cursor_def, ricf_history_origin_def,
       ricf_source_copy_payload_def] >> metis_tac[]
QED

Theorem ricf_phase_entry_return:
  ricf_phase_entry vs C ctx0 log (f::stk) PG G tn fn s a (u::U) B (p,f::pre) /\
  p.rpe_owner <> a /\ active_inst fn inst s /\
  step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' ==>
  ricf_phase_entry vs C ctx0 log stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    u.of_owner U (DRESTRICT B {id | FST id <> a}) (p,pre)
Proof
  simp[ricf_phase_entry_def] >> rpt strip_tac
  >- (irule ricf_history_cursor_return >> metis_tac[])
  >- (Cases_on `pre` >> gvs[])
  >- (drule ricf_history_cursor_endpoint_owners >> simp[FLOOKUP_DRESTRICT])
  >> drule ricf_history_cursor_endpoint_owners >> simp[FLOOKUP_DRESTRICT]
QED

Theorem ricf_source_ledger_return:
  ricf_source_ledger vs C ctx0 log (f::stk) PG G tn fn inst s n a (u::U) B HP H ledger /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_source_ledger vs C ctx0 log stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
    (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
    (ricf_phase_pop ledger)
Proof
  simp[ricf_source_ledger_def] >> strip_tac >>
  conj_tac >- (irule occ_frame_reachable_ret >> metis_tac[]) >>
  drule occ_frame_reachable_owner_fresh >> strip_tac >>
  gvs[ricf_phase_pop_def, EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> rename1 `MEM entry ledger` >>
  Cases_on `entry` >> gvs[] >> rename1 `MEM (p,pre) ledger` >>
  Cases_on `pre` >> gvs[] >>
  `ricf_phase_entry vs C ctx0 log (f::stk) PG G tn fn s a (u::U) B (p,h::t)`
    by metis_tac[] >>
  `h = f` by fs[ricf_phase_entry_def] >>
  qpat_x_assum `h = f` SUBST_ALL_TAC >>
  irule ricf_phase_entry_return >>
  `p.rpe_owner <> a` suffices_by metis_tac[] >>
  fs[ricf_phase_entry_def] >>
  `MEM (EL (LENGTH t) (u::U)).of_owner (MAP (\v. v.of_owner) (u::U))`
    by (simp[MEM_MAP] >> qexists_tac `EL (LENGTH t) (u::U)` >>
        `LENGTH t < LENGTH (u::U)` by simp[] >>
        metis_tac[EL_MEM, MEM]) >>
  qpat_assum `!u'. a = u'.of_owner ==> _` (qspec_then `u` assume_tac) >>
  gvs[ALL_DISTINCT, MEM_MAP] >> metis_tac[]
QED

Theorem ricf_phase_ranges_push_current[simp]:
  ricf_phase_ranges 0 (ricf_phase_push f ledger) = {}
Proof
  Induct_on `ledger` >> simp[ricf_phase_push_def] >>
  Cases_on `h` >> simp[ricf_phase_ranges_cons, GSYM ricf_phase_push_def]
QED

Theorem ricf_phase_ranges_push:
  ricf_phase_ranges (SUC depth) (ricf_phase_push f ledger) =
  ricf_phase_ranges depth ledger
Proof
  Induct_on `ledger` >> simp[ricf_phase_push_def] >> Cases_on `h` >>
  simp[ricf_phase_ranges_cons, GSYM ricf_phase_push_def]
QED

Theorem ricf_phase_ranges_pop:
  ricf_phase_ranges depth (ricf_phase_pop ledger) =
  ricf_phase_ranges (SUC depth) ledger
Proof
  Induct_on `ledger` >> simp[ricf_phase_pop_def] >> Cases_on `h` >>
  rename1 `(p,pre)` >> Cases_on `pre` >>
  simp[ricf_phase_ranges_cons, GSYM ricf_phase_pop_def]
QED

Theorem ricf_phase_stack_ranges_push:
  ricf_phase_stack_ranges (f::stk) (ricf_phase_push f ledger) =
  ricf_phase_ranges 0 ledger :: ricf_phase_stack_ranges stk ledger
Proof
  simp[ricf_phase_stack_ranges_def, listTheory.GENLIST_CONS,
       combinTheory.o_DEF, ricf_phase_ranges_push]
QED

Theorem ricf_phase_stack_ranges_pop:
  ricf_phase_stack_ranges stk (ricf_phase_pop ledger) =
  TL (ricf_phase_stack_ranges (f::stk) ledger)
Proof
  simp[ricf_phase_stack_ranges_def, listTheory.GENLIST_CONS,
       combinTheory.o_DEF, ricf_phase_ranges_pop]
QED

(* Singleton prefixes are the matching anchor return, not a nested readonly
   return.  Current entries are discarded by pop, even if they have the same
   numeric endpoints as an older activation. *)
Theorem ricf_phase_pop_cons[simp]:
  ricf_phase_pop ((p,[])::ledger) = ricf_phase_pop ledger /\
  ricf_phase_pop ((p,f::pre)::ledger) = (p,pre)::ricf_phase_pop ledger
Proof
  simp[ricf_phase_pop_def]
QED

Theorem ricf_phase_pop_anchor[simp]:
  ricf_phase_pop [(p,[f])] = [(p,[])]
Proof
  simp[ricf_phase_pop_def]
QED
