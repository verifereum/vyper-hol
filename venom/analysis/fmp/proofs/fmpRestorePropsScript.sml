(* Conditional local restore contract. Static acceptance is NOT a proof of
 * semantic provenance coverage or of whole-program memory-reuse safety. *)
Theory fmpRestoreProps
Ancestors
  fmpLedgerProps fmpProvenanceProps fmpReclaimDefs fmpReclaimProps
  venomExecSemantics venomState rich_list list
  finite_map words

Theorem fmp_restore_partition:
  MAP (\r. r.fr_mark) regions = st.frs_stack /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  fmp_pop_target popped = SOME target ==>
  let ps = TAKE (LENGTH popped) regions in
  let ks = DROP (LENGTH popped) regions in
    regions = ps ++ ks /\ ps <> [] /\
    MAP (\r. r.fr_mark) ps = popped /\
    MAP (\r. r.fr_mark) ks = kept /\
    (LAST ps).fr_mark = target
Proof
  rpt strip_tac >>
  `popped <> []` by (Cases_on `popped` >> gvs[fmp_pop_target_def]) >>
  drule_all fmp_pop_at_certificate >> strip_tac >>
  simp[LET_THM] >>
  `MAP (\r. r.fr_mark) (TAKE (LENGTH popped) regions) = popped` by
    (simp[MAP_TAKE, TAKE_APPEND1]) >>
  `MAP (\r. r.fr_mark) (DROP (LENGTH popped) regions) = kept` by
    (simp[MAP_DROP, DROP_APPEND1]) >>
  `TAKE (LENGTH popped) regions <> []` by metis_tac[MAP] >>
  `target = LAST popped` by (Cases_on `popped` >> gvs[fmp_pop_target_def]) >>
  `regions <> []` by (Cases_on `regions` >> gvs[]) >>
  simp[] >>
  qspecl_then [`TAKE (LENGTH popped) regions`, `\r. r.fr_mark`] mp_tac LAST_MAP >>
  pure_asm_rewrite_tac [] >> simp[]
QED

Theorem fmp_restore_frame:
  lookup_var fv (update_var fv value s) = SOME value /\
  (!v. v <> fv ==> lookup_var v (update_var fv value s) = lookup_var v s) /\
  (update_var fv value s with vs_vars := s.vs_vars) = s /\
  (update_var fv value s).vs_memory = s.vs_memory /\
  (update_var fv value s).vs_fmp = s.vs_fmp
Proof
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem fmp_restore_assign:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var target] /\
  inst.inst_outputs = [fv] /\ lookup_var target s = SOME value ==>
    step_inst_base inst s = OK (update_var fv value s)
Proof
  simp[step_inst_base_def, eval_operand_def]
QED

(* The split formulation is also convenient for consumers which already carry
 * a concrete ledger partition. No uniqueness assumption is needed for framing
 * or for this LAST-selected target; freshness is needed only for the FMP var. *)
Theorem fmp_restore_ledger_split:
  fmp_ledger_ok (fn_insts fn) env s top (ps ++ ks) /\
  MAP (\r. r.fr_mark) ps = popped /\
  MAP (\r. r.fr_mark) ks = kept /\
  fmp_pop_target popped = SOME target /\
  ~MEM fv (MAP (\r. r.fr_mark) (ps ++ ks)) ==>
    lookup_var target s = SOME (n2w (LAST ps).fr_lo) /\
    fmp_ledger_ok (fn_insts fn) env
      (update_var fv (n2w (LAST ps).fr_lo) s) (LAST ps).fr_lo ks /\
    (LAST ps).fr_lo <= top /\
    EVERY (\r. (LAST ps).fr_lo <= r.fr_lo /\ r.fr_hi <= top) ps /\
    (!r a. MEM r ks /\ (LAST ps).fr_lo <= a /\ a < top ==>
      ~fmp_region_contains r a)
Proof
  strip_tac >>
  `ps <> []` by (Cases_on `ps` >> gvs[fmp_pop_target_def]) >>
  `target = LAST popped` by (Cases_on `popped` >> gvs[fmp_pop_target_def]) >>
  `target = (LAST ps).fr_mark` by
    (qspecl_then [`ps`, `\r. r.fr_mark`] mp_tac LAST_MAP >>
     pure_asm_rewrite_tac [] >> simp[]) >>
  `MEM (LAST ps) (ps ++ ks)` by metis_tac[LAST_MEM, MEM_APPEND] >>
  drule_all fmp_ledger_split >> strip_tac >>
  drule_all fmp_ledger_mark >> strip_tac >>
  simp[] >> conj_tac
  >- (irule fmp_ledger_update_fresh >> gvs[]) >>
  metis_tac[fmp_ledger_retained_disjoint]
QED

Theorem fmp_restore_popped_exclusion:
  fmp_ledger_ok (fn_insts fn) env s top (ps ++ ks) /\
  MAP (\r. r.fr_mark) ps = popped /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  fmp_base_covers env prov /\
  fmp_escape_covers (fn_insts fn) env escaped /\
  fmp_capture_covers fn live p st.frs_captures capProtect ==>
    EVERY (\r. ~fmp_protected prov
      (live_vars_at live (FST p) (SND p)) escaped capProtect r.fr_site) ps
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM r (ps ++ ks)` by simp[] >>
  `MEM r.fr_mark popped` by (gvs[MEM_MAP] >> metis_tac[]) >>
  drule_all fmp_ledger_mark >> strip_tac >>
  metis_tac[fmp_pop_excludes_protected]
QED

(* Restore at the exact production point. The concrete ledger and the three
 * semantic-coverage assumptions are supplied by the consumer, NOT inferred
 * from fmp_reclaim_plan_ok. The frame theorem above supplies the remaining
 * state projections uniformly, without repeating the contract hypotheses. *)
Theorem fmp_restore_contract:
  fmp_ledger_ok (fn_insts fn) env s top regions /\
  MAP (\r. r.fr_mark) regions = st.frs_stack /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  fmp_pop_target popped = SOME target /\
  ~MEM fv (MAP (\r. r.fr_mark) regions) /\
  fmp_base_covers env prov /\
  fmp_escape_covers (fn_insts fn) env escaped /\
  fmp_capture_covers fn live p st.frs_captures capProtect ==>
  let ps = TAKE (LENGTH popped) regions in
  let ks = DROP (LENGTH popped) regions in
  let newtop = (LAST ps).fr_lo in
  let s' = update_var fv (n2w newtop) s in
    lookup_var target s = SOME (n2w newtop) /\
    MAP (\r. r.fr_mark) ks = kept /\
    fmp_ledger_ok (fn_insts fn) env s' newtop ks /\
    newtop <= top /\
    EVERY (\r. newtop <= r.fr_lo /\ r.fr_hi <= top) ps /\
    (!r a. MEM r ks /\ newtop <= a /\ a < top ==>
      ~fmp_region_contains r a) /\
    EVERY (\r. ~fmp_protected prov
      (live_vars_at live (FST p) (SND p)) escaped capProtect r.fr_site) ps
Proof
  strip_tac >> drule_all fmp_restore_partition >>
  simp[LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `LAST ps` >>
  qmatch_goalsub_abbrev_tac `fmp_ledger_ok _ _ _ _ ks` >>
  `regions = ps ++ ks` by simp[Abbr `ps`, Abbr `ks`] >>
  `fmp_ledger_ok (fn_insts fn) env s top (ps ++ ks)` by metis_tac[] >>
  `~MEM fv (MAP (\r. r.fr_mark) (ps ++ ks))` by metis_tac[] >>
  drule_all fmp_restore_ledger_split >> strip_tac >>
  simp[] >> irule fmp_restore_popped_exclusion >>
  metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpRestoreProps");
