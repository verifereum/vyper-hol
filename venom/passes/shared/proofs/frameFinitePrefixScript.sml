(* A run's GAS events up to and including its n-th one, as a derivation that
   needs no termination.  The run reaches a GAS instruction, possibly inside
   INVOKE callees, after completed steps and blocks; each completed piece
   carries some fuel that completes it, and the events it records there.
   Nothing after the last GAS instruction is executed, so the derivation
   exists even when the run later errors, runs out of fuel or never ends. *)
Theory frameFinitePrefix
Ancestors frameGasEvents gasEvents gasEventsFuel venomExecSemantics venomState venomInst
  list rich_list arithmetic

Inductive finite_prefix:
[~gas:]
  (!C owner bb s i.
    get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = GAS ==>
    finite_block_prefix C owner bb s [(owner,i.inst_id)])
[~invoke:]
  (!C owner bb s i name ops fn args cs es.
    get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = INVOKE /\
    decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    finite_run_prefix C fn cs es ==>
    finite_block_prefix C owner bb s es)
[~next:]
  (!C owner bb s i k post es.
    get_instruction bb s.vs_inst_idx = SOME i /\
    ~is_terminator i.inst_opcode /\ step_inst k C i s = OK post /\
    finite_block_prefix C owner bb
      (post with vs_inst_idx := SUC s.vs_inst_idx) es ==>
    finite_block_prefix C owner bb s (gas_events_step k C owner i s ++ es))
[~run_here:]
  (!C fn s bb phi es.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    finite_block_prefix C fn.fn_name bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) es ==>
    finite_run_prefix C fn s es)
[~run_next:]
  (!C fn s bb phi k post es.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    exec_block k C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      OK post /\ ~post.vs_halted /\
    finite_run_prefix C fn post es ==>
    finite_run_prefix C fn s
      (gas_events_block k C fn.fn_name bb
         (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++ es))
End

(* ===== Source: a run with at least n events has a prefix of n events ===== *)

Theorem gas_events_take_prefix:
  (!fuel C owner i s. !n bb.
    0 < n /\ n <= LENGTH (gas_events_step fuel C owner i s) /\
    get_instruction bb s.vs_inst_idx = SOME i ==>
    finite_block_prefix C owner bb s (TAKE n (gas_events_step fuel C owner i s))) /\
  (!fuel C owner bb s. !n.
    0 < n /\ n <= LENGTH (gas_events_block fuel C owner bb s) ==>
    finite_block_prefix C owner bb s (TAKE n (gas_events_block fuel C owner bb s))) /\
  (!fuel C fn s. !n.
    0 < n /\ n <= LENGTH (gas_events_blocks fuel C fn s) ==>
    finite_run_prefix C fn s (TAKE n (gas_events_blocks fuel C fn s)))
Proof
  ho_match_mp_tac gas_events_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume gas_events_take_prefix[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode = GAS`
  >- (gvs[gas_events_step_def] >> `n = 1` by decide_tac >> gvs[] >>
      irule finite_prefix_gas >> simp[]) >>
  gvs[gas_events_step_def] >> BasicProvers.every_case_tac >> gvs[] >>
  irule finite_prefix_invoke >> metis_tac[]
QED

Resume gas_events_take_prefix[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- gvs[Once gas_events_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >> gvs[] >>
  Cases_on `n <= LENGTH (gas_events_step fuel C owner i s)`
  >- (simp[Once gas_events_block_def, TAKE_APPEND1] >>
      first_x_assum irule >> simp[]) >>
  qpat_x_assum `n <= LENGTH (gas_events_block _ _ _ _ _)` mp_tac >>
  simp[Once gas_events_block_def] >>
  Cases_on `step_inst fuel C i s` >> simp[] >>
  rename1 `step_inst fuel C i s = OK post` >>
  Cases_on `is_terminator i.inst_opcode` >> simp[] >> strip_tac >>
  simp[Once gas_events_block_def, TAKE_APPEND2] >>
  irule finite_prefix_next >> simp[] >>
  first_x_assum irule >> simp[]
QED

Resume gas_events_take_prefix[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel`
  >- (`gas_events_blocks 0 C fn s = []` by simp[Once gas_events_blocks_def] >>
      gvs[]) >>
  rename1 `gas_events_blocks (SUC f) C fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (`gas_events_blocks (SUC f) C fn s = []` by
        simp[Once gas_events_blocks_def] >> gvs[]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  TRY (`gas_events_blocks (SUC f) C fn s = []` by
         simp[Once gas_events_blocks_def] >> gvs[] >> NO_TAC) >>
  rename1 `eval_phis _ _ = OK sphi` >> gvs[] >>
  qpat_x_assum `n <= LENGTH (gas_events_blocks _ _ _ _)` mp_tac >>
  drule_all gas_events_blocks_at >>
  disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `n <= LENGTH (gas_events_block f C fn.fn_name bb
    (sphi with vs_inst_idx := phi_prefix_length bb.bb_instructions))`
  >- (strip_tac >> simp[TAKE_APPEND1] >>
      irule finite_prefix_run_here >> simp[] >>
      first_x_assum irule >> simp[]) >>
  Cases_on `exec_block f C bb
    (sphi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> simp[] >> strip_tac >>
  simp[TAKE_APPEND2] >>
  irule finite_prefix_run_next >> simp[] >>
  first_x_assum irule >> simp[]
QED

Finalise gas_events_take_prefix

Theorem gas_events_blocks_prefix:
  0 < n /\ n <= LENGTH (gas_events_blocks fuel C fn s) ==>
  finite_run_prefix C fn s (TAKE n (gas_events_blocks fuel C fn s))
Proof
  metis_tac[cj 3 gas_events_take_prefix]
QED

(* ===== Target: a prefix's events are a prefix of the run's at large fuel ===== *)

Theorem finite_prefix_realizable:
  (!C owner bb s es. finite_block_prefix C owner bb s es ==>
    ?m. !m'. m <= m' ==> ?rest. gas_events_block m' C owner bb s = es ++ rest) /\
  (!C fn s es. finite_run_prefix C fn s es ==>
    ?m. !m'. m <= m' ==> ?rest. gas_events_blocks m' C fn s = es ++ rest)
Proof
  ho_match_mp_tac finite_prefix_ind >> rpt conj_tac
  >- (rpt strip_tac >> qexists `0` >> rpt strip_tac >>
      simp[Once gas_events_block_def, gas_events_step_def])
  >- (rpt strip_tac >> qexists `m` >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[Once gas_events_block_def, gas_events_step_def])
  >- suspend "next"
  >- (rpt strip_tac >> qexists `SUC m` >> Cases >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      simp[Once gas_events_blocks_def])
  >> suspend "run_next"
QED

Resume finite_prefix_realizable[next]:
  rpt strip_tac >> qexists `k + m` >> rpt strip_tac >>
  `step_inst m' C i s = OK post /\
   gas_events_step m' C owner i s = gas_events_step k C owner i s` by
    (qspecl_then [`k`, `C`, `owner`, `i`, `s`] mp_tac
       (cj 1 gas_events_fuel_extension) >>
     disch_then (qspec_then `m'` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `m'` mp_tac) >> simp[] >> strip_tac >>
  drule_all gas_events_block_nonterminator >>
  disch_then (qspec_then `owner` SUBST1_TAC) >> simp[]
QED

Resume finite_prefix_realizable[run_next]:
  rpt strip_tac >> rename1 `~post.vs_halted` >>
  qexists `SUC (k + m)` >> Cases >> simp[] >> strip_tac >>
  rename1 `k + m <= m2` >>
  qabbrev_tac `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `exec_block m2 C bb p = OK post /\
   gas_events_block m2 C fn.fn_name bb p = gas_events_block k C fn.fn_name bb p` by
    (qspecl_then [`k`, `C`, `fn.fn_name`, `bb`, `p`] mp_tac
       (cj 2 gas_events_fuel_extension) >>
     disch_then (qspec_then `m2` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `m2` mp_tac) >> simp[] >> strip_tac >>
  simp[Once gas_events_blocks_def]
QED

Finalise finite_prefix_realizable

Theorem finite_run_prefix_realizable:
  finite_run_prefix C fn s es ==>
  ?k. !k'. k <= k' ==> ?rest. gas_events_blocks k' C fn s = es ++ rest
Proof
  metis_tac[cj 2 finite_prefix_realizable]
QED

val _ = export_theory();
