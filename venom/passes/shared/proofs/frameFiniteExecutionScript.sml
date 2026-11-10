Theory frameFiniteExecution
Ancestors venomExecSemantics venomState venomInst arithmetic

(* Fuel-free derivations of successful execution.  Propagation rules exclude
   both Error and OK; OK has its own sequencing rules. *)
Inductive finite_step:
[~base:]
  (!C i s r. i.inst_opcode <> INVOKE /\ step_inst_base i s = r /\
    (!e. r <> Error e) ==> finite_step C i s r)
[~invoke_return:]
  (!C i s name ops fn args cs ret post out.
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    finite_run C fn cs (IntRet ret post) /\
    bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s post)) = SOME out ==>
    finite_step C i s (OK out))
[~invoke_exit:]
  (!C i s name ops fn args cs r.
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    finite_run C fn cs r /\
    ((?post. r = Halt post) \/ (?a post. r = Abort a post)) ==>
    finite_step C i s r)
[~block_term:]
  (!C bb s i post.
    get_instruction bb s.vs_inst_idx = SOME i /\
    finite_step C i s (OK post) /\ is_terminator i.inst_opcode ==>
    finite_block C bb s (if post.vs_halted then Halt post else OK post))
[~block_next:]
  (!C bb s i post r.
    get_instruction bb s.vs_inst_idx = SOME i /\
    finite_step C i s (OK post) /\ ~is_terminator i.inst_opcode /\
    finite_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx) r ==>
    finite_block C bb s r)
[~block_exit:]
  (!C bb s i r.
    get_instruction bb s.vs_inst_idx = SOME i /\ finite_step C i s r /\
    (!post. r <> OK post) ==> finite_block C bb s r)
[~run_next:]
  (!C fn s bb phi post r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    finite_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) (OK post) /\
    ~post.vs_halted /\ finite_run C fn post r ==> finite_run C fn s r)
[~run_halt:]
  (!C fn s bb phi post.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    finite_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) (OK post) /\ post.vs_halted ==>
    finite_run C fn s (Halt post))
[~run_exit:]
  (!C fn s bb phi r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    finite_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) r /\
    (!post. r <> OK post) ==> finite_run C fn s r)
End

Theorem finite_execution_nonerror:
  (!C i s r. finite_step C i s r ==> !e. r <> Error e) /\
  (!C bb s r. finite_block C bb s r ==> !e. r <> Error e) /\
  (!C fn s r. finite_run C fn s r ==> !e. r <> Error e)
Proof
  ho_match_mp_tac finite_step_ind >> rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs()]
QED

Theorem finite_execution_realizable:
  (!C i s r. finite_step C i s r ==>
    ?n. !k. n <= k ==> step_inst k C i s = r) /\
  (!C bb s r. finite_block C bb s r ==>
    ?n. !k. n <= k ==> exec_block k C bb s = r) /\
  (!C fn s r. finite_run C fn s r ==>
    ?n. !k. n <= k ==> run_blocks k C fn s = r)
Proof
  ho_match_mp_tac finite_step_ind >> rpt conj_tac
  >- (rpt strip_tac >> qexists_tac `0` >> simp[step_inst_def])
  >- (rpt strip_tac >> qexists_tac `n` >> simp[step_inst_def])
  >- (rpt strip_tac >> qexists_tac `n` >> simp[step_inst_def])
  >- (rpt strip_tac >> qexists_tac `n` >> simp[Once exec_block_def])
  >- (rpt strip_tac >> qexists_tac `n + n'` >> rpt strip_tac >>
      `n <= k /\ n' <= k` by decide_tac >>
      simp[Once exec_block_def])
  >- (rpt strip_tac >> qexists_tac `n` >> rpt strip_tac >>
      simp[Once exec_block_def] >> Cases_on `r` >> gvs[])
  >- (rpt strip_tac >> qexists_tac `SUC (n + n')` >>
      Cases >> simp[] >> strip_tac >>
      `n <= n'' /\ n' <= n''` by decide_tac >>
      simp[Once run_blocks_def])
  >- (rpt strip_tac >> qexists_tac `SUC n` >>
      Cases >> simp[Once run_blocks_def])
  >> rpt strip_tac >> qexists_tac `SUC n` >>
  Cases >> simp[] >> strip_tac >> simp[Once run_blocks_def] >>
  Cases_on `r` >> gvs[]
QED

Theorem finite_execution_complete:
  (!fuel C i s. (!e. step_inst fuel C i s <> Error e) ==>
    finite_step C i s (step_inst fuel C i s)) /\
  (!fuel C bb s. (!e. exec_block fuel C bb s <> Error e) ==>
    finite_block C bb s (exec_block fuel C bb s)) /\
  (!fuel C fn s. (!e. run_blocks fuel C fn s <> Error e) ==>
    finite_run C fn s (run_blocks fuel C fn s))
Proof
  ho_match_mp_tac run_defs_ind >> conj_tac
  >- suspend "step"
  >> conj_tac >- suspend "block"
  >> suspend "run"
QED

Resume finite_execution_complete[step]:
  rpt strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke i` >- fs[Once step_inst_def] >>
      PairCases_on `x` >>
      Cases_on `lookup_function x0 C.ctx_functions`
      >- fs[Once step_inst_def] >>
      rename1 `lookup_function x0 C.ctx_functions = SOME fn` >>
      Cases_on `eval_operands x1 s` >- fs[Once step_inst_def] >>
      rename1 `eval_operands x1 s = SOME args` >>
      Cases_on `setup_callee fn args s` >- fs[Once step_inst_def] >>
      rename1 `setup_callee fn args s = SOME cs` >>
      `!e. run_blocks fuel C fn cs <> Error e` by
        (spose_not_then strip_assume_tac >> fs[Once step_inst_def]) >>
      `finite_run C fn cs (run_blocks fuel C fn cs)` by metis_tac[] >>
      Cases_on `run_blocks fuel C fn cs` >>
      gvs[step_inst_def, AllCaseEqs()]
      >- (irule finite_step_invoke_exit >> simp[] >> metis_tac[])
      >- (irule finite_step_invoke_exit >> simp[] >> metis_tac[])
      >> Cases_on `bind_outputs i.inst_outputs i'.iret_values
           (adopt_return_fmp i' (merge_callee_state s v))` >> gvs[] >>
      irule finite_step_invoke_return >> simp[] >> metis_tac[])
  >> gvs[step_inst_def] >> irule finite_step_base >> simp[step_inst_def]
QED

Resume finite_execution_complete[block]:
  rpt strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- fs[Once exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `!e. step_inst fuel C inst s <> Error e` by
    (spose_not_then strip_assume_tac >> fs[Once exec_block_def]) >>
  `finite_step C inst s (step_inst fuel C inst s)` by metis_tac[] >>
  Cases_on `step_inst fuel C inst s` >> gvs[]
  >- (rename1 `step_inst fuel C inst s = OK post` >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (simp[Once exec_block_def] >>
          irule finite_step_block_term >> metis_tac[]) >>
      `!e. exec_block fuel C bb
        (post with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
        (qpat_x_assum `!e. exec_block fuel C bb s <> Error e` mp_tac >>
         simp[Once exec_block_def]) >>
      simp[Once exec_block_def] >> irule finite_step_block_next >>
      metis_tac[])
  >> simp[Once exec_block_def] >> irule finite_step_block_exit >>
  simp[] >> metis_tac[]
QED

Resume finite_execution_complete[run]:
  rpt strip_tac >> Cases_on `fuel` >- fs[Once run_blocks_def] >>
  rename1 `run_blocks (SUC n) C fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- fs[Once run_blocks_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK phi` >>
      `!e. exec_block n C bb (phi with vs_inst_idx :=
        phi_prefix_length bb.bb_instructions) <> Error e` by
        (spose_not_then strip_assume_tac >> fs[Once run_blocks_def]) >>
      `finite_block C bb (phi with vs_inst_idx :=
        phi_prefix_length bb.bb_instructions)
        (exec_block n C bb (phi with vs_inst_idx :=
          phi_prefix_length bb.bb_instructions))` by metis_tac[] >>
      Cases_on `exec_block n C bb (phi with vs_inst_idx :=
        phi_prefix_length bb.bb_instructions)` >> gvs[]
      >- (rename1 `exec_block n C bb _ = OK post` >>
          Cases_on `post.vs_halted`
          >- (simp[Once run_blocks_def] >> irule finite_step_run_halt >>
              metis_tac[]) >>
          `!e. run_blocks n C fn post <> Error e` by
            (qpat_x_assum `!e. run_blocks (SUC n) C fn s <> Error e` mp_tac >>
             simp[Once run_blocks_def]) >>
          simp[Once run_blocks_def] >> irule finite_step_run_next >>
          metis_tac[])
      >> simp[Once run_blocks_def] >> irule finite_step_run_exit >>
      simp[] >> metis_tac[])
  >> fs[Once run_blocks_def]
QED

Finalise finite_execution_complete

Theorem finite_step_iff:
  finite_step C i s r <=>
  ?n. step_inst n C i s = r /\ (!e. r <> Error e)
Proof
  eq_tac
  >- (strip_tac >> drule (cj 1 finite_execution_realizable) >>
      strip_tac >> qexists_tac `n` >> simp[] >>
      metis_tac[cj 1 finite_execution_nonerror])
  >> metis_tac[cj 1 finite_execution_complete]
QED

Theorem finite_block_iff:
  finite_block C bb s r <=>
  ?n. exec_block n C bb s = r /\ (!e. r <> Error e)
Proof
  eq_tac
  >- (strip_tac >> drule (cj 2 finite_execution_realizable) >>
      strip_tac >> qexists_tac `n` >> simp[] >>
      metis_tac[cj 2 finite_execution_nonerror])
  >> metis_tac[cj 2 finite_execution_complete]
QED

Theorem finite_run_iff:
  finite_run C fn s r <=>
  ?n. run_blocks n C fn s = r /\ (!e. r <> Error e)
Proof
  eq_tac
  >- (strip_tac >> drule (cj 3 finite_execution_realizable) >>
      strip_tac >> qexists_tac `n` >> simp[] >>
      metis_tac[cj 3 finite_execution_nonerror])
  >> metis_tac[cj 3 finite_execution_complete]
QED

val _ = export_theory();
