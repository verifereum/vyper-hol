Theory frameDecoratedEndpoints
Ancestors frameFiniteJointDecoration frameFiniteExecution frameJointTransition
  venomExecSemantics venomState venomInst list

(* The fields restored after a returning call, or retained by an ordinary
   instruction and a block edge. Mutable ghost maps deliberately do not occur. *)
Definition decoration_frame_def:
  decoration_frame (JointConfig stk PG G tn fn i s oms om hs h) =
    (stk,PG,fn,oms,hs)
End

Theorem decoration_consumes_frame:
  decoration_consumes C i q post qm ev qn ==>
  decoration_frame qn = decoration_frame q
Proof
  Cases_on `q` >> Cases_on `qm` >> Cases_on `qn` >>
  simp[decoration_consumes_def, resume_pending_def] >> rpt strip_tac >>
  gvs[joint_transition_cases, decoration_frame_def]
QED

Theorem decoration_block_frame:
  joint_transition C q (SOME (OriginBlock fuel post)) qn ==>
  decoration_frame qn = decoration_frame q
Proof
  Cases_on `q` >> Cases_on `qn` >>
  simp[joint_transition_cases, decoration_frame_def] >> metis_tac[]
QED

Theorem decorated_execution_frame:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    i.inst_opcode <> INVOKE ==> qe = q) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    ((?post. r = OK post) \/ (?ret send. r = IntRet ret send)) ==>
    decoration_frame qe = decoration_frame q) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    (!ret send. r = IntRet ret send ==>
    decoration_frame qe = decoration_frame q))
Proof
  ho_match_mp_tac decorated_step_strongind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      gvs[])
  >- (rpt strip_tac >> gvs[] >>
      drule decoration_consumes_frame >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      `i.inst_opcode <> INVOKE` by
        (drule (cj 1 decorated_execution_erases) >>
         simp[Once finite_step_cases] >> metis_tac[]) >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      drule decoration_block_frame >> metis_tac[])
  >> rpt strip_tac >> gvs[]
QED

Theorem decorated_execution_intret_endpoint:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    !ret send. r = IntRet ret send ==>
      qe = q /\ local_pending C qe (IntRet ret send)) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    !ret send. r = IntRet ret send ==>
      decoration_frame qe = decoration_frame q /\
      local_pending C qe (IntRet ret send)) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    !ret send. r = IntRet ret send ==>
      decoration_frame qe = decoration_frame q /\
      local_pending C qe (IntRet ret send))
Proof
  ho_match_mp_tac decorated_step_strongind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[decoration_at_def, local_pending_def] >>
      irule finite_step_base >> simp[])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> Cases_on `post.vs_halted` >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      drule decoration_consumes_frame >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      drule (cj 2 decorated_execution_frame) >> simp[] >>
      drule decoration_block_frame >> metis_tac[])
  >> rpt strip_tac >> gvs[]
QED

Definition decoration_finish_def:
  decoration_finish C r q <=> local_pending C q r \/
    ?post. r = Halt post /\ post.vs_halted /\ local_pending C q (OK post)
End

Theorem decorated_execution_finish:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    (!post. r <> OK post) ==> decoration_finish C r qe) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    decoration_finish C r qe) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    decoration_finish C r qe)
Proof
  ho_match_mp_tac decorated_step_strongind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[decoration_finish_def, local_pending_def, decoration_at_def] >>
      disj1_tac >> irule finite_step_base >> simp[])
  >- (rpt strip_tac >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      drule (cj 1 decorated_execution_frame) >> simp[] >> strip_tac >>
      drule (cj 1 decorated_execution_erases) >> strip_tac >>
      Cases_on `q` >> gvs[decoration_at_def] >>
      Cases_on `post.vs_halted` >>
      simp[decoration_finish_def, local_pending_def])
  >> rpt strip_tac >> gvs[decoration_finish_def] >> metis_tac[]
QED

Theorem decorated_step_pending_exit:
  decorated_step C i s r q n w qe d ==> pending_exit C q r qe
Proof
  simp[Once decorated_step_cases] >> rpt strip_tac
  >- (Cases_on `q` >> gvs[pending_exit_def, local_pending_def, decoration_at_def] >>
      disj1_tac >> irule finite_step_base >> simp[])
  >- (drule (cj 3 decorated_execution_intret_endpoint) >> simp[] >> strip_tac >>
      Cases_on `q` >> Cases_on `qc` >> Cases_on `qe` >>
      gvs[decoration_at_def, decoration_frame_def, joint_transition_cases,
          pending_exit_def, resume_pending_def] >> metis_tac[])
  >> drule (cj 3 decorated_execution_finish) >>
  simp[decoration_finish_def, pending_exit_def] >> metis_tac[]
QED

val _ = export_theory();
