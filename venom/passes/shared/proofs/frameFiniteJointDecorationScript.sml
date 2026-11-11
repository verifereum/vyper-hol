Theory frameFiniteJointDecoration
Ancestors frameFiniteJointEndpoints frameFiniteJointTrace frameFiniteExecution
  frameJointTransition frameJointTrace contextCodegenRel venomExecSemantics
  venomState venomInst list arithmetic

(* Paths contain destinations, not a duplicated starting observation. *)
Definition joint_segment_def:
  (joint_segment C q [] qe <=> qe = q) /\
  (joint_segment C q ((ev,q1)::w) qe <=>
    joint_transition C q ev q1 /\ joint_segment C q1 w qe)
End

Datatype:
  finite_decoration = FiniteDecoration num num (finite_decoration list)
End

Definition decoration_at_def:
  decoration_at fn i s (JointConfig stk PG G tn fn0 i0 s0 oms om hs h) <=>
    fn0 = fn /\ i0 = i /\ s0 = s /\ active_inst fn i s
End

Definition decoration_entry_def:
  decoration_entry fn s q <=> ?i. decoration_at fn i s q
End

Definition local_pending_def:
  local_pending C (JointConfig stk PG G tn fn i s oms om hs h) r <=>
    active_inst fn i s /\ i.inst_opcode <> INVOKE /\ finite_step C i s r
End

Definition resume_pending_def:
  resume_pending C (JointConfig stk PG G tn caller inv s oms om hs h) post qe <=>
    active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
    ?PGc Gc tnc callee ri sr omc hc ret send.
      qe = JointConfig
        (<|cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
        PGc Gc tnc callee ri sr (om::oms) omc (h::hs) hc /\
      local_pending C qe (IntRet ret send) /\
      bind_outputs inv.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state s send)) = SOME post
End

Definition pending_exit_def:
  pending_exit C owner r qe <=>
    (qe = owner /\ local_pending C qe r) \/
    (?post. r = OK post /\ resume_pending C owner post qe) \/
    (?post. r = Halt post /\ local_pending C qe (Halt post)) \/
    (?a post. r = Abort a post /\ local_pending C qe (Abort a post)) \/
    (?post. r = Halt post /\ post.vs_halted /\ local_pending C qe (OK post))
End

(* The two alternatives below consume a pending OK instruction.  In particular
   a call is still at its callee's IntRet endpoint before this edge. *)
Definition decoration_consumes_def:
  decoration_consumes C i q post qm ev qn <=>
    joint_transition C qm ev qn /\
    ((i.inst_opcode <> INVOKE /\ qm = q /\
      ?fuel. ev = SOME (OriginOrdinary fuel post)) \/
     (i.inst_opcode = INVOKE /\ resume_pending C q post qm /\
      ?fuel callee ri sr ret send.
        ev = SOME (OriginResume fuel callee ri sr ret send post)))
End

Inductive decorated_step:
[~base:]
  (!C i s r fn q n.
    decoration_at fn i s q /\ i.inst_opcode <> INVOKE /\
    step_inst_base i s = r /\ (!e. r <> Error e) ==>
    decorated_step C i s r q n [] q (FiniteDecoration n n []))
[~invoke_return:]
  (!C i s name ops fn args cs ret send post caller q n qc wc qe dc.
    decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
    decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    joint_transition C q NONE qc /\
    decorated_run C fn cs (IntRet ret send) qc (n+1) wc qe dc /\
    bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s send)) = SOME post ==>
    decorated_step C i s (OK post) q n ((NONE,qc)::wc) qe
      (FiniteDecoration n (n + LENGTH ((NONE,qc)::wc)) [dc]))
[~invoke_exit:]
  (!C i s name ops fn args cs r caller q n qc wc qe dc.
    decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
    decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    joint_transition C q NONE qc /\
    decorated_run C fn cs r qc (n+1) wc qe dc /\
    ((?post. r = Halt post) \/ (?a post. r = Abort a post)) ==>
    decorated_step C i s r q n ((NONE,qc)::wc) qe
      (FiniteDecoration n (n + LENGTH ((NONE,qc)::wc)) [dc]))
[~block_term:]
  (!C bb s i post fn q n w qe ds.
    decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    decorated_step C i s (OK post) q n w qe ds /\
    is_terminator i.inst_opcode ==>
    decorated_block C bb s (if post.vs_halted then Halt post else OK post)
      q n w qe (FiniteDecoration n (n+LENGTH w) [ds]))
[~block_next:]
  (!C bb s i post r fn q n ws qm ds ev qn wb qe db.
    decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    decorated_step C i s (OK post) q n ws qm ds /\
    ~is_terminator i.inst_opcode /\
    decoration_consumes C i q post qm ev qn /\
    decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
    decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
      r qn (n+LENGTH ws+1) wb qe db ==>
    decorated_block C bb s r q n (ws++[(ev,qn)]++wb) qe
      (FiniteDecoration n (n+LENGTH (ws++[(ev,qn)]++wb)) [ds;db]))
[~block_exit:]
  (!C bb s i r fn q n w qe ds.
    decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    decorated_step C i s r q n w qe ds /\ (!post. r <> OK post) ==>
    decorated_block C bb s r q n w qe
      (FiniteDecoration n (n+LENGTH w) [ds]))
[~run_next:]
  (!C fn s bb phi post r q n wb qm db fuel qn wr qe dr.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    decoration_entry fn
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
    decorated_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) (OK post) q n wb qm db /\
    ~post.vs_halted /\ local_pending C qm (OK post) /\
    (?stk PG G tn i si oms om hs h.
      qm = JointConfig stk PG G tn fn i si oms om hs h /\
      active_inst fn i si /\ is_terminator i.inst_opcode) /\
    joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
    decorated_run C fn post r qn (n+LENGTH wb+1) wr qe dr ==>
    decorated_run C fn s r q n (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe
      (FiniteDecoration n
        (n+LENGTH (wb++[(SOME (OriginBlock fuel post),qn)]++wr)) [db;dr]))
[~run_halt:]
  (!C fn s bb phi post q n w qe db.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    decoration_entry fn
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
    decorated_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) (OK post) q n w qe db /\
    post.vs_halted ==>
    decorated_run C fn s (Halt post) q n w qe
      (FiniteDecoration n (n+LENGTH w) [db]))
[~run_exit:]
  (!C fn s bb phi r q n w qe db.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    decoration_entry fn
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
    decorated_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) r q n w qe db /\
    (!post. r <> OK post) ==>
    decorated_run C fn s r q n w qe
      (FiniteDecoration n (n+LENGTH w) [db]))
End

(* Completeness, proved downstream, will quantify over arbitrary ghost fields
   of an active matching q and every absolute n.  Step, block and run finite
   derivations then yield w,qe,d. Blocks also require the actual lookup_block;
   runs require enters_block. No reachability or demand invariant is needed.
   Reachable prefixes are composed with joint_segment only afterwards. *)

Theorem decorated_execution_erases:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    finite_step C i s r) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    finite_block C bb s r) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    finite_run C fn s r)
Proof
  ho_match_mp_tac decorated_step_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule finite_step_base >> simp[])
  >- (rpt strip_tac >> irule finite_step_invoke_return >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_invoke_exit >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_block_term >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_block_next >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_block_exit >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_run_next >> metis_tac[])
  >- (rpt strip_tac >> irule finite_step_run_halt >> metis_tac[])
  >> rpt strip_tac >> irule finite_step_run_exit >> metis_tac[]
QED

Theorem joint_segment_append:
  !w q qm v qe. joint_segment C q w qm /\ joint_segment C qm v qe ==>
    joint_segment C q (w ++ v) qe
Proof
  Induct >> simp[joint_segment_def] >> rpt strip_tac >>
  PairCases_on `h` >> gvs[joint_segment_def] >> metis_tac[]
QED

Theorem decorated_execution_segment:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    joint_segment C q w qe) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    joint_segment C q w qe) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    joint_segment C q w qe)
Proof
  ho_match_mp_tac decorated_step_ind >> rpt strip_tac >>
  gvs[joint_segment_def, decoration_consumes_def] >>
  metis_tac[joint_segment_append, joint_segment_def]
QED

Theorem decorated_execution_interval:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    ?children. d = FiniteDecoration n (n+LENGTH w) children) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    ?children. d = FiniteDecoration n (n+LENGTH w) children) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    ?children. d = FiniteDecoration n (n+LENGTH w) children)
Proof
  ho_match_mp_tac decorated_step_ind >> rpt strip_tac >> simp[]
QED

Theorem decorated_invoke_child:
  decorated_step C i s r q n w qe d /\ i.inst_opcode = INVOKE ==>
  ?fn cs cr qc wc dc children.
    joint_transition C q NONE qc /\
    decorated_run C fn cs cr qc (n+1) wc qe dc /\
    w = (NONE,qc)::wc /\
    d = FiniteDecoration n (n+LENGTH w) [dc] /\
    dc = FiniteDecoration (n+1) (n+1+LENGTH wc) children
Proof
  simp[Once decorated_step_cases] >> rpt strip_tac >> gvs[] >>
  drule (cj 3 decorated_execution_interval) >> strip_tac >>
  `n+1+LENGTH wc = n+(LENGTH wc+1)` by decide_tac >>
  gvs[] >> metis_tac[]
QED

Theorem decorated_execution_ok_endpoint:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==> T) /\
  (!C bb s r q n w qe d.
    decorated_block C bb s r q n w qe d ==> !post fn i.
    r = OK post /\ decoration_at fn i s q ==>
    local_pending C qe (OK post) /\
    ?stk PG G tn ti si oms om hs h.
      qe = JointConfig stk PG G tn fn ti si oms om hs h /\
      active_inst fn ti si /\ is_terminator ti.inst_opcode) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==> T)
Proof
  ho_match_mp_tac decorated_step_strongind >> simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `post.vs_halted` >> gvs[] >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      Cases_on `q` >> gvs[decoration_at_def] >>
      qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[Once decorated_step_cases] >> rpt strip_tac >>
      gvs[local_pending_def, decoration_at_def] >>
      irule finite_step_base >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[decoration_entry_def] >> Cases_on `q` >>
      gvs[decoration_at_def] >> metis_tac[])
  >> rpt strip_tac >> gvs[]
QED

(* Constructor probes compose operational and structural rules; they do not
   postulate an undecorated callee or invent a terminal successor. *)
Theorem decorated_ordinary_sequence:
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK post /\
  joint_transition C q (SOME (OriginOrdinary fuel post)) qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
    r qn (n+1) wb qe db ==>
  decorated_block C bb s r q n
    ([(SOME (OriginOrdinary fuel post),qn)]++wb) qe
    (FiniteDecoration n (n+LENGTH ([(SOME (OriginOrdinary fuel post),qn)]++wb))
      [FiniteDecoration n n [];db])
Proof
  strip_tac >>
  `decorated_step C i s (OK post) q n [] q (FiniteDecoration n n [])` by
    (irule decorated_step_base >> simp[] >> metis_tac[]) >>
  drule_at Any decorated_step_block_next >>
  simp[decoration_consumes_def] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem decorated_returned_invoke_sequence:
  decoration_at caller i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = INVOKE /\ ~is_terminator i.inst_opcode /\
  decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  joint_transition C q NONE qc /\
  decorated_run C callee cs (IntRet ret send) qc (n+1) wc qm dc /\
  bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s send)) = SOME post /\
  resume_pending C q post qm /\
  joint_transition C qm (SOME (OriginResume fuel callee ri sr ret send post)) qn /\
  decoration_entry caller (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx) r qn
    (n+LENGTH ((NONE,qc)::wc)+1) wb qe db ==>
  decorated_block C bb s r q n
    (((NONE,qc)::wc)++[(SOME (OriginResume fuel callee ri sr ret send post),qn)]++wb)
    qe (FiniteDecoration n
      (n+LENGTH (((NONE,qc)::wc)++
        [(SOME (OriginResume fuel callee ri sr ret send post),qn)]++wb))
      [FiniteDecoration n (n+LENGTH ((NONE,qc)::wc)) [dc];db])
Proof
  strip_tac >>
  `decorated_step C i s (OK post) q n ((NONE,qc)::wc) qm
     (FiniteDecoration n (n+LENGTH ((NONE,qc)::wc)) [dc])` by
    (irule decorated_step_invoke_return >> metis_tac[]) >>
  drule_at Any decorated_step_block_next >>
  simp[decoration_consumes_def] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem decorated_callee_terminal_block:
  decoration_at caller i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  joint_transition C q NONE qc /\
  decorated_run C callee cs r qc (n+1) wc qe dc /\
  ((?post. r = Halt post) \/ (?a post. r = Abort a post)) ==>
  decorated_block C bb s r q n ((NONE,qc)::wc) qe
    (FiniteDecoration n (n+LENGTH ((NONE,qc)::wc))
      [FiniteDecoration n (n+LENGTH ((NONE,qc)::wc)) [dc]])
Proof
  strip_tac >>
  `decorated_step C i s r q n ((NONE,qc)::wc) qe
     (FiniteDecoration n (n+LENGTH ((NONE,qc)::wc)) [dc])` by
    (irule decorated_step_invoke_exit >> metis_tac[]) >>
  drule_at Any decorated_step_block_exit >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem decorated_block_run_sequence:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  decoration_entry fn
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
  decorated_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (OK post) q n wb qm db /\ ~post.vs_halted /\
  joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
  decorated_run C fn post r qn (n+LENGTH wb+1) wr qe dr ==>
  decorated_run C fn s r q n (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe
    (FiniteDecoration n
      (n+LENGTH (wb++[(SOME (OriginBlock fuel post),qn)]++wr)) [db;dr])
Proof
  strip_tac >>
  drule (cj 2 decorated_execution_ok_endpoint) >>
  gvs[decoration_entry_def] >> disch_then drule >> strip_tac >>
  drule_at Any decorated_step_run_next >>
  simp[decoration_entry_def] >> disch_then irule >> metis_tac[]
QED

val _ = export_theory();
