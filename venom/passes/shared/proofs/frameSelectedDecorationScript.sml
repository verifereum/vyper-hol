Theory frameSelectedDecoration
Ancestors frameFiniteJointDecoration frameFiniteExecution list arithmetic

(* The ambient path is never reselected.  Both the absolute start and the
   actual selected decoration are arguments, not hidden run-entry witnesses. *)
Definition selected_segment_def:
  selected_segment C q0 path n q w qe <=>
    ?pre suffix. path = pre ++ w ++ suffix /\ n = LENGTH pre /\
      joint_segment C q0 pre q /\ joint_segment C q w qe
End

Definition selected_run_def:
  selected_run C q0 path fn s r q n w qe d <=>
    decorated_run C fn s r q n w qe d /\
    selected_segment C q0 path n q w qe
End

Theorem joint_segment_split:
  !w q v qe. joint_segment C q (w ++ v) qe <=>
    ?qm. joint_segment C q w qm /\ joint_segment C qm v qe
Proof
  Induct >> simp[joint_segment_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[joint_segment_def] >> metis_tac[]
QED

Theorem joint_segment_endpoint_index:
  !w q qe suffix. joint_segment C q w qe ==>
    EL (LENGTH w) (q::MAP SND (w ++ suffix)) = qe
Proof
  Induct >> simp[joint_segment_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[joint_segment_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem selected_segment_indices:
  selected_segment C q0 path n q w qe ==>
  n + LENGTH w <= LENGTH path /\
  EL n (q0::MAP SND path) = q /\
  EL (n + LENGTH w) (q0::MAP SND path) = qe
Proof
  simp[selected_segment_def] >> rpt strip_tac >> gvs[]
  >- (qspecl_then [`pre`, `q0`, `q`, `w ++ suffix`] mp_tac
        joint_segment_endpoint_index >> simp[MAP_APPEND]) >>
  `joint_segment C q0 (pre ++ w) qe` by metis_tac[joint_segment_append] >>
  qspecl_then [`pre ++ w`, `q0`, `qe`, `suffix`] mp_tac
    joint_segment_endpoint_index >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem selected_segment_parts:
  selected_segment C q0 path n q (u ++ v) qe /\
  joint_segment C q u qm /\ joint_segment C qm v qe ==>
  selected_segment C q0 path n q u qm /\
  selected_segment C q0 path (n + LENGTH u) qm v qe
Proof
  simp[selected_segment_def] >> rpt strip_tac >> gvs[]
  >- (qexistsl [`pre`, `v ++ suffix`] >> simp[APPEND_ASSOC]) >>
  qexistsl [`pre ++ u`, `suffix`] >> simp[APPEND_ASSOC] >>
  metis_tac[joint_segment_append]
QED


Theorem selected_singleton_event:
  selected_segment C q0 path n q [(ev,qn)] qn ==>
  EL n (MAP FST path) = ev
Proof
  simp[selected_segment_def] >> strip_tac >> gvs[] >>
  simp[MAP_APPEND, EL_APPEND_EQN]
QED

Theorem selected_segment_edge:
  selected_segment C q0 path n q (u ++ ([(ev,qn)] ++ v)) qe /\
  joint_segment C q u qm /\ joint_transition C qm ev qn /\
  joint_segment C qn v qe ==>
  selected_segment C q0 path n q u qm /\
  selected_segment C q0 path (n + LENGTH u + 1) qn v qe /\
  n + LENGTH u < LENGTH path /\
  EL (n + LENGTH u) (MAP FST path) = ev /\
  EL (n + LENGTH u) (q0::MAP SND path) = qm /\
  EL (n + LENGTH u + 1) (q0::MAP SND path) = qn
Proof
  strip_tac >>
  `selected_segment C q0 path n q u qm /\
   selected_segment C q0 path (n + LENGTH u) qm ([(ev,qn)] ++ v) qe` by
    (irule selected_segment_parts >>
     goal_assum (drule_at Any) >> simp[joint_segment_def]) >>
  `selected_segment C q0 path (n + LENGTH u) qm [(ev,qn)] qn /\
   selected_segment C q0 path ((n + LENGTH u) + LENGTH [(ev,qn)]) qn v qe` by
    (irule selected_segment_parts >>
     goal_assum (drule_at Any) >> simp[joint_segment_def]) >>
  drule_all selected_singleton_event >> strip_tac >>
  qpat_assum `selected_segment C q0 path _ qm [(ev,qn)] qn`
    (mp_then Any mp_tac selected_segment_indices) >>
  gvs[]
QED

(* These are constructor interfaces: the recursive decorated witnesses remain
   explicit and are embedded in precisely the parent's ambient path. *)
Theorem selected_run_next_children:
  selected_segment C q0 path n q (wb ++ ([(SOME (OriginBlock fuel post),qn)] ++ wr)) qe /\
  decorated_block C bb phi (OK post) q n wb qm db /\
  joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
  decorated_run C fn post r qn (n + LENGTH wb + 1) wr qe dr ==>
  selected_segment C q0 path n q wb qm /\
  selected_run C q0 path fn post r qn (n + LENGTH wb + 1) wr qe dr /\
  n + LENGTH wb < LENGTH path /\
  EL (n + LENGTH wb) (MAP FST path) = SOME (OriginBlock fuel post) /\
  EL (n + LENGTH wb) (q0::MAP SND path) = qm /\
  EL (n + LENGTH wb + 1) (q0::MAP SND path) = qn
Proof
  strip_tac >>
  `joint_segment C q wb qm` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C qn wr qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all selected_segment_edge >> simp[selected_run_def]
QED

Theorem selected_invoke_child:
  selected_segment C q0 path n q w qe /\
  decorated_step C i s r q n w qe d /\ i.inst_opcode = INVOKE ==>
  ?fn cs cr qc wc dc children.
    joint_transition C q NONE qc /\
    selected_run C q0 path fn cs cr qc (n+1) wc qe dc /\
    w = (NONE,qc)::wc /\
    d = FiniteDecoration n (n+LENGTH w) [dc] /\
    dc = FiniteDecoration (n+1) (n+1+LENGTH wc) children /\
    EL n (MAP FST path) = NONE /\
    EL (n+1+LENGTH wc) (q0::MAP SND path) = qe
Proof
  strip_tac >> drule_all decorated_invoke_child >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `selected_segment C q0 path n q [(NONE,qc)] qc /\
   selected_segment C q0 path
     (n + LENGTH ([(NONE,qc)]:(origin_event option # joint_config) list)) qc wc qe` by
    (irule selected_segment_parts >> gvs[joint_segment_def]) >>
  drule_all selected_singleton_event >> strip_tac >>
  qpat_assum `selected_segment C q0 path (_ + LENGTH _) qc wc qe`
    (mp_then Any mp_tac selected_segment_indices) >>
  simp[] >> strip_tac >>
  qexistsl [`fn`, `cs`, `cr`] >> gvs[selected_run_def]
QED

(* Target derivations are abstract: neither instruction pairing nor the
   target callee/function is fixed by these constructor compositions. *)
Theorem selected_run_next_compose:
  selected_segment C q0 path n q (wb ++ ([(SOME (OriginBlock fuel post),qn)] ++ wr)) qe /\
  decorated_block C bb phi (OK post) q n wb qm db /\
  joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
  decorated_run C fn post r qn (n + LENGTH wb + 1) wr qe dr /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\
  finite_block C' bb' (phi' with vs_inst_idx :=
    phi_prefix_length bb'.bb_instructions) (OK post') /\
  ~post'.vs_halted /\ finite_run C' fn' post' r' ==>
  selected_run C q0 path fn post r qn (n + LENGTH wb + 1) wr qe dr /\
  finite_run C' fn' t r'
Proof
  strip_tac >> conj_tac
  >- (drule_all selected_run_next_children >> simp[]) >>
  irule finite_step_run_next >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem selected_invoke_return_compose:
  selected_segment C q0 path n q ((NONE,qc)::wc) qe /\
  decorated_run C fn cs (IntRet ret send) qc (n+1) wc qe dc /\
  joint_transition C q NONE qc /\
  i'.inst_opcode = INVOKE /\ decode_invoke i' = SOME (name',ops') /\
  lookup_function name' C'.ctx_functions = SOME fn' /\
  eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
  finite_run C' fn' ct (IntRet ret' send') /\
  bind_outputs i'.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state t send')) = SOME tpost ==>
  selected_run C q0 path fn cs (IntRet ret send) qc (n+1) wc qe dc /\
  EL (n+1+LENGTH wc) (q0::MAP SND path) = qe /\
  finite_step C' i' t (OK tpost)
Proof
  strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `selected_segment C q0 path n q [(NONE,qc)] qc /\
   selected_segment C q0 path
     (n + LENGTH ([(NONE,qc)]:(origin_event option # joint_config) list)) qc wc qe` by
    (irule selected_segment_parts >> gvs[joint_segment_def]) >>
  qpat_assum `selected_segment C q0 path (_ + LENGTH _) qc wc qe`
    (mp_then Any mp_tac selected_segment_indices) >>
  simp[selected_run_def] >> strip_tac >> gvs[] >>
  irule finite_step_invoke_return >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
