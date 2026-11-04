Theory frameOriginHistoryCompletedWrites
Ancestors
  frameOriginHistoryPreservation frameOriginHistoryEntries
  contextCodegenRel venomExecSemantics venomState finite_map pred_set list rich_list

Theorem eval_phis_reset_writes:
  eval_phis pre is = OK post /\ pre.vs_prev_bb = NONE ==>
  origin_phi_writes is = {} /\ phi_prefix_length is = 0
Proof
  Cases_on `is` >> simp[eval_phis_def, origin_phi_writes_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, origin_phi_writes_def, phi_prefix_length_def,
       eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem enters_block_reset_writes:
  enters_block fn pre s /\ pre.vs_prev_bb = NONE ==>
  origin_entry_writes fn pre = {}
Proof
  simp[enters_block_def, origin_entry_writes_def] >> rpt strip_tac >>
  simp[] >> metis_tac[eval_phis_reset_writes]
QED

Theorem setup_callee_no_predecessor:
  setup_callee fn args caller = SOME callee ==> callee.vs_prev_bb = NONE
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED

Definition origin_completed_writes_def:
  origin_completed_writes [] = {} /\
  origin_completed_writes [a] = {} /\
  origin_completed_writes [a;b] = {} /\
  origin_completed_writes (a::e::b::rest) =
    (case (a,b) of
       (OriginObserve src,OriginObserve dst) => origin_edge_writes src e
     | _ => {}) UNION origin_completed_writes (e::b::rest)
End

Theorem origin_completed_writes_start[simp]:
  origin_completed_writes [start;OriginObserve a] = {}
Proof
  simp[origin_completed_writes_def]
QED

Theorem origin_completed_writes_append:
  !h. h <> [] /\ LAST h = OriginObserve a /\
    (!snap. e <> OriginObserve snap) ==>
    origin_completed_writes (h ++ [e;OriginObserve b]) =
    origin_completed_writes h UNION origin_edge_writes a e
Proof
  recInduct origin_completed_writes_ind >>
  simp[origin_completed_writes_def] >> rpt strip_tac >>
  gvs[UNION_ASSOC] >> Cases_on `a'` >> Cases_on `e` >> gvs[]
QED

Theorem origin_completed_writes_cons:
  origin_completed_writes h SUBSET origin_completed_writes (ev::h)
Proof
  Cases_on `h` >> simp[origin_completed_writes_def] >>
  Cases_on `t` >> simp[origin_completed_writes_def, SUBSET_UNION]
QED

Theorem origin_completed_writes_prefix:
  !pre h. origin_completed_writes h SUBSET origin_completed_writes (pre ++ h)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  metis_tac[SUBSET_TRANS, origin_completed_writes_cons]
QED

Theorem origin_completed_writes_occurrence:
  h = pre ++ OriginObserve a::e::OriginObserve b::rest /\
  v IN origin_edge_writes a e ==> v IN origin_completed_writes h
Proof
  strip_tac >> gvs[] >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  `v IN origin_completed_writes (OriginObserve a::e::OriginObserve b::rest)` by
    simp[origin_completed_writes_def] >>
  qspecl_then [`pre`, `OriginObserve a::e::OriginObserve b::rest`] mp_tac
    origin_completed_writes_prefix >>
  simp[SUBSET_DEF] >> metis_tac[]
QED
