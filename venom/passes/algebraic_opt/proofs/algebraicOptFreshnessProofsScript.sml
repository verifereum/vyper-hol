Theory algebraicOptFreshnessProofs
Ancestors
  algebraicOptTraceProofs algebraicOptDominanceProofs venomExecSemantics venomWf venomInst list unitShapeDefs

Theorem ao_resolve_phi_pair:
  !pred ops z. resolve_phi pred ops = SOME (Var z) ==>
    MEM (pred,z) (phi_pairs ops)
Proof
  recInduct resolve_phi_ind >>
  simp[resolve_phi_def, phi_pairs_def] >> rpt strip_tac >> gvs[]
  >- (Cases_on `lbl = prev_bb`
      >- gvs[phi_pairs_def] >>
      gvs[] >> Cases_on `val_op` >> gvs[phi_pairs_def]) >>
  Cases_on `v2` >> simp[phi_pairs_def]
QED

Theorem ao_selected_phi_available:
  !fn bb phi pred z.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
    phi.inst_opcode = PHI /\
    resolve_phi pred phi.inst_operands = SOME (Var z) ==>
    ?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
      fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pred_bb NONE z
Proof
  rpt strip_tac >> drule ao_resolve_phi_pair >> strip_tac >>
  fs[wf_ssa_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> simp[phi_edge_uses_wf_def] >>
  metis_tac[]
QED

Theorem ao_distinct_output_index[local]:
  !xs f n m x.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    n < LENGTH xs /\ m < LENGTH xs /\
    MEM x (f (EL n xs)) /\ MEM x (f (EL m xs)) ==> n = m
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> Cases_on `n` >> Cases_on `m` >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_EL]
QED

Theorem ao_output_occurrence_blocks[local]:
  !bbs b1 b2 j1 j2 i1 i2 x.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    MEM b1 bbs /\ MEM b2 bbs /\
    get_instruction b1 j1 = SOME i1 /\
    get_instruction b2 j2 = SOME i2 /\
    MEM x i1.inst_outputs /\ MEM x i2.inst_outputs ==>
    b1 = b2 /\ j1 = j2 /\ i1 = i2
Proof
  Induct_on `bbs` >- simp[] >>
  simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
       ALL_DISTINCT_APPEND] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      metis_tac[ao_distinct_output_index])
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      fs[MEM_FLAT, MEM_MAP, MEM_fn_insts_blocks_iff] >>
      metis_tac[MEM_EL])
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      fs[MEM_FLAT, MEM_MAP, MEM_fn_insts_blocks_iff] >>
      metis_tac[MEM_EL]) >>
  metis_tac[]
QED

Theorem ao_ssa_output_occurrence:
  !fn b1 b2 j1 j2 i1 i2 x.
    wf_ssa fn /\ MEM b1 fn.fn_blocks /\ MEM b2 fn.fn_blocks /\
    get_instruction b1 j1 = SOME i1 /\
    get_instruction b2 j2 = SOME i2 /\
    MEM x i1.inst_outputs /\ MEM x i2.inst_outputs ==>
    b1 = b2 /\ j1 = j2 /\ i1 = i2
Proof
  simp[wf_ssa_def, ssa_form_def, fn_insts_def] >>
  metis_tac[ao_output_occurrence_blocks]
QED

Theorem ao_ssa_transition_writer:
  !fn bb j i x k phase s b.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\
    get_instruction bb j = SOME i /\ MEM x i.inst_outputs /\
    ao_transition_writes fn x (k,phase,s) b ==>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (if phase then i.inst_opcode = PHI
     else s.vs_inst_idx = j /\ ~is_terminator i.inst_opcode)
Proof
  rpt gen_tac >> Cases_on `phase` >>
  simp[ao_transition_writes_def] >> strip_tac
  >- (drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
      qpat_x_assum `MEM _ _.bb_instructions` mp_tac >>
      rewrite_tac[MEM_EL] >> strip_tac >>
      `get_instruction bb' n = SOME i'` by simp[get_instruction_def] >>
      metis_tac[ao_ssa_output_occurrence]) >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  metis_tac[ao_ssa_output_occurrence]
QED

(* O.Q INTERFACE AUDIT -- proposal only, NOT an established theorem.

Proposed writer-forces-producer boundary, with an ordinary observation or
selected-PHI predecessor-exit observation encoded by use_opt:

!ctx fn trace a b tail bp r prod x z target use_opt h t.
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  trace = a::b::tail /\ ao_source_trace ctx fn trace /\
  LAST trace = (h,F,t) /\
  MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
  prod.inst_opcode = ISZERO /\ prod.inst_outputs = [x] /\
  prod.inst_operands = [Var z] /\
  phi_prefix_length bp.bb_instructions <= r /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
  def_available_at fn target use_opt x /\
  (case use_opt of
     SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                 use.inst_opcode <> PHI
   | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                    is_terminator term.inst_opcode) /\
  ao_transition_writes fn z a b ==>
  ?middle q u v rest w.
    trace = a::(middle ++ (q,F,u)::(q,F,v)::rest) /\
    u.vs_current_bb = bp.bb_label /\ u.vs_inst_idx = r /\
    ao_source_step ctx fn (q,F,u) (q,F,v) /\
    step_inst q ctx prod u = OK w /\
    v = w with vs_inst_idx := SUC r

The leading a in the conclusion matters: the producer edge is AFTER the
hypothetical writer edge, not merely somewhere on the same trace. The suffix
must end at the original ordinary consumer-pre node or actual predecessor exit,
never at a successor post-PHI node. ao_selected_phi_available supplies NONE
availability; ao_source_trace_selected_edge supplies that predecessor endpoint.

Case-to-interface map (not yet a formal integration proof):
- W (ao_ssa_transition_writer) identifies an ordinary operand writer's exact
  block/index, or identifies its containing atomic PHI batch.
- ao_dominance_interval on ao_source_trace_path forces a producer LABEL between
  the identified operand-definition block and observation block. It does not
  itself return the required later edge.
- Truly interior producer labels: ao_source_trace_interior_execution gives the
  actual edge and original-list witnesses.
- Initial partial visit in producer block: operand definition precedes prod by
  def_available_at and W. From an ordinary writer, its post-index is <= r;
  crossing_index or crosses_before_exit can then find the edge. If the writer
  is after a previously selected producer within that same sequential visit,
  sequential_bounds instead excludes it. Missing integration: extract this
  first visit and its exit from the writer-started suffix, including re-entry.
- Final partial visit in producer block: SOME availability gives r < consumer
  index using W. NONE needs the well-formed terminator's final position. Use
  final_visit, sequential_bounds and crosses_index. Missing integration:
  distinguish no intervening entry from a final complete-entry fragment.
- PHI writer: use source_step_entry, start AFTER the whole batch at phi prefix,
  then cross r. Never invent a sequential ordering of PHI writes.
- Producer/writer or producer/consumer in the same block: these are precisely
  the two endpoint cases, not cases discharged by interior_execution.
- Self-loop: split on F-to-T and T-to-F edges, not changing labels. Existing
  final_visit permits this; no same-label monotonicity is claimed.
- Literal producer operand: no variable writer-forcing obligation; eval_operand
  is state-independent. Variable with no definition: wf_ssa's ordinary-use
  availability forbids it for this ISZERO producer; do not assume it is zero.

First producer existence is separate: source_prefix_value_origin and
iszero_historical_operand establish historical successful evaluation from an
initially absent x, but their witnesses are prefixes, not adjacent occurrences
of an arbitrarily supplied original trace. A trace-local value-origin boundary
(or a first-execution dominance/crossing proof) is still needed before applying
trace_last_event on that same trace. Stability after the last producer then
uses the proposed forcing boundary to rule out z writers; W rules out other
x writers and source_trace_non_writer transports both lookups. Neither first
existence nor the endpoint forcing integration is certified by W/B/V alone.
*)
