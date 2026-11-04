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

Theorem ao_wf_instruction_index:
  !fn bb i j.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
    EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (fs[wf_function_def, fn_inst_ids_distinct_def] >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     rewrite_tac[MEM_SPLIT] >> strip_tac >> gvs[] >>
     fs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[EL_MAP]
QED

Theorem ao_available_at_index:
  !fn bb k v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\
    def_available_at fn bb (SOME (EL k bb.bb_instructions)) v ==>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\ fn_dominates fn db.bb_label bb.bb_label /\
      (db = bb ==> ?i. i < k /\ EL i bb.bb_instructions = di)
Proof
  rpt gen_tac >> simp[def_available_at_def] >> strip_tac >>
  qexistsl [`def_bb`, `def_inst`] >> simp[] >> strip_tac >> gvs[] >>
  `j = k` by (irule ao_wf_instruction_index >> metis_tac[]) >>
  metis_tac[]
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
  sequential_bounds instead excludes it. initial_visit now extracts this
  first visit and its actual exit, including same-label re-entry; application
  to the writer-started suffix and witness embedding remain unproved.
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

First producer existence is now supplied by ao_source_trace_iszero_origin
below, on the SAME supplied trace, with an actual successful adjacent edge.
It requires the head lookup absent and final lookup present; it does not require
an independently chosen source-prefix history. Last-event selection and the
subsequent operand stability argument still need formal integration.

O.F ENDPOINT-INTERFACE AUDIT (no forcing/freshness theorem certified):

Static localization still to prove at the interface level:
From the proposal's hypotheses and the writer edge obtain an operand defining
instruction di at block db/index d, with z in its outputs, and
  fn_dominates fn db.bb_label bp.bb_label.
When db = bp, ordinary writer post-index <= r. For an atomic PHI writer in bp,
post-index = phi_prefix_length bp.bb_instructions <= r instead.
From final availability obtain fn_dominates fn bp.bb_label target.bb_label;
when bp = target obtain r < t.vs_inst_idx for BOTH use_opt cases.
These implications are not standalone proved boundaries yet. W identifies
writers once a defining occurrence is supplied, but does not itself extract
availability witnesses. Unfold wf_ssa/def_dominates_uses only in the future
static boundary. Match their witnesses using ao_ssa_output_occurrence. For
SOME, uniqueness of the producer occurrence with output x and of the operand
definition with output z aligns the existential EL indices. Equality of two
occurrences of the use instruction is now handled by ao_wf_instruction_index:
wf_function has globally distinct instruction IDs, so equal records identify
the actual index even for output-free consumers. ao_available_at_index exports
the actual-index availability witness. Thus the repeated ASSERT suspicion is
excluded by a checked structural boundary, not by consumer output uniqueness.
For NONE, non_terminator_before_terminator now supplies r < t.vs_inst_idx
without any outgoing step. lookup_block_MEM/label and wf_function label
uniqueness must align MEM blocks with lookups before crossing.

Dynamic case matrix, conditional on those static implications:
Let suffix = b::tail, so trace = [a] ++ suffix and LAST suffix = (h,F,t).
The successful writer is a->b. All crossings below occur in suffix, hence
are strictly after that writer even if the crossing starts at b.
- Ordinary writer: a has phase F; source_step_sequential gives b phase F,
  unchanged block and index SUC d. W rules out a terminator writer.
- PHI writer: a has phase T; source_step_entry gives b phase F at the PHI
  prefix. The whole batch is before b; no individual PHI ordering is used.
  In either case the suffix head label is db.bb_label.
- bp = db (including bp = db = target): apply initial_visit to suffix.
  If it is all F, single_visit_label identifies target and sequential_bounds
  supplies the same visit geometry; crosses_index uses post-index <= r and
  r < t.vs_inst_idx. Otherwise initial_visit returns an all-F prefix ending
  at the actual F-to-T exit. crosses_before_exit yields an edge within that
  prefix from post-index <= r. Reattach its recorded exit and back suffix.
  This case takes priority over final/interior cases and covers all self-loops
  whose initial label is bp, regardless of later returns to that label.
- bp <> db and bp = target: final_visit on suffix cannot be all F, since
  single_visit_label would equate its head and last labels. Its last T-to-F
  entry gives an all-F final fragment starting at the PHI prefix. Match its
  block with bp and use crosses_index plus r < t.vs_inst_idx. Reattach the
  original front through its T entry node. This includes any number of
  same-label loop re-entries: final_visit is phase-based, not label-based.
- bp <> db and bp <> target: source_trace_path plus dominance_interval
  forces MEM bp.bb_label (ao_trace_path suffix). interior_execution then
  supplies the adjacent successful edge with exact suffix decomposition.
  It requires both endpoint label inequalities, not merely different states.
- SOME versus NONE changes only the static final bound above, not this
  exhaustive equality split or crossing argument. selected_edge together
  with selected_phi_available reduces a selected PHI use to the predecessor's
  phase-F terminator-pre endpoint and preserves lookup across the outgoing
  F-to-T step. Do not transport across successor PHIs.

For every row: if suffix = front ++ edge_pre::edge_post::back, choose
middle = front in the proposal; prefixing a gives the exact original trace.
Nested initial/final fragment witnesses combine by APPEND_ASSOC. This is
ordinary list equality, not a projection from a CFG path. No witness may be
borrowed from a different history.

Remaining mathematical outputs (recommend shallow allocation, no more audits):
1. Static localization/bounds stated above. The actual-index SOME occurrence
   issue is resolved by ao_available_at_index and ao_wf_instruction_index;
   matching the producer/operand definition witnesses and exporting the full
   dominance and position interface still requires proof.
2. The EXACT writer-forces-producer proposal above, consuming those static
   facts and the three dynamic rows; no extra reachability assumptions.
3. Last-producer freshness: on an entry-origin trace with initially absent x
   and present endpoint x, select the last occurrence given by iszero_origin.
   W and SSA uniqueness exclude x writers on its suffix. Any z writer on that
   suffix would, by output 2 on its writer-started subtrace, force a later
   producer and contradict lastness. non_writer transports the operand and
   output lookups; the successful ISZERO step gives the endpoint equation.
   Selected-PHI consumers use the predecessor endpoint reduction, separately.
These are required integration obligations, NOT consequences certified merely
by completing this audit. No new definition or admitted theorem is introduced.
*)

Theorem ao_source_trace_iszero_origin:
  !trace ctx fn x value bp r prod.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x (SND (SND (LAST trace))) = SOME value /\
    wf_ssa fn /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\
    prod.inst_opcode = ISZERO /\ prod.inst_outputs = [x] ==>
    ?front q u v back w.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = bp.bb_label /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      step_inst q ctx prod u = OK w /\
      v = w with vs_inst_idx := SUC r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_source_trace_lookup_origin >> strip_tac >>
  `ao_source_step ctx fn a b` by
    metis_tac[ao_source_trace_transition_split] >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  `lookup_block a2.vs_current_bb fn.fn_blocks = SOME bp /\
   (if a1 then prod.inst_opcode = PHI
    else a2.vs_inst_idx = r /\ ~is_terminator prod.inst_opcode)` by
    (irule (INST_TYPE [alpha |-> ``:num``] ao_ssa_transition_writer) >>
     simp[] >> qexistsl [`(b0,b1,b2)`, `a0`] >> simp[]) >>
  Cases_on `a1` >- gvs[] >> gvs[] >>
  qpat_x_assum `ao_source_step _ _ _ _` mp_tac >>
  simp[Once ao_source_step_cases] >> strip_tac >> gvs[] >>
  qexistsl [`front`, `a0`, `a2`, `back`, `t`] >> simp[] >>
  conj_tac >- metis_tac[venomExecPropsTheory.lookup_block_label] >>
  irule (cj 2 ao_source_step_rules) >> simp[] >> metis_tac[]
QED

Theorem ao_iszero_observation_location:
  !fn bp r prod x target t use_opt.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
    prod.inst_opcode = ISZERO /\ prod.inst_outputs = [x] /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) ==>
    fn_dominates fn bp.bb_label target.bb_label /\
    (bp = target ==> r < t.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM target fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  fs[def_available_at_def] >>
  qpat_x_assum `MEM def_inst def_bb.bb_instructions` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  `get_instruction def_bb n = SOME def_inst` by simp[get_instruction_def] >>
  `def_bb = bp /\ n = r /\ def_inst = prod` by
    (irule ao_ssa_output_occurrence >> metis_tac[MEM]) >> gvs[] >>
  strip_tac >> gvs[] >> Cases_on `use_opt` >> gvs[]
  >- (`bb_well_formed bp` by metis_tac[wf_function_def] >>
      irule venomExecPropsTheory.non_terminator_before_terminator >>
      metis_tac[is_terminator_def]) >>
  `j = t.vs_inst_idx` by
    (irule ao_wf_instruction_index >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  `i = n` by
    (irule ao_wf_instruction_index >> qexistsl [`bp`, `fn`] >>
     gvs[get_instruction_def, AllCaseEqs()]) >>
  gvs[]
QED

Theorem ao_iszero_writer_location:
  !ctx fn bp r prod x z k phase s b.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
    prod.inst_opcode = ISZERO /\ prod.inst_outputs = [x] /\
    prod.inst_operands = [Var z] /\
    phi_prefix_length bp.bb_instructions <= r /\
    ao_source_step ctx fn (k,phase,s) b /\
    ao_transition_writes fn z (k,phase,s) b ==>
    ?db d di q v.
      MEM db fn.fn_blocks /\ get_instruction db d = SOME di /\
      MEM z di.inst_outputs /\ fn_dominates fn db.bb_label bp.bb_label /\
      b = (q,F,v) /\ v.vs_current_bb = db.bb_label /\
      (db = bp ==> v.vs_inst_idx <= r)
Proof
  rpt gen_tac >> strip_tac >>
  `r < LENGTH bp.bb_instructions /\ EL r bp.bb_instructions = prod` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `MEM prod bp.bb_instructions` by metis_tac[MEM_EL] >>
  `def_available_at fn bp (SOME prod) z` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  `?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM z di.inst_outputs /\ fn_dominates fn db.bb_label bp.bb_label /\
    (db = bp ==> ?i. i < r /\ EL i bp.bb_instructions = di)` by
    (irule ao_available_at_index >> simp[]) >>
  qpat_x_assum `MEM di db.bb_instructions` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  `get_instruction db n = SOME di` by simp[get_instruction_def] >>
  drule_all ao_ssa_transition_writer >> strip_tac >>
  PairCases_on `b` >> Cases_on `phase` >> gvs[]
  >- (Cases_on `b1`
      >- metis_tac[ao_source_step_no_entry_entry] >>
      drule ao_source_step_entry >> strip_tac >> gvs[] >>
      qexistsl [`bb`, `n`, `EL n bb.bb_instructions`] >>
      simp[GSYM MEM_EL] >>
      metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  Cases_on `b1`
  >- (drule ao_source_step_exit >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  drule ao_source_step_sequential >> strip_tac >> gvs[] >>
  qexistsl [`bb`, `s.vs_inst_idx`, `EL s.vs_inst_idx bb.bb_instructions`] >>
  simp[GSYM MEM_EL] >>
  `s.vs_current_bb = bb.bb_label` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  simp[] >> strip_tac >> gvs[] >>
  `i = s.vs_inst_idx` by
    (irule ao_wf_instruction_index >> qexistsl [`bb`, `fn`] >> simp[]) >>
  decide_tac
QED

Theorem ao_source_trace_writer_forces_iszero:
  !ctx fn trace a b tail bp r prod x z target use_opt h t.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    trace = a::b::tail /\ ao_source_trace ctx fn trace /\
    LAST trace = (h,F,t) /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\
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
      step_inst q ctx prod u = OK w /\ v = w with vs_inst_idx := SUC r
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `ao_source_step ctx fn a b /\ ao_source_trace ctx fn (b::tail)` by
    gvs[ao_source_trace_def] >>
  PairCases_on `a` >>
  drule_all ao_iszero_writer_location >> strip_tac >> gvs[] >>
  `fn_dominates fn bp.bb_label target.bb_label /\
   (bp = target ==> r < t.vs_inst_idx)` by
    (irule ao_iszero_observation_location >> metis_tac[]) >>
  `lookup_block bp.bb_label fn.fn_blocks = SOME bp` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  Cases_on `db = bp` >- suspend "initial" >>
  Cases_on `target = bp` >- suspend "final" >>
  suspend "interior"
QED

Resume ao_source_trace_writer_forces_iszero[initial]:
  gvs[] >>
  drule ao_source_trace_initial_visit >> strip_tac
  >- (`t.vs_current_bb = bp.bb_label` by
        (qspec_then `tail` (qspecl_then [`ctx`,`fn`,`(q,F,v)`] mp_tac)
           ao_source_trace_single_visit_label >>
         (impl_tac >- gvs[]) >> rewrite_tac[EVERY_MEM] >>
         disch_then (qspec_then `LAST ((q,F,v)::tail)` mp_tac) >>
         simp[rich_listTheory.LAST_MEM]) >>
      `target = bp` by gvs[] >>
      `r < t.vs_inst_idx` by metis_tac[] >>
      qspec_then `(q,F,v)::tail` (qspecl_then [`ctx`,`fn`] mp_tac)
        ao_source_trace_crosses_index >>
      simp[] >> disch_then (qspecl_then [`r`,`prod`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `~is_terminator prod.inst_opcode` by simp[is_terminator_def] >>
  qspec_then `front ++ [(j,F,u)]` (qspecl_then [`ctx`,`fn`] mp_tac)
    ao_source_trace_crosses_before_exit >>
  simp[] >>
  disch_then (qspecl_then [`r`,`prod`,`out`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qexistsl [`front'`,`q'`,`u'`,`back' ++ (j,T,out)::back`,`w`] >>
  simp[] >>
  qpat_x_assum `front ++ [(j,F,u)] = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then (fn th => rewrite_tac[GSYM th])
QED
Resume ao_source_trace_writer_forces_iszero[final]:
  gvs[] >>
  `db.bb_label <> bp.bb_label` by (strip_tac >> gvs[]) >>
  qspec_then `(q,F,v)::tail` (qspecl_then [`ctx`,`fn`] mp_tac)
    ao_source_trace_final_visit >>
  simp[] >> strip_tac
  >- (qspec_then `tail` (qspecl_then [`ctx`,`fn`,`(q,F,v)`] mp_tac)
        ao_source_trace_single_visit_label >>
      (impl_tac >- gvs[]) >> rewrite_tac[EVERY_MEM] >>
      disch_then (qspec_then `LAST ((q,F,v)::tail)` mp_tac) >>
      simp[rich_listTheory.LAST_MEM] >> strip_tac >> gvs[]) >>
  `LAST ((j,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)::back) =
    (h,F,t)` by (Cases_on `back` >> gvs[]) >>
  `p.vs_current_bb = t.vs_current_bb` by
    (qspec_then `back` (qspecl_then [`ctx`,`fn`,
        `(j,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)`] mp_tac)
       ao_source_trace_single_visit_label >>
     (impl_tac >- gvs[]) >> rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `LAST ((j,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)::back)` mp_tac) >>
     simp[rich_listTheory.LAST_MEM] >> metis_tac[]) >>
  `bb = bp` by
    (drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
     strip_tac >> gvs[]) >>
  qspec_then `(j,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)::back`
    (qspecl_then [`ctx`,`fn`] mp_tac) ao_source_trace_crosses_index >>
  simp[] >> disch_then (qspecl_then [`r`,`prod`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `t.vs_current_bb = bb.bb_label` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  qexistsl [`(front ++ [(k,T,s)]) ++ front'`,`q'`,`u`,`back'`,`w`] >>
  simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `(j,F,_)::back = _` (fn th => rewrite_tac[GSYM th])
QED
Resume ao_source_trace_writer_forces_iszero[interior]:
  `db.bb_label <> bp.bb_label` by (strip_tac >> gvs[]) >>
  `bp.bb_label <> t.vs_current_bb` by (strip_tac >> gvs[]) >>
  qspec_then `(q,F,v)::tail` (qspecl_then [`ctx`,`fn`] mp_tac)
    ao_source_trace_path >> simp[] >> strip_tac >>
  qspec_then `(q,F,v)::tail` mp_tac ao_trace_path_shape >>
  simp[] >> strip_tac >>
  `MEM bp.bb_label (ao_trace_path ((q,F,v)::tail))` by
    (irule ao_dominance_interval >>
     simp[] >> qexistsl [`fn`] >>
     gvs[] >> metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  qspec_then `(q,F,v)::tail` (qspecl_then [`ctx`,`fn`,`bp`,`r`,`prod`] mp_tac)
    ao_source_trace_interior_execution >>
  simp[is_terminator_def] >> strip_tac >> gvs[] >> metis_tac[]
QED
Finalise ao_source_trace_writer_forces_iszero

Theorem ao_ssa_iszero_not_self:
  !fn bp r prod x z.
    wf_function fn /\ wf_ssa fn /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [Var z] ==> z <> x
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  `r < LENGTH bp.bb_instructions /\ EL r bp.bb_instructions = prod` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `MEM prod bp.bb_instructions` by metis_tac[MEM_EL] >>
  `def_available_at fn bp (SOME prod) x` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  `?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM x di.inst_outputs /\ fn_dominates fn db.bb_label bp.bb_label /\
    (db = bp ==> ?i. i < r /\ EL i bp.bb_instructions = di)` by
    (irule ao_available_at_index >> simp[]) >>
  qpat_x_assum `MEM di db.bb_instructions` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  `get_instruction db n = SOME di` by simp[get_instruction_def] >>
  `MEM x prod.inst_outputs` by simp[] >>
  `db = bp /\ n = r` by metis_tac[ao_ssa_output_occurrence] >>
  gvs[] >>
  `i = n` by
    (irule ao_wf_instruction_index >> qexistsl [`bp`,`fn`] >> simp[]) >>
  decide_tac
QED

Theorem ao_source_trace_last_iszero:
  !ctx fn trace bp r prod x z target use_opt h t value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [Var z] /\
    phi_prefix_length bp.bb_instructions <= r /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) ==>
    ?front q u v back w.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = bp.bb_label /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      step_inst q ctx prod u = OK w /\ v = w with vs_inst_idx := SUC r /\
      lookup_var x t = lookup_var x v /\
      eval_operand (Var z) t = eval_operand (Var z) u
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `trace` (qspec_then `ao_transition_writes fn x` strip_assume_tac)
    ao_trace_last_event
  >- (drule_all ao_source_trace_non_writer >> simp[]) >>
  `ao_source_step ctx fn a b` by
    metis_tac[ao_source_trace_transition_split] >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  `lookup_block a2.vs_current_bb fn.fn_blocks = SOME bp /\
   (if a1 then prod.inst_opcode = PHI
    else a2.vs_inst_idx = r /\ ~is_terminator prod.inst_opcode)` by
    (irule (INST_TYPE [alpha |-> ``:num``] ao_ssa_transition_writer) >>
     simp[] >> qexistsl [`(b0,b1,b2)`, `a0`] >> simp[]) >>
  Cases_on `a1` >- gvs[] >> gvs[] >>
  qpat_x_assum `ao_source_step _ _ _ _` mp_tac >>
  simp[Once ao_source_step_cases] >> strip_tac >> gvs[] >>
  suspend "stable"
QED
Resume ao_source_trace_last_iszero[stable]:
  `lookup_block bp.bb_label fn.fn_blocks = SOME bp` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `ao_source_trace ctx fn ((a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)` by
    metis_tac[ao_source_trace_transition_split] >>
  `lookup_var x (t' with vs_inst_idx := SUC a2.vs_inst_idx) = lookup_var x t` by
    (qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspecl_then [`ctx`,`fn`,`x`] mp_tac) ao_source_trace_non_writer >> simp[]) >>
  `ao_trace_avoids (ao_transition_writes fn z)
    ((a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)` by
    (spose_not_then assume_tac >>
     qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspec_then `ao_transition_writes fn z` strip_assume_tac) ao_trace_last_event >>
     `ao_source_trace ctx fn (a::b::back')` by
       metis_tac[ao_source_trace_split] >>
     `LAST (a::b::back') = (h,F,t)` by gvs[] >>
     qspecl_then [`ctx`,`fn`,`a::b::back'`] mp_tac
       ao_source_trace_writer_forces_iszero >>
     simp[] >>
     qexistsl [`bp`,`a2.vs_inst_idx`,`prod`,`x`,`z`,`use_opt`] >>
     simp[] >> rpt gen_tac >> strip_tac >> rpt strip_tac >>
     `ao_transition_writes fn x (q,F,u)
        (q,F,w with vs_inst_idx := SUC a2.vs_inst_idx)` by
       (simp[ao_transition_writes_def] >> qexistsl [`bp`,`prod`] >>
        simp[is_terminator_def]) >>
     qpat_x_assum `ao_trace_avoids (ao_transition_writes fn x) _` mp_tac >>
     qpat_x_assum `_ = front' ++ a::b::back'` (fn th => rewrite_tac[th]) >>
     rewrite_tac[Once ao_trace_avoids_split] >>
     pure_rewrite_tac[ao_trace_avoids_def] >> strip_tac >>
     qpat_x_assum `ao_trace_avoids (ao_transition_writes fn x) (b::back')` mp_tac >>
     qpat_x_assum `b::back' = _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     rewrite_tac[Once ao_trace_avoids_split] >>
     simp[ao_trace_avoids_def]) >>
  suspend "transport"
QED
Resume ao_source_trace_last_iszero[transport]:
  `z <> x` by metis_tac[ao_ssa_iszero_not_self] >>
  `lookup_var z t' = lookup_var z a2` by
    (drule venomInstPropsTheory.step_preserves_non_output_vars >>
     disch_then (qspec_then `z` mp_tac) >> simp[venomStateTheory.lookup_var_def]) >>
  `lookup_var z (t' with vs_inst_idx := SUC a2.vs_inst_idx) = lookup_var z t` by
    (qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspecl_then [`ctx`,`fn`,`z`] mp_tac) ao_source_trace_non_writer >> simp[]) >>
  qexistsl [`front`,`a0`,`a2`,`back`,`t'`] >>
  simp[venomStateTheory.eval_operand_def] >>
  conj_tac >- metis_tac[venomExecPropsTheory.lookup_block_label] >>
  conj_tac >- metis_tac[ao_source_step_rules] >>
  gvs[venomStateTheory.lookup_var_def]
QED
Finalise ao_source_trace_last_iszero


Theorem ao_source_trace_selected_phi_last_iszero:
  !ctx fn trace bp r prod x z bb phi pred h s value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\
    LAST trace = (h,T,s) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x s = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [Var z] /\
    phi_prefix_length bp.bb_instructions <= r /\
    MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
    phi.inst_opcode = PHI /\ s.vs_prev_bb = SOME pred /\
    resolve_phi pred phi.inst_operands = SOME (Var x) ==>
    ?front q u v back w.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = bp.bb_label /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      step_inst q ctx prod u = OK w /\ v = w with vs_inst_idx := SUC r /\
      lookup_var x s = lookup_var x v /\
      eval_operand (Var z) s = eval_operand (Var z) u
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_source_trace_selected_edge >> simp[] >>
  disch_then drule >> strip_tac >>
  PairCases_on `a` >> gvs[] >>
  drule_all ao_selected_phi_available >> strip_tac >>
  `lookup_block a2.vs_current_bb fn.fn_blocks = SOME pred_bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `?term. get_instruction pred_bb a2.vs_inst_idx = SOME term /\
          is_terminator term.inst_opcode` by
    (drule ao_source_step_exit >> simp[] >> strip_tac >> gvs[]) >>
  `lookup_var x (SND (SND (HD (front ++ [(a0,F,a2)])))) = NONE` by
    (Cases_on `front` >> gvs[]) >>
  qspecl_then [`ctx`,`fn`,`front ++ [(a0,F,a2)]`] mp_tac
    ao_source_trace_last_iszero >>
  simp[] >>
  disch_then (qspecl_then [`bp`,`r`,`prod`,`x`,`z`,`NONE`,`value`] mp_tac) >>
  simp[] >> strip_tac >>
  `eval_operand (Var z) s = eval_operand (Var z) a2` by
    (qpat_x_assum `!x'. lookup_var x' a2 = lookup_var x' s`
       (qspec_then `z` assume_tac) >>
     gvs[venomStateTheory.eval_operand_def]) >>
  qexistsl [`front'`,`q`,`u`,`back ++ [(h,T,s)]`,`w`] >> simp[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `front ++ [(a0,F,a2)] = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED
