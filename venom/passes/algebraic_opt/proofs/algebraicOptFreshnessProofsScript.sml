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

(* Ordinary producer provenance:
   Availability locates the selected operand's definition before the producer,
   while the actual ordinary-use or predecessor-exit observation locates the
   producer before the endpoint. Writer-forcing crosses the initial, final, or
   interior producer visit strictly after the hypothetical operand writer.
   Last-event selection then excludes operand writers after the last output
   write. The generic transport boundary below does not depend on an opcode's
   evaluation rule, and allows multiple outputs (the operand must be in none).
   ISZERO interfaces are retained as specializations for existing consumers.
   These results do not assert unrestricted stored DFG equations, nor transitive
   ASSIGN-chain availability at the final observation. *)

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

Theorem ao_producer_observation_location:
  !fn bp r prod x target t use_opt.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
    ~is_terminator prod.inst_opcode /\ MEM x prod.inst_outputs /\
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
      irule non_terminator_before_terminator >>
      metis_tac[is_terminator_def]) >>
  `j = t.vs_inst_idx` by
    (irule ao_wf_instruction_index >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  `i = n` by
    (irule ao_wf_instruction_index >> qexistsl [`bp`, `fn`] >>
     gvs[get_instruction_def, AllCaseEqs()]) >>
  gvs[]
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
  rpt gen_tac >> strip_tac >> irule ao_producer_observation_location >>
  simp[] >> metis_tac[is_terminator_def, MEM]
QED

Theorem ao_producer_writer_location:
  !ctx fn bp r prod z k phase s b.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
    def_available_at fn bp (SOME prod) z /\
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
  rpt gen_tac >> strip_tac >> irule ao_producer_writer_location >>
  simp[] >> conj_tac >- metis_tac[] >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  fs[wf_ssa_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ao_source_trace_writer_forces_producer:
  !ctx fn trace a b tail bp r prod x z target use_opt h t.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    trace = a::b::tail /\ ao_source_trace ctx fn trace /\
    LAST trace = (h,F,t) /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\
    prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode /\
    MEM x prod.inst_outputs /\ MEM (Var z) prod.inst_operands /\
    def_available_at fn bp (SOME prod) z /\
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
  drule_all ao_producer_writer_location >> strip_tac >> gvs[] >>
  `fn_dominates fn bp.bb_label target.bb_label /\
   (bp = target ==> r < t.vs_inst_idx)` by
    (irule ao_producer_observation_location >> metis_tac[]) >>
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

Resume ao_source_trace_writer_forces_producer[initial]:
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
Resume ao_source_trace_writer_forces_producer[final]:
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
Resume ao_source_trace_writer_forces_producer[interior]:
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
Finalise ao_source_trace_writer_forces_producer

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
  rpt gen_tac >> strip_tac >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `def_available_at fn bp (SOME prod) z` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  irule ao_source_trace_writer_forces_producer >>
  simp[] >> metis_tac[is_terminator_def, MEM]
QED

Theorem ao_ssa_producer_operand_not_output:
  !fn bp r prod z.
    wf_function fn /\ wf_ssa fn /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\
    def_available_at fn bp (SOME prod) z ==> ~MEM z prod.inst_outputs
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `r < LENGTH bp.bb_instructions /\ EL r bp.bb_instructions = prod` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `MEM prod bp.bb_instructions` by metis_tac[MEM_EL] >>
  `?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM z di.inst_outputs /\ fn_dominates fn db.bb_label bp.bb_label /\
    (db = bp ==> ?i. i < r /\ EL i bp.bb_instructions = di)` by
    (irule ao_available_at_index >> simp[]) >>
  qpat_x_assum `MEM di db.bb_instructions` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  `get_instruction db n = SOME di` by simp[get_instruction_def] >>
  `db = bp /\ n = r` by metis_tac[ao_ssa_output_occurrence] >>
  gvs[] >>
  `i = n` by
    (irule ao_wf_instruction_index >> qexistsl [`bp`,`fn`] >> simp[]) >>
  decide_tac
QED

Theorem ao_ssa_iszero_not_self:
  !fn bp r prod x z.
    wf_function fn /\ wf_ssa fn /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [Var z] ==> z <> x
Proof
  rpt gen_tac >> strip_tac >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `def_available_at fn bp (SOME prod) z` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  drule_all ao_ssa_producer_operand_not_output >> simp[]
QED

Theorem ao_source_trace_last_output:
  !ctx fn trace bp r prod x value h t.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode <> PHI /\
    ~is_terminator prod.inst_opcode /\ MEM x prod.inst_outputs ==>
    ?front q u v back w.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = bp.bb_label /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      step_inst q ctx prod u = OK w /\ v = w with vs_inst_idx := SUC r /\
      lookup_var x t = lookup_var x v /\
      ao_trace_avoids (ao_transition_writes fn x) ((q,F,v)::back)
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
     simp[] >> qexistsl [`(b0,b1,b2)`, `a0`] >> simp[] >> metis_tac[]) >>
  Cases_on `a1` >- gvs[] >> gvs[] >>
  qpat_x_assum `ao_source_step _ _ _ _` mp_tac >>
  simp[Once ao_source_step_cases] >> strip_tac >> gvs[] >>
  `ao_source_trace ctx fn ((a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)` by
    metis_tac[ao_source_trace_transition_split] >>
  `lookup_var x (t' with vs_inst_idx := SUC a2.vs_inst_idx) = lookup_var x t` by
    (qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspecl_then [`ctx`,`fn`,`x`] mp_tac) ao_source_trace_non_writer >> simp[]) >>
  qexistsl [`front`,`a0`,`a2`,`back`,`t'`] >> simp[] >>
  conj_tac >- metis_tac[venomExecPropsTheory.lookup_block_label] >>
  metis_tac[ao_source_step_rules]
QED

Theorem ao_source_trace_last_producer_operands:
  !ctx fn trace bp r prod x target use_opt h t value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode <> PHI /\
    ~is_terminator prod.inst_opcode /\ MEM x prod.inst_outputs /\
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
      (!op. MEM op prod.inst_operands ==> eval_operand op t = eval_operand op u)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_source_trace_last_output >>
  disch_then (qx_choose_then `front` (qx_choose_then `a0`
    (qx_choose_then `a2` (qx_choose_then `v` (qx_choose_then `back`
      (qx_choose_then `t'` strip_assume_tac)))))) >>
  gvs[] >> qexistsl [`front`,`a0`,`a2`,`back`,`t'`] >> simp[] >>
  rpt strip_tac >> Cases_on `op`
  >~ [`eval_operand (Lit c) t = _`]
  >- simp[venomStateTheory.eval_operand_def]
  >~ [`eval_operand (Label label) t = _`]
  >- (`MEM (a0,F,a2)
        (front ++ (a0,F,a2)::(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)`
        by simp[] >>
      `MEM (h,F,t)
        (front ++ (a0,F,a2)::(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)`
        by (qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
              mp_tac rich_listTheory.LAST_MEM >> simp[MEM_APPEND] >>
            metis_tac[]) >>
      `t.vs_labels = a2.vs_labels` by metis_tac[ao_source_trace_labels] >>
      simp[venomStateTheory.eval_operand_def]) >>
  rename1 `MEM (Var z) prod.inst_operands` >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `def_available_at fn bp (SOME prod) z` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  suspend "stable"
QED
Resume ao_source_trace_last_producer_operands[stable]:
  `lookup_block bp.bb_label fn.fn_blocks = SOME bp` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `ao_source_trace ctx fn ((a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)` by
    metis_tac[ao_source_trace_transition_split] >>
  `ao_trace_avoids (ao_transition_writes fn z)
    ((a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back)` by
    (spose_not_then assume_tac >>
     qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspec_then `ao_transition_writes fn z` strip_assume_tac) ao_trace_last_event >>
     `ao_source_trace ctx fn (a::b::back')` by
       metis_tac[ao_source_trace_split] >>
     `LAST (a::b::back') = (h,F,t)` by gvs[] >>
     qspecl_then [`ctx`,`fn`,`a::b::back'`] mp_tac
       ao_source_trace_writer_forces_producer >>
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
Resume ao_source_trace_last_producer_operands[transport]:
  `~MEM z prod.inst_outputs` by metis_tac[ao_ssa_producer_operand_not_output] >>
  `lookup_var z t' = lookup_var z a2` by
    (drule venomInstPropsTheory.step_preserves_non_output_vars >>
     disch_then (qspec_then `z` mp_tac) >> simp[venomStateTheory.lookup_var_def]) >>
  `lookup_var z (t' with vs_inst_idx := SUC a2.vs_inst_idx) = lookup_var z t` by
    (qspec_then `(a0,F,t' with vs_inst_idx := SUC a2.vs_inst_idx)::back`
       (qspecl_then [`ctx`,`fn`,`z`] mp_tac) ao_source_trace_non_writer >> simp[]) >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED
Finalise ao_source_trace_last_producer_operands

Theorem ao_source_trace_last_producer_operand:
  !ctx fn trace bp r prod x z target use_opt h t value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode <> PHI /\
    ~is_terminator prod.inst_opcode /\ MEM x prod.inst_outputs /\
    MEM (Var z) prod.inst_operands /\ def_available_at fn bp (SOME prod) z /\
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
  drule_all ao_source_trace_last_producer_operands >> strip_tac >>
  qexistsl [`front`,`q`,`u`,`v`,`back`,`w`] >> simp[]
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
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `def_available_at fn bp (SOME prod) z` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  irule ao_source_trace_last_producer_operand >>
  simp[] >> metis_tac[is_terminator_def, MEM]
QED

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

Theorem ao_available_through_producer:
  !fn bp prod x z target use_opt.
    wf_function fn /\ wf_ssa fn /\
    MEM bp fn.fn_blocks /\ MEM prod bp.bb_instructions /\
    MEM x prod.inst_outputs /\
    def_available_at fn bp (SOME prod) z /\
    def_available_at fn target use_opt x ==>
    def_available_at fn target use_opt z
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `MEM prod bp.bb_instructions`
    (qx_choose_then `r` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qpat_x_assum `def_available_at fn target use_opt x` mp_tac >>
  rewrite_tac[def_available_at_def] >> strip_tac >>
  qpat_assum `MEM def_inst def_bb.bb_instructions`
    (qx_choose_then `d` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `get_instruction bp r = SOME prod /\
   get_instruction def_bb d = SOME def_inst` by simp[get_instruction_def] >>
  `def_bb = bp /\ d = r /\ def_inst = prod` by
    metis_tac[ao_ssa_output_occurrence] >>
  qpat_x_assum `def_bb = bp` SUBST_ALL_TAC >>
  qpat_x_assum `def_inst = prod` SUBST_ALL_TAC >>
  qpat_x_assum `def_available_at fn bp (SOME prod) z` mp_tac >>
  rewrite_tac[def_available_at_def] >> strip_tac >>
  rename1 `MEM z zi.inst_outputs` >> rename1 `MEM zi zb.bb_instructions` >>
  qexistsl [`zb`,`zi`] >> simp[] >>
  conj_tac >- metis_tac[ao_fn_dominates_trans] >>
  strip_tac >>
  `bp.bb_label = zb.bb_label` by metis_tac[ao_fn_dominates_antisym] >>
  `bp = zb` by
    (`lookup_block bp.bb_label fn.fn_blocks = SOME bp /\
      lookup_block zb.bb_label fn.fn_blocks = SOME zb` by
       (conj_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  gvs[] >> Cases_on `use_opt` >- simp[] >> gvs[] >>
  `j = d /\ i' = d` by
    (conj_tac >> irule ao_wf_instruction_index >>
     qexistsl [`bp`,`fn`] >> simp[]) >>
  qexistsl [`i`,`j'`] >> simp[] >> decide_tac
QED

Theorem ao_source_trace_iszero_operand_value:
  !ctx fn trace bp r prod x op target use_opt h t value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [op] /\
    phi_prefix_length bp.bb_instructions <= r /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) ==>
    ?word. eval_operand op t = SOME word /\
           value = (if word = 0w then 1w else 0w)
Proof
  rpt gen_tac >> strip_tac >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode /\
   MEM x prod.inst_outputs` by simp[is_terminator_def] >>
  drule_all ao_source_trace_last_producer_operands >> strip_tac >>
  `eval_operand op t = eval_operand op u` by metis_tac[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, exec_pure1_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def] >>
  Cases_on `x' = 0w` >> simp[venomExecSemanticsTheory.bool_to_word_def]
QED

Theorem ao_source_trace_iszero_value:
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
    ?word. eval_operand (Var z) t = SOME word /\
           value = (if word = 0w then 1w else 0w)
Proof
  rpt gen_tac >> strip_tac >> drule_all ao_source_trace_iszero_operand_value >> simp[]
QED


Theorem ao_source_trace_selected_phi_iszero_operand_value:
  !ctx fn trace bp r prod x op bb phi pred h s value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\
    LAST trace = (h,T,s) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x s = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ISZERO /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [op] /\
    phi_prefix_length bp.bb_instructions <= r /\
    MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
    phi.inst_opcode = PHI /\ s.vs_prev_bb = SOME pred /\
    resolve_phi pred phi.inst_operands = SOME (Var x) ==>
    ?word. eval_operand op s = SOME word /\
           value = (if word = 0w then 1w else 0w)
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
  `s.vs_labels = a2.vs_labels` by
    (drule ao_source_step_labels >> simp[]) >>
  `eval_operand op s = eval_operand op a2` by
    (Cases_on `op` >> simp[venomStateTheory.eval_operand_def]) >>
  qspecl_then [`ctx`,`fn`,`front ++ [(a0,F,a2)]`] mp_tac
    ao_source_trace_iszero_operand_value >>
  simp[] >>
  disch_then (qspecl_then [`bp`,`r`,`prod`,`x`,`op`,`NONE`,`value`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ao_source_trace_selected_phi_iszero_value:
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
    ?word. eval_operand (Var z) s = SOME word /\
           value = (if word = 0w then 1w else 0w)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_source_trace_selected_phi_iszero_operand_value >> simp[]
QED
