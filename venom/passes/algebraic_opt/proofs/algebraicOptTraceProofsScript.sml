Theory algebraicOptTraceProofs
Ancestors
  algebraicOptReachabilityProofs venomState venomInst venomWf venomExecSemantics list rich_list pair

(* A single real transition, not the reflexive initial prefix. PHIs are atomic. *)
Inductive ao_source_step:
  (!ctx fn k s bb p.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_step ctx fn (SUC k,T,s)
      (k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t ==>
    ao_source_step ctx fn (k,F,s)
      (k,F,t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t /\ ~t.vs_halted ==>
    ao_source_step ctx fn (k,F,s) (k,T,t))
End

Definition ao_source_trace_def:
  ao_source_trace ctx fn ([]:(num # bool # venom_state) list) = T /\
  ao_source_trace ctx fn [a] = T /\
  ao_source_trace ctx fn (a::b::rest) =
    (ao_source_step ctx fn a b /\ ao_source_trace ctx fn (b::rest))
End

Theorem ao_source_step_prefix:
  !ctx fn a b.
    ao_source_step ctx fn a b ==>
    !s0 n. ao_source_prefix ctx fn s0 n (FST a) (FST (SND a)) (SND (SND a)) ==>
      ao_source_prefix ctx fn s0 n (FST b) (FST (SND b)) (SND (SND b))
Proof
  ho_match_mp_tac ao_source_step_ind >> simp[] >> rpt strip_tac >>
  metis_tac[ao_source_prefix_rules]
QED

Theorem ao_source_trace_snoc:
  !trace ctx fn a.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ao_source_step ctx fn (LAST trace) a ==>
    ao_source_trace ctx fn (trace ++ [a])
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `trace` >> simp[ao_source_trace_def] >>
  metis_tac[APPEND, NOT_CONS_NIL]
QED

Theorem ao_source_trace_extend:
  !ctx fn start a b.
    ao_source_step ctx fn a b /\
    (?trace. trace <> [] /\ HD trace = start /\ LAST trace = a /\
      ao_source_trace ctx fn trace) ==>
    ?trace. trace <> [] /\ HD trace = start /\ LAST trace = b /\
      ao_source_trace ctx fn trace
Proof
  rpt strip_tac >> qexists `trace ++ [b]` >>
  simp[LAST_APPEND_CONS] >> conj_tac
  >- (Cases_on `trace` >> gvs[]) >>
  irule ao_source_trace_snoc >> simp[]
QED

Theorem ao_source_prefix_has_trace:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    ?trace. trace <> [] /\ HD trace = (n,T,s0) /\
      LAST trace = (k,phase,s) /\ ao_source_trace ctx fn trace
Proof
  ho_match_mp_tac ao_source_prefix_ind >> conj_tac
  >- (rpt gen_tac >> qexists `[(n,T,s0)]` >> simp[ao_source_trace_def]) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  irule ao_source_trace_extend >>
  qexists `LAST trace` >>
  (conj_tac >- (qexists `trace` >> simp[])) >>
  gvs[] >> metis_tac[ao_source_step_rules]
QED

Theorem ao_source_trace_replay:
  !trace ctx fn s0 n.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ao_source_prefix ctx fn s0 n
      (FST (HD trace)) (FST (SND (HD trace))) (SND (SND (HD trace))) ==>
    ao_source_prefix ctx fn s0 n
      (FST (LAST trace)) (FST (SND (LAST trace))) (SND (SND (LAST trace)))
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `trace` >> simp[ao_source_trace_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  drule ao_source_step_prefix >> simp[]
QED

Theorem ao_source_prefix_trace_iff:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s <=>
    ?trace. trace <> [] /\ HD trace = (n,T,s0) /\
      LAST trace = (k,phase,s) /\ ao_source_trace ctx fn trace
Proof
  rpt gen_tac >> eq_tac
  >- metis_tac[ao_source_prefix_has_trace] >>
  strip_tac >> drule ao_source_trace_replay >>
  disch_then (qspecl_then [`ctx`,`fn`,`s0`,`n`] mp_tac) >>
  simp[ao_source_prefix_rules]
QED

(* Split the ACTUAL list; neither direction chooses another history. *)
Theorem ao_source_trace_split:
  !front ctx fn a back.
    ao_source_trace ctx fn (front ++ a::back) <=>
    ao_source_trace ctx fn (front ++ [a]) /\ ao_source_trace ctx fn (a::back)
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `front`
  >- simp[ao_source_trace_def] >>
  rule_assum_tac (REWRITE_RULE [APPEND]) >>
  simp[NoAsms, ao_source_trace_def] >> metis_tac[]
QED

Theorem ao_source_trace_transition_split:
  !front ctx fn a b back.
    ao_source_trace ctx fn (front ++ a::b::back) <=>
    ao_source_trace ctx fn (front ++ [a]) /\
    ao_source_step ctx fn a b /\ ao_source_trace ctx fn (b::back)
Proof
  rpt gen_tac >> once_rewrite_tac[ao_source_trace_split] >>
  simp[ao_source_trace_def]
QED

(* The two endpoints carry the full common predecessor state, including
   previous-block selection. There is no intermediate PHI writing event. *)
Theorem ao_source_trace_phi_probe:
  !ctx fn k s bb p.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_trace ctx fn
      [(SUC k,T,s); (k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)]
Proof
  rpt strip_tac >> simp[ao_source_trace_def] >>
  metis_tac[ao_source_step_rules]
QED

(* Re-entry at the same label is a real edge, not the reflexive initial
   node. The phase change still distinguishes pre-PHI from sequential. *)
Theorem ao_source_trace_loop_probe:
  !ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
    ao_source_trace ctx fn [(k,F,s); (k,T,t)]
Proof
  rpt strip_tac >> simp[ao_source_trace_def] >>
  metis_tac[ao_source_step_rules]
QED

(* Avoidance and latest events refer to edges, including their post-node. *)
Definition ao_trace_avoids_def:
  ao_trace_avoids R [] = T /\
  ao_trace_avoids R [a] = T /\
  ao_trace_avoids R (a::b::rest) =
    (~R a b /\ ao_trace_avoids R (b::rest))
End

Theorem ao_trace_avoids_split:
  !front R a back.
    ao_trace_avoids R (front ++ a::back) <=>
    ao_trace_avoids R (front ++ [a]) /\ ao_trace_avoids R (a::back)
Proof
  Induct >> simp[ao_trace_avoids_def] >>
  rpt gen_tac >> Cases_on `front`
  >- simp[ao_trace_avoids_def] >>
  rule_assum_tac (REWRITE_RULE [APPEND]) >>
  simp[NoAsms, ao_trace_avoids_def] >> metis_tac[]
QED

Theorem ao_trace_last_event:
  !trace R.
    ao_trace_avoids R trace \/
    ?front a b back. trace = front ++ a::b::back /\
      R a b /\ ao_trace_avoids R (b::back)
Proof
  Induct >- simp[ao_trace_avoids_def] >>
  rpt gen_tac >> Cases_on `trace`
  >- simp[ao_trace_avoids_def] >>
  first_x_assum (qspec_then `R` strip_assume_tac)
  >- (Cases_on `R h h'` >> simp[ao_trace_avoids_def] >>
      qexistsl [`[]`,`h`,`h'`,`t`] >> simp[]) >>
  disj2_tac >> qexistsl [`h::front`,`a`,`b`,`back`] >> simp[]
QED

Definition ao_transition_writes_def:
  ao_transition_writes fn x (k,phase,s) (b:num # bool # venom_state) =
    if phase then
      (?bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ MEM x i.inst_outputs)
    else
      (?bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i /\
        ~is_terminator i.inst_opcode /\ MEM x i.inst_outputs)
End

Theorem ao_eval_phis_non_output:
  !is s p x. eval_phis s is = OK p /\
    (!i. MEM i is /\ i.inst_opcode = PHI ==> ~MEM x i.inst_outputs) ==>
    lookup_var x p = lookup_var x s
Proof
  Induct >- simp[eval_phis_def] >>
  rpt gen_tac >> simp[eval_phis_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      AllCaseEqs()] >> metis_tac[ao_eval_one_phi_output]
QED

Theorem ao_source_step_non_writer:
  !ctx fn a b. ao_source_step ctx fn a b ==>
    !x. ~ao_transition_writes fn x a b ==>
    lookup_var x (SND (SND a)) = lookup_var x (SND (SND b))
Proof
  ho_match_mp_tac ao_source_step_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[ao_transition_writes_def] >> rpt strip_tac
  >- (`lookup_var x p = lookup_var x s` by
        (irule ao_eval_phis_non_output >> metis_tac[]) >>
      gvs[lookup_var_def])
  >- (drule_all venomInstPropsTheory.step_preserves_non_output_vars >>
      simp[lookup_var_def]) >>
  drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
  disch_then (qspec_then `x` mp_tac) >> simp[lookup_var_def]
QED

Theorem ao_source_trace_non_writer:
  !trace ctx fn x.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ao_trace_avoids (ao_transition_writes fn x) trace ==>
    lookup_var x (SND (SND (HD trace))) =
    lookup_var x (SND (SND (LAST trace)))
Proof
  Induct >> simp[ao_source_trace_def, ao_trace_avoids_def] >>
  rpt gen_tac >> Cases_on `trace` >>
  simp[ao_source_trace_def, ao_trace_avoids_def] >>
  rpt strip_tac >> drule ao_source_step_non_writer >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >>
  metis_tac[HD, LAST_DEF, NOT_CONS_NIL]
QED

Theorem ao_source_step_sequential:
  !ctx fn k s j t. ao_source_step ctx fn (k,F,s) (j,F,t) ==>
    j = k /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    ?bb inst u. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK u /\
      t = u with vs_inst_idx := SUC s.vs_inst_idx
Proof
  rpt gen_tac >> simp[Once ao_source_step_cases] >> rpt strip_tac >>
  gvs[] >> drule_all venomInstPropsTheory.step_preserves_control_flow >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem ao_source_trace_sequential_positions:
  !trace ctx fn.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    EVERY (\a. ~FST (SND a)) trace ==>
    !i. i < LENGTH trace ==>
      FST (EL i trace) = FST (HD trace) /\
      (SND (SND (EL i trace))).vs_current_bb =
        (SND (SND (HD trace))).vs_current_bb /\
      (SND (SND (EL i trace))).vs_inst_idx =
        (SND (SND (HD trace))).vs_inst_idx + i
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `trace` >- simp[] >>
  simp[ao_source_trace_def] >> rpt strip_tac >>
  PairCases_on `h` >> PairCases_on `h'` >> gvs[] >>
  drule ao_source_step_sequential >> strip_tac >>
  Cases_on `i` >- simp[] >>
  first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem ao_source_step_entry:
  !ctx fn k s j t. ao_source_step ctx fn (k,T,s) (j,F,t) ==>
    k = SUC j /\ t.vs_current_bb = s.vs_current_bb /\
    ?bb p. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK p /\
      t = p with vs_inst_idx := phi_prefix_length bb.bb_instructions
Proof
  rpt gen_tac >> simp[Once ao_source_step_cases] >> rpt strip_tac >>
  gvs[] >> drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
  simp[] >> metis_tac[]
QED

Theorem ao_source_step_no_entry_entry:
  !ctx fn k s j t. ~ao_source_step ctx fn (k,T,s) (j,T,t)
Proof
  simp[Once ao_source_step_cases]
QED

Theorem ao_source_step_exit:
  !ctx fn k s j t. ao_source_step ctx fn (k,F,s) (j,T,t) ==>
    j = k /\ t.vs_prev_bb = SOME s.vs_current_bb /\
    (!x. lookup_var x s = lookup_var x t) /\
    ?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t /\
      ~t.vs_halted
Proof
  rpt gen_tac >> simp[Once ao_source_step_cases] >> rpt strip_tac >> gvs[] >>
  drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all venomExecPropsTheory.step_inst_base_term_prev_bb >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem ao_source_step_exit_cfg:
  !ctx fn k s j t.
    wf_function fn /\ fn_inst_wf fn /\
    ao_source_step ctx fn (k,F,s) (j,T,t) ==>
    fn_cfg_edge fn s.vs_current_bb t.vs_current_bb
Proof
  rpt strip_tac >> drule ao_source_step_exit >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst = EL s.vs_inst_idx bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def, MEM_EL] >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all venomExecProofsTheory.step_inst_base_term_succs >> strip_tac >>
  simp[fn_cfg_edge_def] >> qexists `bb` >> simp[] >>
  gvs[bb_well_formed_def, bb_succs_def, LAST_EL, MEM_nub, MEM_REVERSE] >>
  Cases_on `bb.bb_instructions` >- fs[] >>
  qpat_x_assum `MEM t.vs_current_bb (get_successors _)` mp_tac >>
  simp[MEM_nub, MEM_REVERSE]
QED

(* Retain real visit edges, including equal-label self-loops. *)
Definition ao_trace_path_def:
  ao_trace_path ([]:(num # bool # venom_state) list) = [] /\
  ao_trace_path [a] = [(SND (SND a)).vs_current_bb] /\
  ao_trace_path (a::b::rest) =
    if FST (SND b) then
      (SND (SND a)).vs_current_bb :: ao_trace_path (b::rest)
    else ao_trace_path (b::rest)
End

Theorem ao_trace_path_shape:
  !trace. trace <> [] ==>
    ao_trace_path trace <> [] /\
    LAST (ao_trace_path trace) = (SND (SND (LAST trace))).vs_current_bb /\
    (!lbl. MEM lbl (ao_trace_path trace) ==>
      ?a. MEM a trace /\ lbl = (SND (SND a)).vs_current_bb)
Proof
  Induct >- simp[] >> gen_tac >> Cases_on `trace`
  >- simp[ao_trace_path_def] >>
  simp[ao_trace_path_def] >> Cases_on `FST (SND h')` >>
  simp[] >> rpt strip_tac >> metis_tac[MEM, LAST_DEF, NOT_CONS_NIL]
QED

Theorem ao_source_step_stutter:
  !ctx fn a b. ao_source_step ctx fn a b /\ ~FST (SND b) ==>
    (SND (SND a)).vs_current_bb = (SND (SND b)).vs_current_bb
Proof
  rpt gen_tac >> PairCases_on `a` >> PairCases_on `b` >>
  Cases_on `a1` >> Cases_on `b1` >> simp[] >> strip_tac
  >- (drule ao_source_step_entry >> simp[]) >>
  drule ao_source_step_sequential >> simp[]
QED

Theorem ao_source_trace_path:
  !trace ctx fn.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    wf_function fn /\ fn_inst_wf fn ==>
    is_fn_path fn (ao_trace_path trace) /\
    HD (ao_trace_path trace) = (SND (SND (HD trace))).vs_current_bb
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `trace`
  >- simp[ao_trace_path_def, is_fn_path_def] >>
  simp[ao_source_trace_def] >> strip_tac >>
  rule_assum_tac (REWRITE_RULE [NOT_CONS_NIL]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `FST (SND h')`
  >- (PairCases_on `h` >> PairCases_on `h'` >> gvs[] >>
      Cases_on `h1`
      >- metis_tac[ao_source_step_no_entry_entry] >>
      drule_all ao_source_step_exit_cfg >> strip_tac >>
      simp[ao_trace_path_def] >>
      qmatch_goalsub_abbrev_tac `is_fn_path fn (_::path)` >>
      `path <> []` by metis_tac[ao_trace_path_shape, NOT_CONS_NIL] >>
      Cases_on `path` >> gvs[is_fn_path_def]) >>
  drule_all ao_source_step_stutter >> strip_tac >>
  simp[ao_trace_path_def]
QED

Theorem ao_source_trace_last_step:
  !trace ctx fn.
    2 <= LENGTH trace /\ ao_source_trace ctx fn trace ==>
    ?front a b. trace = front ++ [a;b] /\ LAST trace = b /\
      ao_source_trace ctx fn (front ++ [a]) /\ ao_source_step ctx fn a b
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `trace`
  >- simp[] >>
  Cases_on `t`
  >- (simp[ao_source_trace_def] >> strip_tac >>
      qexistsl [`[]`,`h`,`h'`] >> simp[ao_source_trace_def]) >>
  strip_tac >>
  first_x_assum (qspecl_then [`ctx`,`fn`] mp_tac) >>
  (impl_tac >- gvs[ao_source_trace_def]) >> strip_tac >>
  qexistsl [`h::front`,`a`,`b`] >> simp[] >>
  `ao_source_trace ctx fn ((h::front) ++ [a;b])` by metis_tac[APPEND] >>
  qpat_x_assum `ao_source_trace ctx fn ((_::_) ++ _)` mp_tac >>
  once_rewrite_tac[ao_source_trace_transition_split] >> simp[]
QED

Theorem ao_source_trace_selected_edge:
  !trace ctx fn.
    2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\
    FST (SND (LAST trace)) ==>
    ?front a b. trace = front ++ [a;b] /\ LAST trace = b /\
      ~FST (SND a) /\ FST (SND b) /\
      ao_source_trace ctx fn (front ++ [a]) /\ ao_source_step ctx fn a b /\
      (SND (SND b)).vs_prev_bb = SOME (SND (SND a)).vs_current_bb /\
      (!x. lookup_var x (SND (SND a)) = lookup_var x (SND (SND b))) /\
      LAST (ao_trace_path (front ++ [a])) = (SND (SND a)).vs_current_bb
Proof
  rpt strip_tac >> drule_all ao_source_trace_last_step >> strip_tac >>
  qexistsl [`front`,`a`,`b`] >> simp[] >>
  `LAST (ao_trace_path (front ++ [a])) = (SND (SND a)).vs_current_bb` by
    (mp_tac (Q.SPEC `front ++ [a]` ao_trace_path_shape) >>
     simp[LAST_APPEND_CONS]) >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  Cases_on `a1` >- metis_tac[ao_source_step_no_entry_entry] >>
  drule ao_source_step_exit >> simp[]
QED

Theorem ao_trace_avoids_source:
  !trace P. trace <> [] /\ ~P (LAST trace) /\
    ao_trace_avoids (\a b. P a) trace ==> EVERY (\a. ~P a) trace
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `trace` >>
  simp[ao_trace_avoids_def] >> metis_tac[LAST_DEF, NOT_CONS_NIL]
QED

Theorem ao_trace_final_visit_split:
  !trace. trace <> [] /\ ~FST (SND (LAST trace)) ==>
    EVERY (\a. ~FST (SND a)) trace \/
    ?front a b back. trace = front ++ a::b::back /\
      FST (SND a) /\ EVERY (\c. ~FST (SND c)) (b::back)
Proof
  rpt strip_tac >>
  qspec_then `trace` (qspec_then `\a b. FST (SND a)` strip_assume_tac)
    ao_trace_last_event
  >- (disj1_tac >> ho_match_mp_tac ao_trace_avoids_source >> simp[]) >>
  `EVERY (\c. ~FST (SND c)) (b::back)` by
    (ho_match_mp_tac ao_trace_avoids_source >> simp[] >>
     metis_tac[LAST_APPEND_CONS, LAST_DEF]) >>
  disj2_tac >> qexistsl [`front`,`a`,`b`,`back`] >> gvs[]
QED

Theorem ao_source_trace_final_visit:
  !trace ctx fn.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ~FST (SND (LAST trace)) ==>
    EVERY (\a. ~FST (SND a)) trace \/
    ?front k s j t back bb p.
      trace = front ++ (k,T,s)::(j,F,t)::back /\
      EVERY (\c. ~FST (SND c)) ((j,F,t)::back) /\
      ao_source_trace ctx fn (front ++ [(k,T,s)]) /\
      ao_source_trace ctx fn ((j,F,t)::back) /\
      ao_source_step ctx fn (k,T,s) (j,F,t) /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK p /\
      t = p with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
      (!i. i < LENGTH ((j,F,t)::back) ==>
        (SND (SND (EL i ((j,F,t)::back)))).vs_inst_idx =
          phi_prefix_length bb.bb_instructions + i)
Proof
  rpt strip_tac >> drule_all ao_trace_final_visit_split >> strip_tac
  >- simp[] >>
  disj2_tac >>
  `ao_source_trace ctx fn (front ++ [a]) /\ ao_source_step ctx fn a b /\
    ao_source_trace ctx fn (b::back)` by
    metis_tac[ao_source_trace_transition_split] >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  drule ao_source_step_entry >> strip_tac >>
  qexistsl [`front`,`a0`,`a2`,`b0`,`back`,`bb`,`p`] >> simp[] >>
  gvs[] >>
  qspec_then `(b0,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)::back`
    mp_tac ao_source_trace_sequential_positions >> simp[] >> metis_tac[]
QED

Theorem ao_source_trace_single_visit_label:
  !tail ctx fn a.
    ao_source_trace ctx fn (a::tail) /\
    EVERY (\b. ~FST (SND b)) tail ==>
    EVERY (\b. (SND (SND b)).vs_current_bb =
      (SND (SND a)).vs_current_bb) (a::tail)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[ao_source_trace_def] >> strip_tac >>
  drule_all ao_source_step_stutter >> strip_tac >>
  first_x_assum (qspecl_then [`ctx`,`fn`,`h`] mp_tac) >>
  simp[]
QED

Theorem ao_source_trace_crosses_index:
  !trace ctx fn k s j t bb r inst.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    EVERY (\a. ~FST (SND a)) trace /\
    HD trace = (k,F,s) /\ LAST trace = (j,F,t) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb r = SOME inst /\ s.vs_inst_idx <= r /\ r < t.vs_inst_idx ==>
    ?front q u v back.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      ?w. step_inst q ctx inst u = OK w /\ v = w with vs_inst_idx := SUC r
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `trace`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[ao_source_trace_def] >> strip_tac >> gvs[] >>
  PairCases_on `h'` >> gvs[] >>
  drule ao_source_step_sequential >> strip_tac >>
  Cases_on `r = s.vs_inst_idx`
  >- (qexistsl [`[]`,`k`,`s`,`h'2`,`t'`] >>
      gvs[]) >>
  `h'2.vs_inst_idx <= r` by decide_tac >>
  first_x_assum (qspecl_then [`ctx`,`fn`,`bb`,`r`,`inst`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexistsl [`(k,F,s)::front`,`q`,`u'`,`v`,`back`] >>
  simp[]
QED

Theorem non_terminator_before_terminator:
  !bb r inst n term.
    bb_well_formed bb /\
    get_instruction bb r = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    get_instruction bb n = SOME term /\
    is_terminator term.inst_opcode ==> r < n
Proof
  rpt strip_tac >>
  `r < LENGTH bb.bb_instructions /\ inst = EL r bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `n < LENGTH bb.bb_instructions /\ term = EL n bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `n = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[venomWfTheory.bb_well_formed_def] >>
  `r <> n` by metis_tac[] >> decide_tac
QED

Theorem ao_source_trace_crosses_before_exit:
  !trace ctx fn k s j t bb r inst out.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    EVERY (\a. ~FST (SND a)) trace /\
    HD trace = (k,F,s) /\ LAST trace = (j,F,t) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb r = SOME inst /\ s.vs_inst_idx <= r /\
    ao_source_step ctx fn (j,F,t) (j,T,out) /\
    wf_function fn /\ ~is_terminator inst.inst_opcode ==>
    ?front q u v back.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      ?w. step_inst q ctx inst u = OK w /\ v = w with vs_inst_idx := SUC r
Proof
  rpt strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (Cases_on `trace` >> gvs[] >>
     drule_all ao_source_trace_single_visit_label >>
     rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `LAST ((k,F,s)::t')` mp_tac) >>
     simp[LAST_MEM]) >>
  drule ao_source_step_exit >> strip_tac >>
  `bb' = bb` by gvs[] >> gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `r < t.vs_inst_idx` by
    (irule non_terminator_before_terminator >>
     metis_tac[]) >>
  drule_all ao_source_trace_crosses_index >> simp[]
QED

Theorem ao_trace_label_exit[local]:
  !trace lbl.
    MEM lbl (MAP (\a. (SND (SND a)).vs_current_bb) trace) /\
    lbl <> (SND (SND (LAST trace))).vs_current_bb ==>
    ?front a b back. trace = front ++ a::b::back /\
      (SND (SND a)).vs_current_bb = lbl /\
      (SND (SND b)).vs_current_bb <> lbl
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `trace`
  >- simp[] >>
  strip_tac >>
  Cases_on `(SND (SND h)).vs_current_bb = lbl /\
            (SND (SND h')).vs_current_bb <> lbl`
  >- (qexistsl [`[]`,`h`,`h'`,`t`] >> simp[]) >>
  first_x_assum (qspec_then `lbl` mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  qexistsl [`h::front`,`a`,`b`,`back`] >> simp[]
QED

Theorem ao_source_trace_interior_execution:
  !trace ctx fn bb r inst.
    trace <> [] /\ ao_source_trace ctx fn trace /\ wf_function fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    get_instruction bb r = SOME inst /\
    phi_prefix_length bb.bb_instructions <= r /\
    ~is_terminator inst.inst_opcode /\ MEM bb.bb_label (ao_trace_path trace) /\
    bb.bb_label <> (SND (SND (HD trace))).vs_current_bb /\
    bb.bb_label <> (SND (SND (LAST trace))).vs_current_bb ==>
    ?front q u v back w.
      trace = front ++ (q,F,u)::(q,F,v)::back /\
      u.vs_current_bb = bb.bb_label /\ u.vs_inst_idx = r /\
      ao_source_step ctx fn (q,F,u) (q,F,v) /\
      step_inst q ctx inst u = OK w /\ v = w with vs_inst_idx := SUC r
Proof
  rpt strip_tac >>
  `MEM bb.bb_label (MAP (\a. (SND (SND a)).vs_current_bb) trace)` by
    (drule ao_trace_path_shape >> strip_tac >>
     fs[MEM_MAP] >> metis_tac[]) >>
  drule_all ao_trace_label_exit >> strip_tac >>
  `ao_source_trace ctx fn (front ++ [a]) /\ ao_source_step ctx fn a b` by
    metis_tac[ao_source_trace_transition_split] >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  `b1` by
    (Cases_on `b1` >> gvs[] >> drule ao_source_step_stutter >> simp[]) >>
  `~a1` by
    (Cases_on `a1` >> gvs[] >> metis_tac[ao_source_step_no_entry_entry]) >> gvs[] >>
  qspec_then `front ++ [(a0,F,a2)]` (qspecl_then [`ctx`,`fn`] mp_tac)
    ao_source_trace_final_visit >>
  simp[] >> strip_tac
  >- (Cases_on `front` >> gvs[] >>
      drule ao_source_trace_single_visit_label >>
      simp[] >> rewrite_tac[EVERY_MEM] >>
      disch_then (qspec_then `(a0,F,a2)` mp_tac) >>
      simp[]) >>
  qmatch_asmsub_abbrev_tac `ao_source_trace ctx fn ((j,F,start)::back')` >>
  `LAST ((j,F,start)::back') = (a0,F,a2)` by
    (qpat_x_assum `front ++ [_] = _` mp_tac >>
     rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     disch_then (mp_tac o AP_TERM ``LAST : (num # bool # venom_state) list -> num # bool # venom_state``) >> simp[LAST_APPEND_CONS]) >>
  `start.vs_current_bb = bb.bb_label` by
    (drule_all ao_source_trace_single_visit_label >>
     rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `LAST ((j,F,start)::back')` mp_tac) >>
     simp[LAST_MEM]) >>
  `start.vs_current_bb = s.vs_current_bb` by
    (drule ao_source_step_stutter >> simp[]) >>
  `bb' = bb` by gvs[] >>
  `b0 = a0` by (drule ao_source_step_exit >> simp[]) >>
  `start.vs_inst_idx <= r` by simp[Abbr `start`] >>
  qspec_then `(j,F,start)::back'` (qspecl_then [`ctx`,`fn`] mp_tac)
    ao_source_trace_crosses_before_exit >>
  simp[] >>
  disch_then (qspecl_then [`r`,`inst`,`b2`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexistsl [`front' ++ [(k,T,s)] ++ front''`,`q`,`u`,
             `back'' ++ (a0,T,b2)::back`,`w`] >>
  simp[] >>
  `front ++ [(a0,F,a2)] =
    (front' ++ [(k,T,s)]) ++ ((j,F,start)::back')` by
    gvs[APPEND_ASSOC] >>
  qpat_x_assum `front ++ [_] = (front' ++ _) ++ _` mp_tac >>
  gvs[APPEND_ASSOC]
QED

Theorem ao_source_trace_sequential_bounds:
  !trace ctx fn a.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    EVERY (\v. ~FST (SND v)) trace /\ MEM a trace ==>
    (SND (SND a)).vs_current_bb =
      (SND (SND (HD trace))).vs_current_bb /\
    (SND (SND (HD trace))).vs_inst_idx <= (SND (SND a)).vs_inst_idx /\
    (SND (SND a)).vs_inst_idx <= (SND (SND (LAST trace))).vs_inst_idx
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`trace`, `ctx`, `fn`] mp_tac
    ao_source_trace_sequential_positions >> simp[] >> disch_tac >>
  fs[MEM_EL] >>
  first_assum (qspec_then `n` mp_tac) >> simp[] >>
  first_x_assum (qspec_then `PRE (LENGTH trace)` mp_tac) >>
  simp[LAST_EL] >> rpt strip_tac >> gvs[]
QED

Theorem ao_source_trace_sequential_edge_bound:
  !trace ctx fn front a b back.
    ao_source_trace ctx fn trace /\
    EVERY (\v. ~FST (SND v)) trace /\
    trace = front ++ a::b::back ==>
    (SND (SND a)).vs_inst_idx <
      (SND (SND (LAST trace))).vs_inst_idx
Proof
  rpt gen_tac >> strip_tac >>
  `trace <> [] /\ LENGTH front < LENGTH trace /\
   EL (LENGTH front) trace = a` by simp[EL_APPEND_EQN] >>
  qspecl_then [`trace`, `ctx`, `fn`] mp_tac
    ao_source_trace_sequential_positions >> simp[] >> disch_tac >>
  first_assum (qspec_then `LENGTH front` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (qspec_then `LENGTH front + SUC (LENGTH back)` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[LAST_EL, EL_APPEND_EQN]
QED

Theorem ao_source_trace_lookup_origin:
  !trace ctx fn x value.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x (SND (SND (LAST trace))) = SOME value ==>
    ?front a b back.
      trace = front ++ a::b::back /\ ao_transition_writes fn x a b
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`trace`, `ao_transition_writes fn x`] strip_assume_tac
    ao_trace_last_event
  >- (drule_all ao_source_trace_non_writer >> simp[]) >>
  metis_tac[]
QED

Theorem ao_source_trace_initial_visit:
  !tail ctx fn k s.
    ao_source_trace ctx fn ((k,F,s)::tail) ==>
    EVERY (\a. ~FST (SND a)) ((k,F,s)::tail) \/
    ?front j u out back.
      (k,F,s)::tail = front ++ (j,F,u)::(j,T,out)::back /\
      EVERY (\a. ~FST (SND a)) (front ++ [(j,F,u)]) /\
      HD (front ++ [(j,F,u)]) = (k,F,s) /\
      ao_source_trace ctx fn (front ++ [(j,F,u)]) /\
      ao_source_step ctx fn (j,F,u) (j,T,out) /\
      ao_source_trace ctx fn ((j,T,out)::back)
Proof
  Induct_on `tail` >- simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[ao_source_trace_def] >> strip_tac >>
  Cases_on `h1`
  >- (drule ao_source_step_exit >> strip_tac >> gvs[] >>
      qexistsl [`[]`, `h0`, `s`, `h2`, `tail`] >>
      simp[ao_source_trace_def]) >>
  gvs[] >> first_x_assum drule >> strip_tac
  >- simp[] >>
  disj2_tac >> qexistsl [`(k,F,s)::front`, `j`, `u`, `out`, `back`] >>
  simp[ao_source_trace_def] >>
  Cases_on `front` >> gvs[ao_source_trace_def]
QED

Theorem ao_source_step_labels:
  !ctx fn a b. ao_source_step ctx fn a b ==>
    (SND (SND b)).vs_labels = (SND (SND a)).vs_labels
Proof
  ho_match_mp_tac ao_source_step_ind >> simp[] >> rpt strip_tac >>
  metis_tac[venomExecPropsTheory.step_inst_preserves_labels_always,
            venomExecPropsTheory.eval_phis_preserves_labels]
QED

Theorem ao_source_trace_member_labels[local]:
  !trace ctx fn a b.
    ao_source_trace ctx fn (a::trace) /\ MEM b (a::trace) ==>
    (SND (SND b)).vs_labels = (SND (SND a)).vs_labels
Proof
  Induct >> simp[ao_source_trace_def] >> rpt gen_tac >>
  strip_tac >> gvs[ao_source_trace_def] >>
  drule ao_source_step_labels >> strip_tac >>
  first_x_assum (qspecl_then [`ctx`,`fn`,`h`,`b`] mp_tac) >> simp[]
QED

Theorem ao_source_trace_labels:
  !ctx fn trace k p u h q t.
    ao_source_trace ctx fn trace /\ MEM (k,p,u) trace /\ MEM (h,q,t) trace ==>
    t.vs_labels = u.vs_labels
Proof
  rpt gen_tac >> Cases_on `trace` >- simp[] >> strip_tac >>
  qspecl_then [`t'`,`ctx`,`fn`,`h'`] mp_tac ao_source_trace_member_labels >>
  simp[] >> strip_tac >>
  first_assum (qspec_then `(k,p,u)` mp_tac) >>
  first_x_assum (qspec_then `(h,q,t)` mp_tac) >>
  fs[listTheory.MEM] >> rpt strip_tac >> gvs[]
QED
