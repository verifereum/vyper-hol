Theory algebraicOptReachabilityProofs
Ancestors
  algebraicOptDefs venomExecSemantics venomState venomInstProps venomExecProofs
  venomWfProps venomInst unitShapeDefs passSimulationDefs dfgAnalysisProps

(* A chain boundary must retain a Boolean value at value-sensitive uses;
   at truthy uses the root word itself suffices. *)
Theorem ao_two_iszero_boundary:
  !w:bytes32.
    (bool_to_word (bool_to_word (w = 0w) = 0w) = 0w <=> w = 0w) /\
    bool_to_word (bool_to_word (w = 0w) = 0w) = bool_to_word (w <> 0w)
Proof
  gen_tac >> Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

(* Reads in a parallel PHI batch all use s, even if one output is an
   input of the other. This equation also covers loop back edges. *)
Theorem ao_parallel_phi_pair:
  !s i j x y a b.
    i.inst_opcode = PHI /\ j.inst_opcode = PHI /\
    eval_one_phi s i = SOME (x,a) /\
    eval_one_phi s j = SOME (y,b) ==>
    eval_phis s [i;j] = OK (update_var x a (update_var y b s))
Proof
  rpt strip_tac >> simp[eval_phis_def]
QED

(* A consumer-level provenance interface cannot read a producer's
   operands from a post-PHI environment: its source environment is s. *)
Theorem ao_phi_selected_operand:
  !s inst prev op out w.
    inst.inst_outputs = [out] /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME op /\
    eval_operand op s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rpt strip_tac >> simp[eval_one_phi_def]
QED

(* One producer step exposes precisely the value a chain consumer needs.
   It does not assert that the source operand stays unchanged on a loop. *)
Theorem ao_iszero_producer_step:
  !inst s op out w.
    inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
    inst.inst_outputs = [out] /\ eval_operand op s = SOME w ==>
    step_inst_base inst s = OK (update_var out (bool_to_word (w = 0w)) s)
Proof
  rpt strip_tac >> simp[step_inst_base_def, exec_pure1_def]
QED

(* T marks a run_blocks entry, F a sequential instruction boundary.
   Residual fuel is explicit: PHI processing consumes the block fuel,
   while sequential steps do not. No acyclicity premise excludes loops. *)
Inductive ao_source_prefix:
  (!ctx fn s0 n.
    ao_source_prefix ctx fn s0 n n T s0) /\
  (!ctx fn s0 n k s bb p.
    ao_source_prefix ctx fn s0 n (SUC k) T s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_prefix ctx fn s0 n k F
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!ctx fn s0 n k s bb inst t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t ==>
    ao_source_prefix ctx fn s0 n k F
      (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!ctx fn s0 n k s bb inst t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t /\ ~t.vs_halted ==>
    ao_source_prefix ctx fn s0 n k T t)
End

(* This tests both loop re-entry (t may have the same block label as s)
   and the separation between predecessor and post-PHI environments. *)
Theorem ao_source_prefix_edge_phis:
  !ctx fn s0 n k s bb inst t next p.
    ao_source_prefix ctx fn s0 n (SUC k) F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst (SUC k) ctx inst s = OK t /\ ~t.vs_halted /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME next /\
    eval_phis t next.bb_instructions = OK p ==>
    ao_source_prefix ctx fn s0 n k F
      (p with vs_inst_idx := phi_prefix_length next.bb_instructions)
Proof
  rpt strip_tac >> irule (cj 2 ao_source_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule (cj 4 ao_source_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ao_source_prefix_compose:
  !ctx fn s0 n k s j phase t.
    ao_source_prefix ctx fn s0 n k T s /\
    ao_source_prefix ctx fn s k j phase t ==>
    ao_source_prefix ctx fn s0 n j phase t
Proof
  `!ctx fn s k j phase t.
      ao_source_prefix ctx fn s k j phase t ==>
      !s0 n. ao_source_prefix ctx fn s0 n k T s ==>
        ao_source_prefix ctx fn s0 n j phase t` suffices_by metis_tac[] >>
  ho_match_mp_tac ao_source_prefix_ind >> rpt strip_tac >>
  metis_tac[ao_source_prefix_rules]
QED

Theorem ao_source_prefix_phi_handoff:
  !ctx fn s0 n k s bb p.
    ao_source_prefix ctx fn s0 n (SUC k) T s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_prefix ctx fn s0 n k F
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    lookup_block
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
      fn.fn_blocks = SOME bb
Proof
  rpt strip_tac
  >- (irule (cj 2 ao_source_prefix_rules) >> metis_tac[]) >>
  drule eval_phis_preserves_current_bb >> simp[]
QED

Theorem ao_exec_block_prefix:
  !ctx fn s0 n k s bb t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    exec_block k ctx bb s = OK t ==>
    ao_source_prefix ctx fn s0 n k T t /\ ~t.vs_halted
Proof
  `!ctx fn s0 n k s bb t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    exec_block k ctx bb s = OK t ==>
    ao_source_prefix ctx fn s0 n k T t`
    suffices_by metis_tac[exec_block_OK_not_halted] >>
  rpt gen_tac >>
  qid_spec_tac `t` >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, AllCaseEqs()] >> rpt strip_tac
  >~ [`is_terminator inst.inst_opcode`]
  >- (irule (cj 4 ao_source_prefix_rules) >> metis_tac[]) >>
  `s''.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `ao_source_prefix ctx fn s0 n k F
     (s'' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 3 ao_source_prefix_rules) >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then
    `s'' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[]
QED

Theorem ao_source_prefix_block_edge:
  !ctx fn s0 n k s bb p t.
    ao_source_prefix ctx fn s0 n (SUC k) T s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p /\
    exec_block k ctx bb
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t ==>
    ao_source_prefix ctx fn s0 n k T t /\
    run_blocks (SUC k) ctx fn s = run_blocks k ctx fn t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_source_prefix_phi_handoff >> strip_tac >>
  drule_all ao_exec_block_prefix >> strip_tac >>
  simp[Once run_blocks_def]
QED

Theorem ao_exec_block_terminal_prefix:
  !ctx fn s0 n k s bb r.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    exec_block k ctx bb s = r /\
    (!t. r <> OK t) /\ (!e. r <> Error e) ==>
    ?u inst. ao_source_prefix ctx fn s0 n k F u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst /\
      (step_inst k ctx inst u = r \/
       ?t. step_inst k ctx inst u = OK t /\
           is_terminator inst.inst_opcode /\ t.vs_halted /\ r = Halt t)
Proof
  rpt gen_tac >> qid_spec_tac `r` >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, AllCaseEqs()] >> rpt strip_tac
  >~ [`is_terminator inst.inst_opcode`, `Halt t = r`]
  >- (qexistsl [`s`, `inst`] >> metis_tac[])
  >~ [`step_inst k ctx inst s = Halt t`]
  >- (qexistsl [`s`, `inst`] >> simp[])
  >~ [`step_inst k ctx inst s = Abort a t`]
  >- (qexistsl [`s`, `inst`] >> simp[])
  >~ [`step_inst k ctx inst s = IntRet a t`]
  >- (qexistsl [`s`, `inst`] >> simp[]) >>
  `s''.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `ao_source_prefix ctx fn s0 n k F
     (s'' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 3 ao_source_prefix_rules) >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then
    `s'' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[]
QED

Theorem ao_run_blocks_terminal_prefix:
  !ctx fn s0 n k s r.
    ao_source_prefix ctx fn s0 n k T s /\
    run_blocks k ctx fn s = r /\
    (!t. r <> OK t) /\ (!e. r <> Error e) ==>
    ?j u bb inst. ao_source_prefix ctx fn s0 n j F u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst /\
      (step_inst j ctx inst u = r \/
       ?t. step_inst j ctx inst u = OK t /\
           is_terminator inst.inst_opcode /\ t.vs_halted /\ r = Halt t)
Proof
  rpt gen_tac >> qid_spec_tac `r` >> qid_spec_tac `s` >>
  Induct_on `k` >- simp[run_blocks_def] >>
  rpt strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def, AllCaseEqs()] >> rpt strip_tac
  >> gvs[exec_block_OK_not_halted]
  >>~- ([`eval_phis s bb.bb_instructions = OK p`],
    drule_all ao_source_prefix_phi_handoff >> strip_tac
    >>~- ([`exec_block k ctx bb z = OK t`],
      drule_all ao_exec_block_prefix >> strip_tac >> gvs[] >>
      first_x_assum irule >> simp[]) >>
    metis_tac[ao_exec_block_terminal_prefix]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> gvs[]
QED

Theorem ao_eval_phis_value_origin:
  !s is p x w. eval_phis s is = OK p /\ lookup_var x p = SOME w ==>
    lookup_var x s = SOME w \/
    ?i. MEM i is /\ i.inst_opcode = PHI /\
        eval_one_phi s i = SOME (x,w)
Proof
  gen_tac >> Induct_on `is` >- simp[eval_phis_def] >>
  rpt gen_tac >>
  simp[eval_phis_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem ao_eval_one_phi_output:
  !s i x w. eval_one_phi s i = SOME (x,w) ==> MEM x i.inst_outputs
Proof
  rpt gen_tac >> simp[eval_one_phi_def, AllCaseEqs()] >>
  rpt strip_tac >> simp[]
QED

Theorem ao_source_prefix_value_origin:
  !ctx fn s0 n k phase s x w.
    ao_source_prefix ctx fn s0 n k phase s /\
    lookup_var x s0 = NONE /\ lookup_var x s = SOME w ==>
    (?j u bb i t.
      ao_source_prefix ctx fn s0 n j F u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME i /\
      MEM x i.inst_outputs /\ step_inst j ctx i u = OK t /\
      lookup_var x t = SOME w) \/
    (?j u bb p i.
      ao_source_prefix ctx fn s0 n (SUC j) T u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis u bb.bb_instructions = OK p /\
      MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
      eval_one_phi u i = SOME (x,w))
Proof
  `!ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    !x w. lookup_var x s0 = NONE /\ lookup_var x s = SOME w ==>
    (?j u bb i t.
      ao_source_prefix ctx fn s0 n j F u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME i /\
      MEM x i.inst_outputs /\ step_inst j ctx i u = OK t /\
      lookup_var x t = SOME w) \/
    (?j u bb p i.
      ao_source_prefix ctx fn s0 n (SUC j) T u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis u bb.bb_instructions = OK p /\
      MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
      eval_one_phi u i = SOME (x,w))` suffices_by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> disch_then irule >> simp[]) >>
  ho_match_mp_tac ao_source_prefix_strongind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >>
      `lookup_var x p = SOME w` by gvs[lookup_var_def] >>
      drule_all ao_eval_phis_value_origin >> strip_tac
      >- (first_x_assum irule >> simp[]) >>
      disj2_tac >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> metis_tac[])
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by gvs[lookup_var_def] >>
      Cases_on `MEM x inst.inst_outputs`
      >- (disj1_tac >> qexistsl [`k`, `s`, `bb`, `inst`, `t`] >> simp[]) >>
      drule_all step_preserves_non_output_vars >> strip_tac >>
      first_x_assum irule >> gvs[]) >>
  rpt strip_tac >> drule_all step_terminator_preserves_vars >>
  disch_then (qspec_then `x` mp_tac) >> strip_tac >>
  first_x_assum irule >> gvs[]
QED

Theorem ao_iszero_historical_operand:
  !ctx fn s0 n k phase s i op x w.
    ssa_form fn /\ MEM i (fn_insts fn) /\
    i.inst_opcode = ISZERO /\ i.inst_operands = [op] /\ i.inst_outputs = [x] /\
    ao_source_prefix ctx fn s0 n k phase s /\
    lookup_var x s0 = NONE /\ lookup_var x s = SOME w ==>
    ?j u bb t a.
      ao_source_prefix ctx fn s0 n j F u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME i /\
      step_inst j ctx i u = OK t /\
      eval_operand op u = SOME a /\ w = bool_to_word (a = 0w)
Proof
  rpt strip_tac >> drule_all ao_source_prefix_value_origin >> strip_tac
  >- (rename1 `MEM x h.inst_outputs` >>
      `MEM h (fn_insts fn)` by
        (gvs[fn_insts_def, fn_insts_blocks_def, lookup_block_def,
             get_instruction_def, AllCaseEqs()] >>
         simp[MEM_fn_insts_blocks_iff] >> qexists `bb` >>
         metis_tac[execEquivParamBaseTheory.FIND_MEM, listTheory.EL_MEM]) >>
      `h = i` by
        (irule ssa_outputs_same_inst >>
         gvs[fn_insts_def] >> metis_tac[]) >>
      gvs[] >> qexistsl [`j`, `u`, `bb`, `t`] >> simp[] >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def, exec_pure1_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  rename1 `eval_one_phi u h = SOME (x,w)` >>
  `MEM h (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> qexists `bb` >>
     metis_tac[execEquivParamBaseTheory.FIND_MEM, lookup_block_def]) >>
  drule ao_eval_one_phi_output >> strip_tac >>
  `h = i` by
    (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[]) >>
  gvs[]
QED
