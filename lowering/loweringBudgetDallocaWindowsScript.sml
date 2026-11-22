(* Straight-line instruction windows in the raw allocation recorder. *)
Theory loweringBudgetDallocaWindows
Ancestors
  loweringCallBudgetHistory loweringBudgetStoreRecorder lowerDloadPtrRawReachable
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomInst venomState
  venomExecProofs venomInstProofs1 instIdxIndep o1LowerDloadRunnerBoundary opcodeClass
  loweringCallBudgetBounds loweringBudgetPathDeterminism fragExec exprLoweringProps words list rich_list arithmetic

Theorem lower_budget_window_next:
  lower_budget_path F (D,lo,explicit,ctx) root h marks p /\
  lower_budget_path F (D,lo,explicit,ctx) root (h ++ [e]) marks' q /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\ active_inst p.bp_fn i p.bp_state /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE ==>
  q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
  q.bp_state.vs_current_bb = p.bp_state.vs_current_bb /\
  ?fuel t.
    e = BudgetStep (LENGTH h) p i fuel (OK t) q /\
    step_inst_base i p.bp_state = OK t /\
    q.bp_state = t with vs_inst_idx := SUC p.bp_state.vs_inst_idx
Proof
  strip_tac >>
  `!j. active_inst p.bp_fn j p.bp_state ==> j = i` by
    metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  `!m r. lower_budget_path F (D,lo,explicit,ctx) root h m r ==>
    m = marks /\ r = p` by metis_tac[lower_budget_path_history_unique] >>
  qpat_x_assum `lower_budget_path _ _ _ (_ ++ [_]) _ _` mp_tac >>
  pure_once_rewrite_tac[lower_budget_path_cases] >> strip_tac >>
  full_simp_tac pure_ss [pairTheory.PAIR_EQ, GSYM SNOC_APPEND, SNOC_11, NOT_SNOC_NIL] >>
  qpat_x_assum `!m r. lower_budget_path _ _ _ _ m r ==> _` drule >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[step_inst_non_invoke] >>
  TRY (drule step_inst_base_intret_opcodes >> strip_tac >>
       gvs[is_terminator_def]) >>
  metis_tac[cj 10 step_inst_base_preserves_all]
QED

Theorem lower_budget_path_saved_invokes[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    root.bp_stack = [] ==>
    EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
               f.cf_inst.inst_opcode = INVOKE) q.bp_stack
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
QED

(* An entry skips only the PHI prefix. Any ordinary instruction immediately
   before the current cursor must have been stepped within this block. *)
Theorem lower_budget_window_not_entered[local]:
  enters_block fn s t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  t.vs_inst_idx = SUC k /\ (EL k bb.bb_instructions).inst_opcode <> PHI ==>
  F
Proof
  strip_tac >>
  qpat_x_assum `enters_block _ _ _`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => qpat_x_assum `lookup_block s_phi.vs_current_bb _ = _`
    (mp_tac o ONCE_REWRITE_RULE [th])) >> simp[] >> strip_tac >> gvs[] >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  metis_tac[phi_prefix_length_el_phi]
QED

Theorem lower_budget_window_prev:
  root.bp_stack = [] /\
  lower_budget_path F (D,lo,explicit,ctx) root (h ++ [e]) marks q /\
  ALL_DISTINCT (fn_labels q.bp_fn) /\
  lookup_block q.bp_state.vs_current_bb q.bp_fn.fn_blocks = SOME bb /\
  q.bp_state.vs_inst_idx = SUC k /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode <> PHI /\
  (EL k bb.bb_instructions).inst_opcode <> INVOKE ==>
  ?m p fuel t.
    lower_budget_path F (D,lo,explicit,ctx) root h m p /\
    p.bp_fn = q.bp_fn /\ p.bp_stack = q.bp_stack /\
    p.bp_state.vs_current_bb = q.bp_state.vs_current_bb /\
    p.bp_state.vs_inst_idx = k /\
    e = BudgetStep (LENGTH h) p (EL k bb.bb_instructions) fuel (OK t) q /\
    step_inst_base (EL k bb.bb_instructions) p.bp_state = OK t /\
    q.bp_state = t with vs_inst_idx := SUC k
Proof
  strip_tac >>
  qpat_x_assum `lower_budget_path _ _ _ (_ ++ [_]) _ _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [lower_budget_path_cases])) >>
  strip_tac >>
  full_simp_tac pure_ss [pairTheory.PAIR_EQ, GSYM SNOC_APPEND, SNOC_11, NOT_SNOC_NIL] >>
  gvs[]
  >- (`step_inst_base i p.bp_state = OK t` by gvs[step_inst_non_invoke] >>
      `t.vs_current_bb = p.bp_state.vs_current_bb` by
        metis_tac[cj 10 step_inst_base_preserves_all] >>
      mp_tac (Q.INST [`fn` |-> `p.bp_fn`, `inst` |-> `i`,
        `s` |-> `p.bp_state`] active_inst_block_lookup) >>
      simp[get_instruction_def] >>
      strip_tac >> gvs[] >> metis_tac[])
  >- metis_tac[lower_budget_window_not_entered]
  >- metis_tac[lower_budget_window_not_entered] >>
  drule ld_invoke_bind_control >> strip_tac >>
  `active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE` by
    (drule lower_budget_path_saved_invokes >> simp[]) >>
  `?b. lookup_block f.cf_state.vs_current_bb f.cf_fn.fn_blocks = SOME b /\
       get_instruction b f.cf_state.vs_inst_idx = SOME f.cf_inst` by
    (irule active_inst_block_lookup >> simp[]) >>
  fs[get_instruction_def] >> gvs[]
QED

Theorem lower_budget_window_has_prev:
  root.bp_stack = [] /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  ALL_DISTINCT (fn_labels q.bp_fn) /\
  lookup_block q.bp_state.vs_current_bb q.bp_fn.fn_blocks = SOME bb /\
  q.bp_state.vs_inst_idx = SUC k /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode <> PHI /\
  (EL k bb.bb_instructions).inst_opcode <> INVOKE ==>
  ?h0 m p fuel t.
    lower_budget_path F (D,lo,explicit,ctx) root h0 m p /\
    p.bp_fn = q.bp_fn /\ p.bp_stack = q.bp_stack /\
    p.bp_state.vs_current_bb = q.bp_state.vs_current_bb /\
    p.bp_state.vs_inst_idx = k /\
    h = h0 ++ [BudgetStep (LENGTH h0) p
                 (EL k bb.bb_instructions) fuel (OK t) q] /\
    step_inst_base (EL k bb.bb_instructions) p.bp_state = OK t /\
    q.bp_state = t with vs_inst_idx := SUC k
Proof
  strip_tac >> Cases_on `h` using SNOC_CASES
  >- (qpat_x_assum `lower_budget_path _ _ _ [] _ _` mp_tac >>
      pure_once_rewrite_tac[lower_budget_path_cases] >>
      simp[GSYM SNOC_APPEND] >> strip_tac >> gvs[] >>
      metis_tac[lower_budget_window_not_entered]) >>
  gvs[SNOC_APPEND] >> drule_all lower_budget_window_prev >> metis_tac[]
QED

Theorem lower_budget_path_index_step:
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  n < LENGTH h ==>
  ?m p m' p'.
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h ++ [EL n h]) m' p'
Proof
  strip_tac >>
  drule lower_budget_path_take >>
  disch_then (fn th => mp_tac (Q.SPEC `n` th) >>
                       mp_tac (Q.SPEC `SUC n` th)) >>
  gs[TAKE_SUC_BY_TAKE, SNOC_APPEND] >> metis_tac[]
QED

Theorem lower_budget_path_at_base_step:
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  n < LENGTH h /\
  EL n h = BudgetStep n p i fuel (OK t) p' ==>
  active_inst p.bp_fn i p.bp_state /\
  step_inst fuel ctx i p.bp_state = OK t /\
  ?m m'.
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE (SUC n) h) m' p'
Proof
  strip_tac >> drule_all lower_budget_path_index_step >> strip_tac >>
  rename1 `lower_budget_path F _ _ (_ ++ [_]) mn pn` >>
  `LENGTH (TAKE n h) = n` by simp[LENGTH_TAKE] >>
  qpat_assum `lower_budget_path _ _ _ (_ ++ [_]) mn pn` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [lower_budget_path_cases])) >>
  strip_tac >>
  full_simp_tac pure_ss [pairTheory.PAIR_EQ, GSYM SNOC_APPEND, SNOC_11, NOT_SNOC_NIL] >>
  gvs[] >> rpt (goal_assum (drule_at Any)) >>
  gs[TAKE_SUC_BY_TAKE, SNOC_APPEND] >> metis_tac[]
QED

Theorem calldatasize_step_value[local]:
  step_inst_base (mk_inst id CALLDATASIZE [] [x]) s = OK t ==>
  eval_operand (Var x) (t with vs_inst_idx := n) =
    SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata))
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def,
       bind_outputs_def] >> strip_tac >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lower_budget_dalloca_calldata_size:
  root.bp_stack = [] /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  ALL_DISTINCT (fn_labels q.bp_fn) /\
  lookup_block q.bp_state.vs_current_bb q.bp_fn.fn_blocks = SOME bb /\
  q.bp_state.vs_inst_idx = SUC k /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = mk_inst id CALLDATASIZE [] [x] /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 ==>
  eval_operand (Var x) q.bp_state =
    SOME (n2w (LENGTH q.bp_state.vs_call_ctx.cc_calldata)) /\
  w2n (n2w (LENGTH q.bp_state.vs_call_ctx.cc_calldata) : bytes32) < 2 ** 64
Proof
  strip_tac >>
  drule_all lower_budget_path_charge_facts >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode <> PHI /\
   (EL k bb.bb_instructions).inst_opcode <> INVOKE` by simp[mk_inst_def] >>
  drule_all lower_budget_window_has_prev >> strip_tac >>
  `step_inst_base (mk_inst id CALLDATASIZE [] [x]) p.bp_state = OK t` by
    metis_tac[] >>
  `p.bp_state.vs_call_ctx = root.bp_state.vs_call_ctx` by
    (qpat_assum `lower_budget_path F _ _ h0 m p`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lower_budget_path_charge_facts)) >>
     simp[]) >>
  `t.vs_call_ctx = root.bp_state.vs_call_ctx` by
    (qpat_assum `q.bp_state = _` (fn eq =>
       qpat_assum `q.bp_state.vs_call_ctx = _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [eq]))) >>
  conj_tac
  >- (qpat_x_assum `q.bp_state = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      drule calldatasize_step_value >> simp[]) >>
  `LENGTH root.bp_state.vs_call_ctx.cc_calldata < dimword (:256)` by
    (irule LESS_TRANS >> qexists_tac `2 ** 64` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  fs[w2n_n2w]
QED

Theorem lower_budget_window_index_next:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
  n < LENGTH h /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\ active_inst p.bp_fn i p.bp_state /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE ==>
  ?m' q fuel t.
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE (SUC n) h) m' q /\
    EL n h = BudgetStep n p i fuel (OK t) q /\
    q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_state.vs_current_bb = p.bp_state.vs_current_bb /\
    step_inst_base i p.bp_state = OK t /\
    q.bp_state = t with vs_inst_idx := SUC p.bp_state.vs_inst_idx
Proof
  strip_tac >>
  `?m' q. lower_budget_path F (D,lo,explicit,ctx) root
     (TAKE n h ++ [EL n h]) m' q` by metis_tac[lower_budget_path_index_step] >>
  `LENGTH (TAKE n h) = n` by simp[LENGTH_TAKE] >>
  drule_all lower_budget_window_next >> strip_tac >>
  metis_tac[TAKE_SUC_BY_TAKE, SNOC_APPEND]
QED

Theorem lower_budget_raw_call_alloc_record:
  root.bp_stack = [] /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  n < LENGTH h /\
  EL n h = BudgetStep n p (mk_inst alloc_id DALLOCA [Var x] [y]) fuel (OK t) q /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
  p.bp_state.vs_inst_idx = SUC k /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = mk_inst size_id CALLDATASIZE [] [x] /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 ==>
  ?sz. lower_alloc_record h n p.bp_fn (mk_inst alloc_id DALLOCA [Var x] [y])
          p.bp_state (Var x) sz t /\
       sz = n2w (LENGTH p.bp_state.vs_call_ctx.cc_calldata)
Proof
  strip_tac >> drule_all lower_budget_path_at_base_step >> strip_tac >>
  drule_all lower_budget_dalloca_calldata_size >> strip_tac >>
  qexists_tac `n2w (LENGTH p.bp_state.vs_call_ctx.cc_calldata)` >>
  simp[lower_alloc_record_def, mk_inst_def] >>
  qpat_x_assum `w2n _ < _` mp_tac >>
  simp_tac (srw_ss()) [w2n_n2w] >> decide_tac
QED

Theorem raw_call_alloc_copy_operands:
  x <> y /\ eval_operand (Var x) s = SOME sz /\
  run_inst_seq
    [mk_inst alloc_id DALLOCA [Var x] [y];
     mk_inst copy_id CALLDATACOPY [Var y; Lit 0w; Var x] []] s = OK t ==>
  eval_operand (Var y) (t with vs_inst_idx := n) = SOME s.vs_fmp /\
  eval_operand (Var x) (t with vs_inst_idx := n) = SOME sz
Proof
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >> gvs[write_memory_with_expansion_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem raw_call_effect_operands:
  ((call.inst_opcode = CALL /\
    call.inst_operands = [gas;addr;value;ptr_op;len_op;rbuf;rsz]) \/
   (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
    call.inst_operands = [gas;addr;ptr_op;len_op;rbuf;rsz])) /\
  step_inst_base call s = OK t /\
  eval_operand ptr_op s = SOME offset /\ eval_operand len_op s = SOME sz ==>
  ?args g a v ro rz.
    eval_operands call.inst_operands s = SOME args /\
    ((call.inst_opcode = CALL /\ args = [g;a;v;offset;sz;ro;rz]) \/
     (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
      args = [g;a;offset;sz;ro;rz]))
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base call s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def] >>
  metis_tac[]
QED

Theorem lower_budget_run_window:
  !steps n m p.
    lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
    lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
    n + LENGTH steps <= LENGTH h /\
    ALL_DISTINCT (fn_labels p.bp_fn) /\
    lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
    isPREFIX steps (DROP p.bp_state.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) steps ==>
    ?m' q t.
      lower_budget_path F (D,lo,explicit,ctx) root
        (TAKE (n + LENGTH steps) h) m' q /\
      q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
      q.bp_state.vs_current_bb = p.bp_state.vs_current_bb /\
      run_inst_seq steps p.bp_state = OK t /\
      q.bp_state = t with vs_inst_idx := p.bp_state.vs_inst_idx + LENGTH steps /\
      (!j. j < LENGTH steps ==>
        ?p0 fuel u p1.
          EL (n + j) h = BudgetStep (n + j) p0 (EL j steps) fuel (OK u) p1)
Proof
  Induct >- (simp[run_inst_seq_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `isPREFIX (i :: steps) _` >>
  full_simp_tac pure_ss [LENGTH] >>
  `n < LENGTH h /\ SUC n + LENGTH steps <= LENGTH h` by decide_tac >>
  `p.bp_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL p.bp_state.vs_inst_idx bb.bb_instructions = i /\
   isPREFIX steps (DROP (SUC p.bp_state.vs_inst_idx) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     Cases_on `DROP p.bp_state.vs_inst_idx bb.bb_instructions` >>
     simp[] >> metis_tac[DROP_EQ_CONS]) >>
  `active_inst p.bp_fn i p.bp_state` by
    (irule lookup_instruction_active >> qexists_tac `bb` >>
     simp[get_instruction_def]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) steps` by
    fs[] >>
  drule_all lower_budget_window_index_next >> strip_tac >>
  first_x_assum (qspecl_then [`SUC n`, `m'`, `q`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) steps` by fs[EVERY_MEM] >>
  `?u. run_inst_seq steps t = OK u /\
       t' = u with vs_inst_idx := SUC p.bp_state.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq steps q.bp_state = OK _` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq steps t` >> simp[exec_result_map_def]) >>
  qexistsl_tac [`m''`, `q'`, `u`] >>
  simp[run_inst_seq_def, ADD_CLAUSES] >>
  conj_tac >- fs[ADD_CLAUSES] >>
  gen_tac >> Cases_on `j` >> simp[] >> fs[ADD_CLAUSES] >> metis_tac[ADD_COMM]
QED

Theorem lower_budget_raw_call_effect_record:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
  n + 2 < LENGTH h /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
  ai = mk_inst alloc_id DALLOCA [Var x] [y] /\
  ci = mk_inst copy_id CALLDATACOPY [Var y; Lit 0w; Var x] [] /\
  DROP p.bp_state.vs_inst_idx bb.bb_instructions = ai :: ci :: call :: rest /\
  x <> y /\ eval_operand (Var x) p.bp_state = SOME sz /\
  ((call.inst_opcode = CALL /\
    call.inst_operands = [gas;addr;value;Var y;Var x;rbuf;rsz]) \/
   (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
    call.inst_operands = [gas;addr;Var y;Var x;rbuf;rsz])) ==>
  (?cpre cf cu cpost. EL (n + 1) h =
    BudgetStep (n + 1) cpre ci cf (OK cu) cpost) /\
  ?ep ef et eq ws.
    EL (n + 2) h = BudgetStep (n + 2) ep call ef (OK et) eq /\
    ep.bp_fn = p.bp_fn /\ ep.bp_stack = p.bp_stack /\
    eval_operands call.inst_operands ep.bp_state = SOME ws /\
    ?g a v ro rz.
      (call.inst_opcode = CALL /\ ws = [g;a;v;p.bp_state.vs_fmp;sz;ro;rz]) \/
      (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
       ws = [g;a;p.bp_state.vs_fmp;sz;ro;rz])
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  mp_tac (Q.SPECL [`[ai;ci]`, `n`, `m`, `p`] lower_budget_run_window) >>
  impl_tac >- (simp[mk_inst_def, is_terminator_def] >> decide_tac) >>
  simp[] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `!j. _` (qspec_then `1` mp_tac) >> simp[ADD_COMM]) >>
  `eval_operand (Var y) q.bp_state = SOME p.bp_state.vs_fmp /\
   eval_operand (Var x) q.bp_state = SOME sz` by
    (qpat_assum `q.bp_state = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     drule_all raw_call_alloc_copy_operands >> simp[]) >>
  `DROP q.bp_state.vs_inst_idx bb.bb_instructions = call :: rest` by
    (fs[DECIDE ``n + 2 = SUC (SUC n)``] >>
     metis_tac[DROP_EQ_CONS]) >>
  `active_inst q.bp_fn call q.bp_state` by
    (irule lookup_instruction_active >> qexists_tac `bb` >>
     `q.bp_state.vs_inst_idx < LENGTH bb.bb_instructions /\
      EL q.bp_state.vs_inst_idx bb.bb_instructions = call` by
        metis_tac[DROP_EQ_CONS] >>
     simp[get_instruction_def]) >>
  `~is_terminator call.inst_opcode /\ call.inst_opcode <> INVOKE` by
    fs[MEM, is_terminator_def] >>
  `ALL_DISTINCT (fn_labels q.bp_fn)` by simp[] >>
  drule_all (Q.INST [`n` |-> `n + 2`, `i` |-> `call`,
                      `p` |-> `q`] lower_budget_window_index_next) >>
  strip_tac >>
  drule_all raw_call_effect_operands >> strip_tac >>
  qexistsl_tac [`q`, `fuel`, `t'`, `q'`, `args`] >>
  fs[MEM]
QED

(* A prefix that stops before the effect can have only the successful
   steps of this window after the reservation. *)
Theorem lower_budget_pending_before_effect:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
  n < LENGTH h /\ LENGTH h <= n + LENGTH steps /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
  DROP p.bp_state.vs_inst_idx bb.bb_instructions = steps ++ effect :: rest /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) steps ==>
  (!j. n < j /\ j < LENGTH h ==>
    ?p0 fuel t p1. EL j h = BudgetStep j p0 (EL (j - n) steps) fuel (OK t) p1) /\
  (!i. active_inst last.bp_fn i last.bp_state ==>
    i = EL (LENGTH h - n) (steps ++ [effect]))
Proof
  strip_tac >> qabbrev_tac `k = LENGTH h - n` >>
  `k <= LENGTH steps /\ n + k = LENGTH h` by (fs[Abbr `k`] >> decide_tac) >>
  `LENGTH (TAKE k steps) = k` by simp[LENGTH_TAKE] >>
  mp_tac (Q.SPECL [`TAKE k steps`, `n`, `m`, `p`] lower_budget_run_window) >>
  impl_tac
  >- (simp[EVERY_TAKE, IS_PREFIX_EQ_TAKE', TAKE_APPEND1] >>
      qexists_tac `k` >> simp[TAKE_APPEND1]) >>
  simp[TAKE_LENGTH_ID] >> strip_tac >>
  `q = last` by metis_tac[lower_budget_path_history_unique] >>
  conj_tac
  >- (rpt strip_tac >>
      `j - n < k /\ n + (j - n) = j` by decide_tac >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `j - n` mp_tac) >>
      simp[EL_TAKE]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels last.bp_fn)` by metis_tac[] >>
  `lookup_block last.bp_state.vs_current_bb last.bp_fn.fn_blocks = SOME bb` by
    metis_tac[] >>
  drule_all active_inst_block_lookup >> strip_tac >>
  `last.bp_state.vs_inst_idx = k + p.bp_state.vs_inst_idx` by fs[ADD_COMM] >>
  `k + p.bp_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL (k + p.bp_state.vs_inst_idx) bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[]) >>
  `EL k (steps ++ effect :: rest) = EL k (steps ++ [effect])` by
    (simp[EL_APPEND_EQN] >> IF_CASES_TAC >> simp[] >>
     `k - LENGTH steps = 0` by decide_tac >> simp[]) >>
  metis_tac[EL_DROP]
QED

val lower_history_geometry_quote = “\h a b.
  ?fn ai pre op sz post ap af aq ep ei ef et eq ws.
    lower_alloc_record h a fn ai pre op sz post /\
    EL a h = BudgetStep a ap ai af (OK post) aq /\
    EL b h = BudgetStep b ep ei ef (OK et) eq /\
    ep.bp_fn = fn /\ ep.bp_stack = ap.bp_stack /\
    eval_operands ei.inst_operands ep.bp_state = SOME ws /\
    ((sz = n2w (LENGTH pre.vs_call_ctx.cc_calldata) /\
      ?g addr v ro rz.
        (ei.inst_opcode = CALL /\
          ws = [g; addr; v; pre.vs_fmp; sz; ro; rz]) \/
        (MEM ei.inst_opcode [STATICCALL; DELEGATECALL] /\
          ws = [g; addr; pre.vs_fmp; sz; ro; rz])) \/
     (?v offset len salt.
       ((ei.inst_opcode = CREATE /\ ws = [v; offset; len]) \/
        (ei.inst_opcode = CREATE2 /\ ws = [v; offset; len; salt])) /\
       ((offset = pre.vs_fmp /\ sz = len) \/
        (offset = pre.vs_fmp + 21w /\ sz = len + 21w))))”;

val lower_history_window_quote = “\h q a.
  ?b. a < b /\ b <= LENGTH h /\
        (b < LENGTH h ==> lower_event_consumes (EL b h) /\
                          ^lower_history_geometry_quote h a b) /\
        (b = LENGTH h ==> !i.
          active_inst q.bp_fn i q.bp_state ==> i.inst_opcode <> DALLOCA) /\
        (?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post) /\
        !j. a < j /\ j < b ==>
          ?jp ji jf jt jq.
            EL j h = BudgetStep j jp ji jf (OK jt) jq /\
            ~lower_event_consumes (EL j h) /\
            ~lower_event_allocates (EL j h) /\ ~is_terminator ji.inst_opcode”;

Definition lower_history_window_def:
  lower_history_window h q a <=> ^lower_history_window_quote h q a
End

Theorem lower_history_pairs_before_allocation:
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ^lower_history_window_quote h q a) ==>
  ?pair. lower_history_pairs h pair /\
    (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
      !a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        pair a < LENGTH h) /\
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
      ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==> ?b. _` mp_tac >>
  CONV_TAC (LAND_CONV (SIMP_CONV pure_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])) >>
  disch_then (qx_choose_then `pair` assume_tac) >>
  `!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
     a < pair a /\ pair a <= LENGTH h /\
     !j. a < j /\ j < pair a ==> ~lower_event_allocates (EL j h)` by
    metis_tac[] >>
  `!a b. a < LENGTH h /\ b < LENGTH h /\
     lower_event_allocates (EL a h) /\ lower_event_allocates (EL b h) /\
     pair a = pair b ==> a = b` by
    (rpt strip_tac >>
     `a = b \/ a < b \/ b < a` by decide_tac >>
     metis_tac[]) >>
  qexists_tac `pair` >>
  REWRITE_TAC [lower_history_pairs_def] >>
  rpt conj_tac >> rpt strip_tac
  >- metis_tac[LESS_OR_EQ]
  >- metis_tac[]
  >- metis_tac[]
  >- (qpat_x_assum `!a. _ ==> a < pair a /\ _ /\ _ /\ _ /\ _ /\ _`
       (qspec_then `a` mp_tac) >> simp[] >>
      disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
      qpat_x_assum `?ai pre op sz post ap af aq ep ei ef et eq ws. _`
        (qx_choosel_then [`ai`,`pre`,`op`,`sz`,`post`,`ap`,`af`,`aq`,
                          `ep`,`ei`,`ef`,`et`,`eq`,`ws`]
          (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
      qexistsl_tac [`ai`,`pre`,`op`,`sz`,`post`,`ap`,`af`,`aq`,
                    `ep`,`ei`,`ef`,`et`,`eq`,`ws`] >>
      simp[] >>
      qpat_x_assum `?f f' f'' f''' f''''. !j. _` strip_assume_tac >>
      rpt strip_tac >> first_x_assum drule_all >> strip_tac >> metis_tac[])
  >- metis_tac[LESS_OR_EQ] >>
  metis_tac[]
QED

Theorem lower_history_pairs_from_windows:
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ^lower_history_window_quote h q a) /\
  (!i op sz. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA /\
     i.inst_operands = [op] /\ eval_operand op q.bp_state = SOME sz ==>
     w2n sz <= 2 ** 255 + 2 ** 64) ==>
  ?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
      ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)
Proof
  BETA_TAC >> strip_tac >>
  drule (BETA_RULE lower_history_pairs_before_allocation) >>
  strip_tac >> qexists_tac `pair` >>
  simp[lower_history_current_def] >> metis_tac[]
QED

Theorem lower_history_pairs_from_recorded_windows:
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    lower_history_window h q a) /\
  (!i op sz. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA /\
     i.inst_operands = [op] /\ eval_operand op q.bp_state = SOME sz ==>
     w2n sz <= 2 ** 255 + 2 ** 64) ==>
  ?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
      ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)
Proof
  pure_rewrite_tac[lower_history_window_def] >>
  ACCEPT_TAC lower_history_pairs_from_windows
QED

val raw_call_window_quote = “\fn i s.
  ?bb k size_id alloc_id copy_id x y call gas addr value rbuf rsz rest.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx = SUC k /\
    DROP k bb.bb_instructions =
      mk_inst size_id CALLDATASIZE [] [x] ::
      i :: mk_inst copy_id CALLDATACOPY [Var y; Lit 0w; Var x] [] :: call :: rest /\
    i = mk_inst alloc_id DALLOCA [Var x] [y] /\
    x <> y /\
    ((call.inst_opcode = CALL /\
      call.inst_operands = [gas;addr;value;Var y;Var x;rbuf;rsz]) \/
     (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
      call.inst_operands = [gas;addr;Var y;Var x;rbuf;rsz]))”;

Definition raw_call_dalloca_window_def:
  raw_call_dalloca_window fn i s <=> ^raw_call_window_quote fn i s
End

Theorem lower_budget_raw_call_event_window:
  root.bp_stack = [] /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  n < LENGTH h /\
  EL n h = BudgetStep n p ai af (OK post) aq /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  ^raw_call_window_quote p.bp_fn ai p.bp_state ==>
  ^lower_history_window_quote h last n
Proof
  BETA_TAC >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `?bb k. _`
    (qx_choosel_then [`bb`, `k`, `size_id`, `alloc_id`, `copy_id`, `x`, `y`,
                      `call`, `gas`, `addr`, `value`, `rbuf`, `rsz`, `rest`]
      (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  qabbrev_tac `ci = mk_inst copy_id CALLDATACOPY [Var y; Lit 0w; Var x] []` >>
  `k < LENGTH bb.bb_instructions /\
   EL k bb.bb_instructions = mk_inst size_id CALLDATASIZE [] [x] /\
   DROP p.bp_state.vs_inst_idx bb.bb_instructions = ai :: ci :: call :: rest` by
    metis_tac[DROP_EQ_CONS] >>
  `?sz. lower_alloc_record h n p.bp_fn ai p.bp_state (Var x) sz post /\
        sz = n2w (LENGTH p.bp_state.vs_call_ctx.cc_calldata)` by
    (qpat_x_assum `ai = _` SUBST_ALL_TAC >>
     metis_tac[lower_budget_raw_call_alloc_record]) >>
  `eval_operand (Var x) p.bp_state = SOME sz` by fs[lower_alloc_record_def] >>
  drule_all lower_budget_path_at_base_step >> strip_tac >>
  `~is_terminator ai.inst_opcode /\ ai.inst_opcode <> INVOKE /\
   ~is_terminator ci.inst_opcode /\ ci.inst_opcode <> INVOKE` by
    simp[mk_inst_def, Abbr `ci`, is_terminator_def] >>
  Cases_on `n + 2 < LENGTH h`
  >- (mp_tac lower_budget_raw_call_effect_record >>
      impl_tac >- simp[Abbr `ci`] >>
      disch_then (CONJUNCTS_THEN2 strip_assume_tac
        (qx_choosel_then [`ep`,`ef`,`et`,`eq`,`ws`]
          (MAP_EVERY ASSUME_TAC o CONJUNCTS))) >>
      qexists_tac `n + 2` >>
      rpt conj_tac
      >- decide_tac
      >- decide_tac
      >- (strip_tac >> conj_tac
          >- fs[lower_event_consumes_def, MEM] >>
          qexistsl_tac [`p.bp_fn`, `ai`, `p.bp_state`, `Var x`, `sz`, `post`,
                        `p`, `af`, `aq`, `ep`, `call`, `ef`, `et`, `eq`, `ws`] >>
          asm_rewrite_tac[])
      >- (`n + 2 <> LENGTH h` by decide_tac >> simp[])
      >- (qexistsl_tac [`p.bp_fn`, `ai`, `p.bp_state`, `Var x`, `sz`, `post`] >>
          first_assum ACCEPT_TAC) >>
      rpt strip_tac >> `j = n + 1` by decide_tac >>
      qexistsl_tac [`cpre`, `ci`, `cf`, `cu`, `cpost`] >>
      fs[lower_event_allocates_def, lower_event_consumes_def, Abbr `ci`,
         mk_inst_def, is_terminator_def]) >>
  qexists_tac `LENGTH h` >> simp[] >>
  `LENGTH h <= n + 2` by decide_tac >>
  mp_tac (Q.INST [`steps` |-> `[ai;ci]`, `effect` |-> `call`]
    lower_budget_pending_before_effect) >>
  impl_tac >- simp[] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      `LENGTH h - n = 1 \/ LENGTH h - n = 2` by decide_tac >>
      fs[MEM, Abbr `ci`, mk_inst_def]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `j = n + 1 /\ j - n = 1` by decide_tac >>
  qpat_x_assum `!j. n < j /\ j < LENGTH h ==> _` drule_all >>
  strip_tac >>
  fs[lower_event_allocates_def, lower_event_consumes_def, Abbr `ci`,
     mk_inst_def, is_terminator_def] >>
  metis_tac[]
QED

Theorem lower_budget_raw_call_recorded_window:
  root.bp_stack = [] /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  n < LENGTH h /\
  EL n h = BudgetStep n p ai af (OK post) aq /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  raw_call_dalloca_window p.bp_fn ai p.bp_state ==>
  lower_history_window h last n
Proof
  pure_rewrite_tac[raw_call_dalloca_window_def, lower_history_window_def] >>
  ACCEPT_TAC lower_budget_raw_call_event_window
QED

Theorem lower_budget_alloc_event:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  n < LENGTH h /\ lower_event_allocates (EL n h) ==>
  ?p i fuel t q. EL n h = BudgetStep n p i fuel (OK t) q /\
                 i.inst_opcode = DALLOCA
Proof
  strip_tac >> drule_all lower_budget_path_ordinals >> strip_tac >>
  Cases_on `EL n h` >> gvs[lower_event_allocates_def, lower_event_ordinal_def] >>
  metis_tac[]
QED

(* Recover the start of an emitted prologue, including prefixes that reach
   its DALLOCA without reaching its consuming effect. *)
Theorem lower_budget_before_window:
  !len k root h marks q start bb.
    root.bp_stack = [] /\
    enters_block root.bp_fn start root.bp_state /\
    lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
    ALL_DISTINCT (fn_labels q.bp_fn) /\
    lookup_block q.bp_state.vs_current_bb q.bp_fn.fn_blocks = SOME bb /\
    q.bp_state.vs_inst_idx = k + len /\ k + len < LENGTH bb.bb_instructions /\
    (!j. k <= j /\ j < k + len ==>
      (EL j bb.bb_instructions).inst_opcode <> PHI /\
      (EL j bb.bb_instructions).inst_opcode <> INVOKE) ==>
    ?h0 m p.
      isPREFIX h0 h /\ LENGTH h0 + len = LENGTH h /\
      lower_budget_path F (D,lo,explicit,ctx) root h0 m p /\
      p.bp_fn = q.bp_fn /\ p.bp_stack = q.bp_stack /\
      p.bp_state.vs_current_bb = q.bp_state.vs_current_bb /\
      p.bp_state.vs_inst_idx = k
Proof
  Induct >- (simp[] >> metis_tac[IS_PREFIX_REFL]) >>
  rpt gen_tac >> strip_tac >>
  `q.bp_state.vs_inst_idx = SUC (k + len) /\
   k + len < LENGTH bb.bb_instructions` by decide_tac >>
  `(EL (k + len) bb.bb_instructions).inst_opcode <> PHI /\
   (EL (k + len) bb.bb_instructions).inst_opcode <> INVOKE` by
    (first_x_assum (qspec_then `k + len` mp_tac) >> simp[ADD_CLAUSES]) >>
  drule_all (Q.INST [`k` |-> `k + len`] lower_budget_window_has_prev) >> strip_tac >>
  `lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb` by metis_tac[] >>
  first_x_assum (qspecl_then [`k`, `root`, `h0`, `m`, `p`, `start`, `bb`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  strip_tac >>
  qexistsl_tac [`h0'`, `m'`, `p'`] >>
  fs[IS_PREFIX_APPEND, APPEND_ASSOC, ADD_CLAUSES]
QED

(* Calls, returns and loop back edges cannot interrupt a live allocation
   window. The bound carries the reservation across the straight-line
   steps, then charges its effect before any transfer of control. *)
Theorem lower_history_window_before_control_transfer:
  ^lower_history_window_quote h q a /\ a < j /\ j < LENGTH h /\
  (case EL j h of
     BudgetStep _ _ i _ _ _ => is_terminator i.inst_opcode
   | _ => T) ==>
  ?b. a < b /\ b < j /\ lower_event_consumes (EL b h)
Proof
  BETA_TAC >> strip_tac >>
  `~(j < b)` by
    (strip_tac >> qpat_x_assum `!j. a < j /\ j < b ==> _` drule_all >>
     strip_tac >> gvs[]) >>
  `j <> b` by
    (strip_tac >> gvs[] >>
     Cases_on `EL b h` >> gvs[lower_event_consumes_def, is_terminator_def]) >>
  `b < j /\ b < LENGTH h` by decide_tac >>
  qexists_tac `b` >> simp[]
QED

Theorem lower_history_window_before_next_allocation:
  ^lower_history_window_quote h q a /\ a < j /\ j < LENGTH h /\
  lower_event_allocates (EL j h) ==>
  ?b. a < b /\ b < j /\ lower_event_consumes (EL b h)
Proof
  BETA_TAC >> strip_tac >>
  `~(j < b)` by
    (strip_tac >> qpat_x_assum `!j. a < j /\ j < b ==> _` drule_all >>
     metis_tac[]) >>
  `j <> b` by
    (strip_tac >> gvs[] >>
     Cases_on `EL b h` >> gvs[lower_event_allocates_def, lower_event_consumes_def]) >>
  `b < j /\ b < LENGTH h` by decide_tac >>
  qexists_tac `b` >> simp[]
QED
