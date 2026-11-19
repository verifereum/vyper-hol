(* Concrete forwarding runs up to, but not including, the REVERT fetch's step. *)
Theory gasFocusFmpCutForwardRun
Ancestors
  fmpStageOpFrameForwardAbort fmpStageOpBase fmpStagePointRanges fmpStageRel
  frameViewFacts lowerDloadOracleCallAssembly lowerDloadPtrForward
  ptrDiscipline ptrStaticDiscipline pointerConfinedDefs memLocDefs
  contextCodegenRel venomExecSemantics venomInst venomState
  venomWf arithmetic finite_map pred_set list

Theorem cut_forward_assign_ok[local]:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==> ?y. FLOOKUP t.vs_vars v = SOME y) /\
  inst.inst_opcode = ASSIGN /\ step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\
       s1.vs_labels = t1.vs_labels /\
       (!v x. FLOOKUP s1.vs_vars v = SOME x ==> ?y. FLOOKUP t1.vs_vars v = SOME y) /\
       t1.vs_current_bb = t.vs_current_bb
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >>
  drule_all fmpStageOpFrameForwardAbortTheory.fmp_forward_operand >> strip_tac >>
  simp[step_inst_base_opcode_eqs, update_var_def] >>
  rpt strip_tac >>
  Cases_on `out = v'` >> gvs[update_var_def, FLOOKUP_UPDATE] >>
  first_x_assum drule >> simp[]
QED

Theorem cut_forward_copy_ok[local]:
  s.vs_labels = t.vs_labels /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==> ?y. FLOOKUP t.vs_vars v = SOME y) /\
  s.vs_returndata = t.vs_returndata /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sz] /\
  (!x. eval_operand src s = SOME x ==> eval_operand src t = SOME x) /\
  (!x. eval_operand sz s = SOME x ==> eval_operand sz t = SOME x) /\
  step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\
       s1.vs_labels = t1.vs_labels /\
       (!v x. FLOOKUP s1.vs_vars v = SOME x ==> ?y. FLOOKUP t1.vs_vars v = SOME y) /\
       t1.vs_current_bb = t.vs_current_bb
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >>
  `?d. eval_operand dst t = SOME d` by metis_tac[fmpStageOpFrameForwardAbortTheory.fmp_forward_operand] >>
  `eval_operand src t = SOME offset /\ eval_operand sz t = SOME size_val` by
    metis_tac[] >>
  qpat_x_assum `write_memory_with_expansion _ _ s = s1` (SUBST_ALL_TAC o SYM) >>
  simp[step_inst_base_opcode_eqs, write_memory_with_expansion_def, write_memory_def]
QED

Theorem cut_forward_scalar_prov[local]:
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sz] /\
  MEM op [src;sz] ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v = NONE` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `ptr_use_static_ok _ _ _`
    (qspec_then `v` mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_static_ok_def]) >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def,
      Excl "FILTER"] >>
  simp[FILTER] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem cut_forward_scalar_eq[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sz] /\
  MEM op [src;sz] /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE` by metis_tac[cut_forward_scalar_prov] >>
  `MEM op inst.inst_operands /\ inst.inst_opcode <> PHI` by gvs[] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[] >> metis_tac[ld_active_inst_member]) >>
  drule_all fmp_stage_operand_point >> strip_tac >>
  fs[] >> metis_tac[fmp_mem_value_clean]
QED

Theorem cut_forward_frame_fields[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  s.vs_labels = t.vs_labels /\ s.vs_returndata = t.vs_returndata /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==> ?y. FLOOKUP t.vs_vars v = SOME y)
Proof
  simp[fmp_stage_rel_def, fmp_frame_rel_def, fmp_env_rel_def] >> metis_tac[]
QED

(* The endpoint is fetched but not stepped. In particular, even a COPY that
   would abort has a length-zero successful prefix. *)
Theorem cut_forward_prefix[local]:
  !h.
  h <= j - s.vs_inst_idx /\ revert_forward_pair bb s.vs_inst_idx j /\
  (!k. k <= j - s.vs_inst_idx ==>
       get_instruction bb' (t.vs_inst_idx+k) = get_instruction bb (s.vs_inst_idx+k)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sz] /\
  s.vs_labels = t.vs_labels /\ s.vs_returndata = t.vs_returndata /\
  (!v x. FLOOKUP s.vs_vars v = SOME x ==> ?y. FLOOKUP t.vs_vars v = SOME y) /\
  (!x. eval_operand src s = SOME x ==> eval_operand src t = SOME x) /\
  (!x. eval_operand sz s = SOME x ==> eval_operand sz t = SOME x) /\
  trace (0:num) = s /\
  (!k. k < h ==>
       ?ii r. get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
              step_inst fuel C ii (trace k) = OK r /\
              trace (SUC k) = r with vs_inst_idx := s.vs_inst_idx + SUC k) ==>
  ?U. U 0 = t /\
      (!k. k <= h ==> (U k).vs_inst_idx = t.vs_inst_idx+k /\
                       (U k).vs_current_bb = t.vs_current_bb) /\
      (!k. k < h ==>
           ?ii r. get_instruction bb' (t.vs_inst_idx+k) = SOME ii /\
                  ~is_terminator ii.inst_opcode /\
                  step_inst fuel C' ii (U k) = OK r /\
                  U (SUC k) = r with vs_inst_idx := t.vs_inst_idx + SUC k) /\
      (trace h).vs_labels = (U h).vs_labels /\
      (!v x. FLOOKUP (trace h).vs_vars v = SOME x ==>
             ?y. FLOOKUP (U h).vs_vars v = SOME y)
Proof
  Induct >- (rpt strip_tac >> qexists_tac `\k. t` >> gvs[]) >>
  strip_tac >> qpat_x_assum `(h <= _ /\ _) ==> ?U. _` mp_tac >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
                qpat_assum `!k. k < SUC h ==> _` irule >> decide_tac)) >>
  strip_tac >>
  qpat_assum `!k. k < SUC h ==> _` (qspec_then `h` mp_tac) >> simp[NoAsms] >>
  disch_then (qx_choose_then `ii` (qx_choose_then `r` strip_assume_tac)) >>
  `get_instruction bb' (t.vs_inst_idx+h) = SOME ii` by
    (qpat_assum `!k. k <= j - s.vs_inst_idx ==> _` (qspec_then `h` mp_tac) >> simp[]) >>
  `?u. ~is_terminator ii.inst_opcode /\ step_inst fuel C' ii (U h) = OK u /\
       r.vs_labels = u.vs_labels /\ u.vs_current_bb = (U h).vs_current_bb /\
       (!v x. FLOOKUP r.vs_vars v = SOME x ==> ?y. FLOOKUP u.vs_vars v = SOME y)` by
    (Cases_on `h = 0`
     >- (gvs[step_inst_non_invoke, is_terminator_def] >>
         drule_all cut_forward_copy_ok >> metis_tac[]) >>
     `ii.inst_opcode = ASSIGN` by
       (`s.vs_inst_idx < h + s.vs_inst_idx /\ h + s.vs_inst_idx < j` by decide_tac >>
        qpat_assum `revert_forward_pair _ _ _`
          (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
        first_x_assum irule >> qexists_tac `h + s.vs_inst_idx` >> simp[]) >>
     `step_inst_base ii (trace h) = OK r` by
       (qpat_x_assum `step_inst fuel C ii (trace h) = OK r` mp_tac >>
        simp[step_inst_non_invoke]) >>
     drule_all cut_forward_assign_ok >>
     disch_then (qx_choose_then `u` strip_assume_tac) >>
     qexists_tac `u` >> simp[step_inst_non_invoke, is_terminator_def]) >>
  qexists_tac `\k. if k = SUC h then u with vs_inst_idx := t.vs_inst_idx + SUC h else U k` >>
  simp[] >> conj_tac
  >- (qx_gen_tac `k` >> strip_tac >> Cases_on `k = SUC h` >> simp[] >>
      qpat_assum `!k. k <= h ==> _` (qspec_then `if k = SUC h then h else k` mp_tac) >> simp[]) >>
  qx_gen_tac `k` >> strip_tac >> `k <> SUC h` by decide_tac >> simp[] >>
  Cases_on `k = h` >-
    (qexistsl [`ii`, `u`] >> simp[] >> once_rewrite_tac[ADD_COMM] >> simp[]) >>
  `k < h` by decide_tac >>
  once_rewrite_tac[ADD_COMM] >> asm_rewrite_tac[] >>
  qpat_x_assum `!k. k < h ==> _` (qspec_then `k` mp_tac) >> asm_rewrite_tac[]
QED

(* A prefix supplies the actual reached fetches, without running its endpoint.
   Full-block abort transport also covers aborting at the initial COPY. *)
Theorem focus_fmp_cut_forward_run:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  revert_forward_pair bb s.vs_inst_idx j /\
  (!k. k <= j - s.vs_inst_idx ==>
       get_instruction bb' (t.vs_inst_idx+k) = get_instruction bb (s.vs_inst_idx+k)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sz] ==>
  (!fuel C h trace.
    h <= j - s.vs_inst_idx /\ trace 0 = s /\
    (!k. k < h ==>
         ?ii r. get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
                step_inst fuel C ii (trace k) = OK r /\
                trace (SUC k) = r with vs_inst_idx := s.vs_inst_idx + SUC k) ==>
    ?U. U 0 = t /\
        (!k. k <= h ==> (U k).vs_current_bb = t.vs_current_bb /\
             (U k).vs_inst_idx = t.vs_inst_idx+k /\
             ?ii. get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
                  get_instruction bb' (U k).vs_inst_idx = SOME ii /\
                  (k = 0 ==> ii = inst) /\
                  (0 < k /\ k < j - s.vs_inst_idx ==> ii.inst_opcode = ASSIGN) /\
                  (k = j - s.vs_inst_idx ==> ii.inst_opcode = REVERT)) /\
        (!k. k < h ==>
             ?ii r. get_instruction bb' (U k).vs_inst_idx = SOME ii /\
                    ~is_terminator ii.inst_opcode /\
                    step_inst fuel C' ii (U k) = OK r /\
                    U (SUC k) = r with vs_inst_idx := t.vs_inst_idx + SUC k)) /\
  (!fuel C reason se. exec_block fuel C bb s = Abort reason se ==>
       ?te. exec_block fuel C' bb' t = Abort reason te)
Proof
  strip_tac >> drule_then strip_assume_tac cut_forward_frame_fields >>
  `!x. eval_operand src s = SOME x ==> eval_operand src t = SOME x` by
    (rpt strip_tac >> `MEM src [src;sz]` by simp[] >>
     drule_all cut_forward_scalar_eq >> simp[]) >>
  `!x. eval_operand sz s = SOME x ==> eval_operand sz t = SOME x` by
    (rpt strip_tac >> `MEM sz [src;sz]` by simp[] >>
     drule_all cut_forward_scalar_eq >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!k. k <= j - s.vs_inst_idx ==> get_instruction bb' _ = _`
        (assume_tac o GSYM) >>
      drule_all fmp_forward_available_abort >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all cut_forward_prefix >>
  disch_then (qspec_then `C'` (qx_choose_then `U` strip_assume_tac)) >>
  qexists_tac `U` >> asm_rewrite_tac[] >> reverse conj_tac
  >- (gen_tac >> strip_tac >>
      `(U k).vs_inst_idx = t.vs_inst_idx+k` by
        (qpat_assum `!k. k <= h ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
      asm_rewrite_tac[] >>
      qpat_x_assum `!k. k < h ==> _` (qspec_then `k` mp_tac) >> asm_rewrite_tac[]) >>
  gen_tac >> strip_tac >> simp[] >> once_rewrite_tac[ADD_COMM] >>
  `s.vs_inst_idx < j` by fs[revert_forward_pair_def] >>
  `s.vs_inst_idx <= s.vs_inst_idx+k /\ s.vs_inst_idx+k <= j` by decide_tac >>
  `?ii. get_instruction bb (s.vs_inst_idx+k) = SOME ii` by
    (qpat_assum `revert_forward_pair _ _ _`
       (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
     `j < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
     `s.vs_inst_idx+k < LENGTH bb.bb_instructions` by decide_tac >>
     simp[get_instruction_def]) >>
  `get_instruction bb' (t.vs_inst_idx+k) = SOME ii` by
    (qpat_assum `!k. k <= j - s.vs_inst_idx ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  qexists_tac `ii` >> asm_rewrite_tac[] >>
  conj_tac >- (strip_tac >> fs[]) >>
  drule_all revert_forward_pair_interval_opcode >> strip_tac >>
  simp[] >> decide_tac
QED
