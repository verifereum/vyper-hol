Theory lowerDloadSafetyDelegate
Ancestors
  lowerDloadExternalBoundary lowerDloadOracleCallAssembly lowerDloadSafetyKernel
  lowerDloadSafetyValues lowerDloadSafetyUpdates lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyRelation lowerDloadSafetyAmbient lowerDloadSafetyAllocBounds
  ptrDiscipline venomExecSemantics venomCallOracleDefs extCallOracle venomState pointerConfinedDefs
  codegenRel contextCodegenRel memLocDefs venomInst finite_map pred_set list words arithmetic

Theorem ld_delegate_dispatch:
  inst.inst_opcode = DELEGATECALL /\
  step_inst_base inst t = OK ts ==>
  ?g a ao az ro rz gas addr y n q rn.
    inst.inst_operands = [g;a;ao;az;ro;rz] /\
    eval_operand g t = SOME gas /\ eval_operand a t = SOME addr /\
    eval_operand ao t = SOME y /\ eval_operand az t = SOME n /\
    eval_operand ro t = SOME q /\ eval_operand rz t = SOME rn /\
    exec_delegatecall inst t gas addr y n q rn = OK ts
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_delegate_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = DELEGATECALL /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?g a ao az ro rz gas addr x y n r q rn.
    inst.inst_operands = [g;a;ao;az;ro;rz] /\
    eval_operand g f.lf_src = SOME gas /\ eval_operand a f.lf_src = SOME addr /\
    eval_operand ao f.lf_src = SOME x /\ eval_operand az f.lf_src = SOME n /\
    eval_operand ro f.lf_src = SOME r /\ eval_operand rz f.lf_src = SOME rn /\
    eval_operand ao f.lf_tgt = SOME y /\ eval_operand ro f.lf_tgt = SOME q /\
    (op_prov f.lf_H ao = NONE ==> x = y) /\
    (!k. op_prov f.lf_H ao = SOME k ==> ld_wordrel A (SOME k) x y) /\
    (op_prov f.lf_H ro = NONE ==> r = q) /\
    (!k. op_prov f.lf_H ro = SOME k ==> ld_wordrel A (SOME k) r q) /\
    exec_delegatecall inst f.lf_tgt gas addr y n q rn = OK ts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_delegate_dispatch >> strip_tac >>
  `!i. MEM i [0;1;3;5] ==>
    eval_operand (EL i inst.inst_operands) f.lf_src =
    eval_operand (EL i inst.inst_operands) f.lf_tgt` by
    (rpt strip_tac >> irule ld_oracle_call_scalar_equal >> simp[] >>
     (conj_tac >- metis_tac[]) >> qexists `tn` >> simp[]) >>
  `!op z. MEM op inst.inst_operands /\ eval_operand op f.lf_tgt = SOME z ==>
    ?w. eval_operand op f.lf_src = SOME w /\
      (op_prov f.lf_H op = NONE ==> w = z) /\
      (!k. op_prov f.lf_H op = SOME k ==> ld_wordrel A (SOME k) w z)` by
    (rpt strip_tac >>
     `op_taint tn op = {}` by
       (irule ld_numeric_operand_untainted >>
        qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[]) >>
     irule ld_numeric_operand_observation >> simp[] >>
     (conj_tac >- (qexists `tn` >> simp[])) >>
     (conj_tac >- (qexists `inst` >> simp[])) >>
     qexists `P` >> simp[]) >>
  `?x. eval_operand ao f.lf_src = SOME x /\
      (op_prov f.lf_H ao = NONE ==> x = y) /\
      (!k. op_prov f.lf_H ao = SOME k ==> ld_wordrel A (SOME k) x y)` by
    (first_x_assum irule >> simp[]) >>
  `?r. eval_operand ro f.lf_src = SOME r /\
      (op_prov f.lf_H ro = NONE ==> r = q) /\
      (!k. op_prov f.lf_H ro = SOME k ==> ld_wordrel A (SOME k) r q)` by
    (first_x_assum irule >> simp[]) >>
  qexistsl [`g`,`a`,`ao`,`az`,`ro`,`rz`,`gas`,`addr`,`x`,`y`,`n`,`r`,`q`,`rn`] >>
  simp[] >>
  qpat_x_assum `!i. MEM i _ ==> _` mp_tac >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, EL]
QED

(* With equal accounts and transient storage, both runs adopt the same
   outcome; only the relocated return-buffer write differs. *)
Theorem ld_consume_delegate_effect[local]:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  consume_call_outcome rq rt n t = (w,ts) /\
  xs = TAKE n ts.vs_returndata /\
  tn'.t_mem = tn.t_mem DIFF {ro+j | j < LENGTH xs} /\
  tn'.t_imm = tn.t_imm /\ tn'.t_stor = {} /\ tn'.t_trans = {} /\
  (xs = [] \/ (ro = rt /\ ro + LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta + LENGTH xs <= sz)) ==>
  ?ss. consume_call_outcome rq ro n s = (w,ss) /\
    ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
    ss.vs_returndata = ts.vs_returndata /\
    ss.vs_params = s.vs_params /\ ts.vs_params = t.vs_params /\
    ss.vs_fmp = s.vs_fmp /\ ts.vs_fmp = t.vs_fmp /\
    ss.vs_vars = s.vs_vars /\ ts.vs_vars = t.vs_vars /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_accounts = t.vs_accounts` by
    metis_tac[ld_nonghost_accounts_empty] >>
  `s.vs_transient = t.vs_transient` by
    metis_tac[ld_nonghost_transient_empty] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_nonghost_def] >>
  `ld_memory lo A tn'
     (write_memory_with_expansion ro xs s)
     (write_memory_with_expansion rt xs t)` by
    (irule ld_memory_write_classified >> metis_tac[]) >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
  simp[consume_call_outcome_eq, adopt_outcome_def] >> strip_tac >> gvs[] >>
  gvs[ld_memory_def, ld_nonghost_def, storage_agree_except_def,
      word_agree_except_def] >> metis_tac[]
QED

(* Both runs consume the shared oracle with the source's delegate request. *)
Theorem ld_delegate_execution:
  ld_nonghost tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n (ao:bytes32)) (w2n (az:bytes32)) s =
    read_memory (w2n (at:bytes32)) (w2n az) t /\
  exec_delegatecall inst t (gas:bytes32) (addr:bytes32) at az (rt:bytes32) (rz:bytes32) = OK ts ==>
  ?rq out w u.
    rq = venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall /\
    consume_call_outcome rq (w2n rt) (w2n rz) t = (w,u) /\
    inst.inst_outputs = [out] /\ ts = update_var out w u
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts` by
    metis_tac[ld_nonghost_accounts_empty] >>
  `s.vs_transient = t.vs_transient` by
    metis_tac[ld_nonghost_transient_empty] >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[ld_nonghost_def] >>
  `venom_call_request s addr 0w ao az F = venom_call_request t addr 0w at az F` by
    simp[venom_call_request_def] >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_delegatecall_def, Excl "consume_call_outcome_eq"] >>
  qmatch_goalsub_abbrev_tac `consume_call_outcome rq _ _ t` >>
  Cases_on `consume_call_outcome rq (w2n rt) (w2n rz) t` >>
  simp[AllCaseEqs(), Excl "consume_call_outcome_eq"] >> strip_tac >>
  gvs[Abbr `rq`, Excl "consume_call_outcome_eq"]
QED

val _ = if null (hyp ld_delegate_execution) then ()
        else raise Fail "delegate execution boundary has hypotheses";

Theorem ld_delegate_observed_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\ MEM inst (fn_insts f.lf_fn) /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  tn.t_stor = {} /\ tn.t_trans = {} /\ inst.inst_opcode = DELEGATECALL /\
  3 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst f.lf_src = [(w2n (ro:bytes32),w2n (rz:bytes32))] /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  read_memory (w2n (ao:bytes32)) (w2n (az:bytes32)) f.lf_src =
    read_memory (w2n (at:bytes32)) (w2n az) f.lf_tgt /\
  exec_delegatecall inst f.lf_tgt (gas:bytes32) (addr:bytes32) at az (rt:bytes32) rz = OK ts /\
  (w2n rz = 0 \/ (w2n ro = w2n rt /\ w2n ro + w2n rz <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n ro = b+delta /\ w2n rt = c+delta /\ delta + w2n rz <= sz)) ==>
  ?ss. exec_delegatecall inst f.lf_src gas addr ao az ro rz = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_at Any ld_delegate_execution >>
  disch_then (qspecl_then [`tn`,`f.lf_src`,`ao`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `xs = TAKE (w2n rz) u.vs_returndata` >>
  qabbrev_tac `tn' = tn with t_mem := tn.t_mem DIFF {w2n ro+j | j < LENGTH xs}` >>
  `LENGTH xs <= w2n rz` by simp[Abbr `xs`, LENGTH_TAKE_EQ, MIN_DEF] >>
  `xs = [] \/ (w2n ro = w2n rt /\ w2n ro + LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n ro = b+delta /\ w2n rt = c+delta /\ delta + LENGTH xs <= sz)` by
    (qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` kall_tac >>
     qpat_x_assum `w2n rz = 0 \/ _` strip_assume_tac
     >- (disj1_tac >> fs[Abbr `xs`])
     >- (disj2_tac >> disj1_tac >> (conj_tac >- asm_rewrite_tac[]) >> decide_tac) >>
     disj2_tac >> disj2_tac >>
     qexistsl [`k`,`b`,`c`,`sz`,`delta`] >> simp[] >> decide_tac) >>
  `?rs. consume_call_outcome rq (w2n ro) (w2n rz) f.lf_src = (w,rs) /\
    ld_memory lo A tn' rs u /\ ld_nonghost tn' rs u /\
    rs.vs_returndata = u.vs_returndata /\
    rs.vs_params = f.lf_src.vs_params /\ u.vs_params = f.lf_tgt.vs_params /\
    rs.vs_fmp = f.lf_src.vs_fmp /\ u.vs_fmp = f.lf_tgt.vs_fmp /\
    rs.vs_vars = f.lf_src.vs_vars /\ u.vs_vars = f.lf_tgt.vs_vars /\
    rs.vs_allocas = f.lf_src.vs_allocas /\ u.vs_allocas = f.lf_tgt.vs_allocas /\
    rs.vs_alloca_next = f.lf_src.vs_alloca_next /\ u.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    rs.vs_current_bb = f.lf_src.vs_current_bb /\ u.vs_current_bb = f.lf_tgt.vs_current_bb /\
    rs.vs_prev_bb = f.lf_src.vs_prev_bb /\ u.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    rs.vs_inst_idx = f.lf_src.vs_inst_idx /\ u.vs_inst_idx = f.lf_tgt.vs_inst_idx` by
    (irule ld_consume_delegate_effect >>
     qpat_x_assum `rq = _` kall_tac >>
     qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` kall_tac >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >- simp[Abbr `tn'`]) >>
     (conj_tac >- simp[Abbr `tn'`]) >>
     qexistsl [`w2n rt`,`tn`,`xs`] >>
     simp[Abbr `tn'`] >>
     asm_rewrite_tac[] >> fs[Abbr `xs`, w2n_11] >> metis_tac[]) >>
  `step_taint inst f.lf_src (update_var out w rs) tn =
    tn' with t_var := set_var_taint f.lf_tv inst.inst_outputs {}` by
    (drule_at (Pat `source_memory_write_ranges _ _ = _`) ld_oracle_call_taint >>
     disch_then (qspecl_then [`tn`,`update_var out w rs`] mp_tac) >>
     simp[update_var_def] >>
     disch_then SUBST1_TAC >>
     simp[Abbr `tn'`, Abbr `xs`, adopt_reset_def, ADD_COMM,
          taint_component_equality]) >>
  qexists `update_var out w rs` >>
  (conj_tac >-
    (simp[NoAsms, exec_delegatecall_def, Excl "consume_call_outcome_eq"] >>
     qpat_x_assum `rq = _` (SUBST1_TAC o SYM) >>
     asm_rewrite_tac[] >> simp[Excl "consume_call_outcome_eq"])) >>
  (conj_tac >- (simp[update_var_def] >> irule ld_oracle_call_vars >> simp[] >>
     (conj_tac >- (qexists `w` >> simp[])) >>
     irule ld_inst_output_ir >> qexists `inst` >> simp[])) >>
  qpat_x_assum `rq = _` kall_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` kall_tac >>
  simp[update_var_def] >>
  conj_tac
  >- (qpat_x_assum `ld_memory lo A tn' rs u` mp_tac >>
      simp[ld_memory_def, update_var_def] >> metis_tac[]) >>
  qpat_x_assum `ld_nonghost tn' rs u` mp_tac >>
  simp[ld_nonghost_def, update_var_def] >> rpt strip_tac >>
  qpat_x_assum `rs.vs_call_ctx = _` (fn th => rewrite_tac[GSYM th]) >>
  first_assum (qspec_then `a` mp_tac) >> simp[] >>
  qpat_x_assum `ld_memory lo A tn' rs u` mp_tac >>
  simp[ld_memory_def] >> metis_tac[]
QED

Theorem ld_delegate_step:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) /\
  inst.inst_opcode = DELEGATECALL /\ step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_delegate_operands >> strip_tac >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by
    (fs[taint_ok_def] >> metis_tac[]) >>
  `read_memory (w2n x) (w2n n) f.lf_src = read_memory (w2n y) (w2n n) f.lf_tgt /\
   (w2n rn = 0 \/ (w2n r = w2n q /\ w2n r + w2n rn <= lo) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n r = b+delta /\ w2n q = c+delta /\ delta + w2n rn <= sz))` by
    (irule ld_oracle_call_ranges >>
     qpat_assum `access_ok _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `3 < LENGTH inst.inst_operands /\
   source_memory_write_ranges inst f.lf_src = [(w2n r,w2n rn)]` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def,
         memory_range_of_operands_def] >>
  (Q.SUBGOAL_THEN
    `w2n rn = 0 \/ (w2n r = w2n q /\ w2n r + w2n rn <= lo) \/
     (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n r = b+delta /\ w2n q = c+delta /\ delta + w2n rn <= sz)`
    assume_tac >- metis_tac[]) >>
  drule_all ld_delegate_observed_effect >> strip_tac >>
  qexists `ss` >> simp[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> simp[eval_operands_def]
QED

Theorem ld_sync_delegate_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\ inst.inst_opcode = DELEGATECALL /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_access_ok, ld_sync_taint_ok] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v` by
    metis_tac[ld_alloc_bounds] >>
  `!a k u v z b c sz. FLOOKUP A a = SOME (u,v,z) /\
    FLOOKUP A k = SOME (b,c,sz) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)` by
    metis_tac[ld_alloc_separate] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_sync_active >> simp[] >> strip_tac >>
     metis_tac[ld_alloc_target_no_wrap, HD]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  gvs[step_inst_non_invoke] >>
  `tn.t_var = f.lf_tv` by simp[] >>
  drule_all ld_delegate_step >> strip_tac >>
  qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >>
  (conj_tac >- simp[step_prov_def, out_prov_def, ld_erase_set_prov]) >>
  qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
  gen_tac >> strip_tac >> irule ld_set_prov_selected >>
  qexistsl [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
QED

val _ = if null (hyp ld_sync_delegate_effect) then ()
        else raise Fail "DELEGATECALL producer has hypotheses";
