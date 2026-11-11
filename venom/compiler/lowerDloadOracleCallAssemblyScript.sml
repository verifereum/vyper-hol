Theory lowerDloadOracleCallAssembly
Ancestors
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyAllocBounds venomWf
  lowerDloadExternalCallEffects lowerDloadSafetyWriteAssembly lowerDloadSafetyBytes
  lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyUpdates
  lowerDloadSafetyKernel lowerDloadSafetyRelation ptrDiscipline venomExecSemantics venomCallOracleDefs venomState
  memLocDefs pointerConfinedDefs codegenRel contextCodegenRel venomInst finite_map pred_set list words arithmetic

(* A numeric use observes either a selected translated pointer or an
   untainted scalar.  Definedness is transported independently of value class. *)
Theorem ld_numeric_operand_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\ op_taint tn op = {} /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x /\
      (op_prov f.lf_H op = NONE ==> x = y) /\
      (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `?x. eval_operand op f.lf_src = SOME x` by
    (irule ld_write_operand_defined >> metis_tac[]) >>
  qexists_tac `x` >> simp[] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >> metis_tac[]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def] >>
  drule_all ld_vars_value >> Cases_on `FLOOKUP f.lf_H s` >>
  simp[ld_word_agree_empty]
QED


Theorem ld_filter_unique_index[local]:
  !xs x i j. FILTER ($= x) xs = [x] /\
    i < LENGTH xs /\ j < LENGTH xs /\ EL i xs = x /\ EL j xs = x ==>
    i = j
Proof
  Induct >- simp[] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `x = h`
  >- (`FILTER ($= h) xs = []` by
        (qpat_x_assum `FILTER _ (_::_) = _` mp_tac >>
         asm_rewrite_tac[FILTER, CONS_11]) >>
      `!k. k < LENGTH xs ==> EL k xs <> h` by
        (qpat_x_assum `FILTER _ _ = []` mp_tac >>
         simp[FILTER_EQ_NIL, EVERY_MEM, MEM_EL] >> metis_tac[]) >>
      Cases_on `i` >> Cases_on `j` >> gvs[EL]) >>
  `FILTER ($= x) xs = [x]` by
    (qpat_x_assum `FILTER _ (_::_) = _` mp_tac >> asm_rewrite_tac[FILTER]) >>
  Cases_on `i` >> Cases_on `j` >> gvs[EL] >>
  first_x_assum irule >> simp[]
QED

Theorem ld_ptr_use_scalar_index:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> INVOKE /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ] /\
  mem_read_ops inst = SOME rd /\ mem_write_ops inst = SOME wr /\
  rd.iao_ofst = EL ri inst.inst_operands /\
  wr.iao_ofst = EL wi inst.inst_operands /\
  i < LENGTH inst.inst_operands /\ ri < LENGTH inst.inst_operands /\
  wi < LENGTH inst.inst_operands /\ i <> ri /\ i <> wi /\
  EL i inst.inst_operands = Var v ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  qpat_x_assum `ptr_use_ok _ _ _`
    (mp_tac o REWRITE_RULE [ptr_use_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
    disj1_tac >> fs[])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  gvs[Excl "FILTER"]
  >- (`i = wi` by
        (irule (INST_TYPE [``:'a`` |-> ``:operand``] ld_filter_unique_index) >>
         qexistsl_tac [`Var v`,`inst.inst_operands`] >> simp[]) >> fs[]) >>
  `i = ri` by
    (irule (INST_TYPE [``:'a`` |-> ``:operand``] ld_filter_unique_index) >>
     qexistsl_tac [`Var v`,`inst.inst_operands`] >> simp[]) >> fs[]
QED

Theorem ld_oracle_call_scalar_index:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\ MEM i [0;1;2;4;6]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
    inst.inst_operands = [g;a;ao;az;ro;rz] /\ MEM i [0;1;3;5])) /\
  EL i inst.inst_operands = Var x ==>
  x NOTIN fn_pv P fn
Proof
  strip_tac >> (fs[] >> irule ld_ptr_use_scalar_index >>
  (reverse conj_tac >- simp[]) >>
  qexistsl_tac [`i`,`inst`] >>
  simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  qexistsl_tac [`if inst.inst_opcode = CALL then 3 else 2`,
                `if inst.inst_opcode = CALL then 5 else 4`] >>
  simp[EL] >> fs[] >> gvs[])
QED

Theorem ld_oracle_call_scalar_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\ MEM i [0;1;2;4;6]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
    inst.inst_operands = [g;a;ao;az;ro;rz] /\ MEM i [0;1;3;5])) ==>
  eval_operand (EL i inst.inst_operands) f.lf_src =
  eval_operand (EL i inst.inst_operands) f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM (EL i inst.inst_operands) inst.inst_operands` by
    (simp[MEM_EL] >> qexists_tac `i` >> simp[] >>
     first_x_assum strip_assume_tac >> fs[] >> gvs[]) >>
  `!x. EL i inst.inst_operands = Var x ==> x NOTIN fn_pv P f.lf_fn` by
    (metis_tac[ld_oracle_call_scalar_index]) >>
  `op_prov f.lf_H (EL i inst.inst_operands) = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  irule ld_vars_operand_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >> conj_tac
  >- (irule ld_numeric_operand_nonopaque >> simp[] >>
      qexists_tac `inst` >> simp[] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> fs[] >> metis_tac[]) >>
  `op_taint tn (EL i inst.inst_operands) = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> fs[] >> metis_tac[]) >>
  gvs[op_taint_def]
QED

Theorem ld_oracle_call_dispatch:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
    st = t.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)) /\
  step_inst_base inst t = OK ts ==>
  ?gas addr value at size rt rsize.
    eval_operand g t = SOME gas /\ eval_operand a t = SOME addr /\
    (inst.inst_opcode = CALL ==> eval_operand v t = SOME value) /\
    (inst.inst_opcode = STATICCALL ==> value = 0w) /\
    (inst.inst_opcode = CALL ==> ~(st /\ value <> 0w)) /\
    eval_operand ao t = SOME at /\ eval_operand az t = SOME size /\
    eval_operand ro t = SOME rt /\ eval_operand rz t = SOME rsize /\
    exec_ext_call inst t gas addr value at size rt rsize st = OK ts
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_oracle_call_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
    st = f.lf_tgt.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)) /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?gas addr value x y size r q rsize.
    eval_operand g f.lf_src = SOME gas /\
    eval_operand a f.lf_src = SOME addr /\
    (inst.inst_opcode = CALL ==> eval_operand v f.lf_src = SOME value) /\
    (inst.inst_opcode = STATICCALL ==> value = 0w) /\
    (inst.inst_opcode = CALL ==> ~(st /\ value <> 0w)) /\
    eval_operand ao f.lf_src = SOME x /\
    eval_operand az f.lf_src = SOME size /\
    eval_operand ro f.lf_src = SOME r /\
    eval_operand rz f.lf_src = SOME rsize /\
    eval_operand ao f.lf_tgt = SOME y /\
    eval_operand ro f.lf_tgt = SOME q /\
    (op_prov f.lf_H ao = NONE ==> x = y) /\
    (!k. op_prov f.lf_H ao = SOME k ==> ld_wordrel A (SOME k) x y) /\
    (op_prov f.lf_H ro = NONE ==> r = q) /\
    (!k. op_prov f.lf_H ro = SOME k ==> ld_wordrel A (SOME k) r q) /\
    exec_ext_call inst f.lf_tgt gas addr value y size q rsize st = OK ts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i. ((inst.inst_opcode = CALL /\ MEM i [0;1;2;4;6]) \/
         (inst.inst_opcode = STATICCALL /\ MEM i [0;1;3;5])) ==>
     eval_operand (EL i inst.inst_operands) f.lf_src =
     eval_operand (EL i inst.inst_operands) f.lf_tgt` by
    (rpt strip_tac >> irule ld_oracle_call_scalar_equal >> simp[] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >> metis_tac[]) >>
  `!op z. MEM op inst.inst_operands /\ eval_operand op f.lf_tgt = SOME z ==>
    ?w. eval_operand op f.lf_src = SOME w /\
      (op_prov f.lf_H op = NONE ==> w = z) /\
      (!k. op_prov f.lf_H op = SOME k ==> ld_wordrel A (SOME k) w z)` by
    (rpt strip_tac >>
     `op_taint tn op = {}` by
       (irule ld_numeric_operand_untainted >>
        qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[] >>
        qpat_x_assum `_ \/ _` strip_assume_tac >> fs[] >> gvs[]) >>
     irule ld_numeric_operand_observation >> simp[] >>
     conj_tac >- (qexists_tac `tn` >> simp[]) >>
     conj_tac >- (qexists_tac `inst` >> simp[] >>
       qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
     qexists_tac `P` >> simp[]) >>
  drule_all ld_oracle_call_dispatch >> strip_tac >>
  rename1 `eval_operand az f.lf_tgt = SOME n` >>
  `?x. eval_operand ao f.lf_src = SOME x /\
      (op_prov f.lf_H ao = NONE ==> x = at) /\
      (!k. op_prov f.lf_H ao = SOME k ==> ld_wordrel A (SOME k) x at)` by
    (first_x_assum irule >> qpat_x_assum `_ \/ _` strip_assume_tac >> fs[]) >>
  `?r. eval_operand ro f.lf_src = SOME r /\
      (op_prov f.lf_H ro = NONE ==> r = rt) /\
      (!k. op_prov f.lf_H ro = SOME k ==> ld_wordrel A (SOME k) r rt)` by
    (first_x_assum irule >> qpat_x_assum `_ \/ _` strip_assume_tac >> fs[]) >>
  qexistsl_tac [`gas`,`addr`,`value`,`x`,`at`,`n`,`r`,`rt`,`rsize`] >>
  simp[] >> qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >>
  first_x_assum (fn th => map_every (fn i => mp_tac (Q.SPEC i th))
    [`0`,`1`,`2`,`3`,`4`,`5`,`6`]) >> simp[EL]
QED

Theorem ld_observed_memory_read:
  ld_memory lo A tn s t /\
  access_ok lo (ld_erase A o_f H) fn inst s /\
  taint_ok fn tn inst s /\ ~about_to_revert fn inst s /\
  ~in_revert_forward fn s /\
  ~MEM inst.inst_opcode [MLOAD;ILOAD;MCOPY;RETURN] /\
  mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!k. op_prov H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) x y) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  read_memory (w2n x) n s = read_memory (w2n y) n t
Proof
  strip_tac >> Cases_on `n = 0` >- gvs[read_memory_def] >>
  `!j. j < n ==> w2n x+j NOTIN tn.t_mem` by
    (fs[taint_ok_def] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`w2n x`,`n`,`w2n x+j`] mp_tac) >>
     simp[] >> decide_tac) >>
  `0 < n` by decide_tac >>
  drule_all ld_read_access_classified >> strip_tac
  >- (gvs[] >> irule ld_memory_read_low >>
      qexistsl_tac [`A`,`lo`,`tn`] >> simp[ADD_COMM]) >>
  gvs[] >> irule ld_memory_read_slot >>
  qexistsl_tac [`A`,`k`,`lo`,`sz`,`tn`] >> simp[GSYM ADD_ASSOC]
QED

Theorem ld_oracle_call_ranges:
  ld_memory lo A tn s t /\
  access_ok lo (ld_erase A o_f H) fn inst s /\ taint_ok fn tn inst s /\
  ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
    eval_operand v s = SOME value) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
    inst.inst_operands = [g;a;ao;az;ro;rz])) /\
  eval_operand g s = SOME gas /\ eval_operand a s = SOME addr /\
  eval_operand ao s = SOME x /\ eval_operand az s = SOME n /\
  eval_operand ro s = SOME r /\ eval_operand rz s = SOME rsize /\
  (op_prov H ao = NONE ==> x = y) /\
  (!k. op_prov H ao = SOME k ==> ld_wordrel A (SOME k) x y) /\
  (op_prov H ro = NONE ==> r = q) /\
  (!k. op_prov H ro = SOME k ==> ld_wordrel A (SOME k) r q) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  read_memory (w2n x) (w2n n) s = read_memory (w2n y) (w2n n) t /\
  (w2n rsize = 0 \/ (w2n r = w2n q /\ w2n r + w2n rsize <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n r = b+delta /\ w2n q = c+delta /\ delta + w2n rsize <= sz))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `mem_read_ops inst = SOME <|iao_ofst := ao; iao_size := SOME az;
                            iao_max_size := SOME az|> /\
   mem_write_ops inst = SOME <|iao_ofst := ro; iao_size := NONE;
                             iao_max_size := SOME rz|> /\
   MEM (w2n x,w2n n) (source_memory_read_ranges inst s) /\
   MEM (w2n r,w2n rsize) (source_memory_write_ranges inst s) /\
   ~about_to_revert fn inst s /\
   ~MEM inst.inst_opcode [MLOAD;ILOAD;MCOPY;RETURN]` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> fs[] >>
     simp[mem_read_ops_def, mem_write_ops_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, eval_operands_def, about_to_revert_def]) >>
  conj_tac
  >- (irule ld_observed_memory_read >> simp[] >>
      qexistsl_tac [`A`,`H`,`fn`,`inst`,`lo`,
        `<|iao_ofst := ao; iao_size := SOME az; iao_max_size := SOME az|>`,`tn`] >>
      fs[] >> metis_tac[]) >>
  Cases_on `w2n rsize = 0` >- gvs[] >>
  `0 < w2n rsize` by decide_tac >>
  drule ld_write_access_classified >> simp[] >>
  disch_then (qspecl_then [`q`,`r`,`w2n rsize`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[ADD_COMM] >> metis_tac[]
QED

Theorem ld_exec_ext_call_frame:
  exec_ext_call inst s gas addr value ao az ro rz st = OK ss /\
  inst.inst_outputs = [out] /\ FLOOKUP ss.vs_vars out = SOME w ==>
  ss.vs_vars = s.vs_vars |+ (out,w) /\
  ss.vs_params = s.vs_params /\ ss.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  gvs[exec_ext_call_def, consume_call_outcome_eq, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_oracle_call_taint:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL) /\
  3 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst s = [(w2n (ro:bytes32),w2n (rz:bytes32))] /\
  ss.vs_allocas = s.vs_allocas /\ ss.vs_fmp = s.vs_fmp ==>
  step_taint inst s ss tn = tn with <|
    t_var := set_var_taint tn.t_var inst.inst_outputs {};
    t_mem := tn.t_mem DIFF {w2n ro+j | j < LENGTH (TAKE (w2n rz) ss.vs_returndata)};
    t_stor := adopt_reset inst
      (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
       ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor;
    t_trans := adopt_reset inst
      (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
       ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans |>
Proof
  strip_tac >>
  `written_taint tn inst s = {} /\ out_taint tn inst s = {}` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >>
     Cases_on `t` >> fs[written_taint_def, out_taint_def]) >>
  `new_site_bytes s ss = {}` by
    (simp[new_site_bytes_def, EXTENSION] >> rpt strip_tac >>
     Cases_on `aid IN FDOM s.vs_allocas` >> fs[FLOOKUP_DEF]) >>
  `range_bytes (step_writes inst s ss) =
    {w2n ro+j | j < LENGTH (TAKE (w2n rz) ss.vs_returndata)}` by
    (simp[step_writes_def, range_bytes_def, LENGTH_TAKE_EQ, EXTENSION] >>
     Cases_on `w2n rz <= LENGTH ss.vs_returndata` >> simp[MIN_DEF] >>
     gen_tac >> (eq_tac
     >- (strip_tac >> qexists_tac `x - w2n ro` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac)) >>
  Cases_on `tn` >>
  simp[step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       taint_component_equality]
QED

(* Variable agreement observes only the two variable maps and parameter lists. *)
Theorem ld_vars_state_cong:
  !s f t P A. s.vs_vars = f.lf_src.vs_vars /\ t.vs_vars = f.lf_tgt.vs_vars /\
  s.vs_params = f.lf_src.vs_params /\ t.vs_params = f.lf_tgt.vs_params ==>
  (ld_vars P A (f with <|lf_src := s; lf_tgt := t|>) <=> ld_vars P A f)
Proof
  simp[ld_vars_def]
QED

Theorem ld_oracle_call_vars:
  ld_vars P A f /\ MEM out (fn_ir_vars f.lf_fn) /\
  ss.vs_vars = f.lf_src.vs_vars |+ (out,w) /\
  ts.vs_vars = f.lf_tgt.vs_vars |+ (out,w) /\
  ss.vs_params = f.lf_src.vs_params /\
  ts.vs_params = f.lf_tgt.vs_params ==>
  ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
    lf_H := set_prov f.lf_H [out] NONE;
    lf_tv := set_var_taint f.lf_tv [out] mask|>)
Proof
  strip_tac >>
  `ld_vars P A (f with <|
    lf_src := f.lf_src with vs_vars := f.lf_src.vs_vars |+ (out,w);
    lf_tgt := f.lf_tgt with vs_vars := f.lf_tgt.vs_vars |+ (out,w);
    lf_H := set_prov f.lf_H [out] NONE;
    lf_tv := set_var_taint f.lf_tv [out] mask|>)` by
    (irule ld_vars_write >> simp[set_var_taint_def, FLOOKUP_UPDATE,
       word_agree_except_def]) >>
  qspecl_then [`ss`,`f with <|
    lf_src := f.lf_src with vs_vars := f.lf_src.vs_vars |+ (out,w);
    lf_tgt := f.lf_tgt with vs_vars := f.lf_tgt.vs_vars |+ (out,w);
    lf_H := set_prov f.lf_H [out] NONE;
    lf_tv := set_var_taint f.lf_tv [out] mask|>`,`ts`]
    mp_tac ld_vars_state_cong >> simp[]
QED

Theorem ld_effect_var_mask[simp]:
  (ld_memory lo A (tn with t_var := tv) s t <=> ld_memory lo A tn s t) /\
  (ld_nonghost (tn with t_var := tv) s t <=> ld_nonghost tn s t)
Proof
  simp[ld_memory_def, ld_nonghost_def]
QED


(* exec_ext_call ignores gas and converts ret offsets/sizes with w2n.
   Fix the independent type parameters at the bytes32 operand interface. *)
val call_effect = INST_TYPE [
  ``:'a`` |-> ``:256 word``, ``:'e`` |-> ``:256 word``,
  ``:'b`` |-> ``:256``, ``:'c`` |-> ``:256``, ``:'d`` |-> ``:256``]
  ld_exec_ext_call_effect;

Theorem ld_oracle_call_observed_effect:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  tn.t_var = f.lf_tv /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  (inst.inst_opcode = CALL ==> st = f.lf_src.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = STATICCALL ==> st) /\
  3 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst f.lf_src = [(w2n (ro:bytes32),w2n (rz:bytes32))] /\
  read_memory (w2n ao) (w2n az) f.lf_src =
    read_memory (w2n at) (w2n az) f.lf_tgt /\
  exec_ext_call inst f.lf_tgt (gas:bytes32) addr value at az (rt:bytes32) rz st = OK ts /\
  (w2n rz = 0 \/ (w2n ro = w2n rt /\ w2n ro + w2n rz <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n ro = b+delta /\ w2n rt = c+delta /\ delta + w2n rz <= sz)) ==>
  ?ss. exec_ext_call inst f.lf_src gas addr value ao az ro rz st = OK ss /\
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
  drule_all call_effect >> disch_then (qspec_then `gas` strip_assume_tac) >>
  `ss.vs_vars = f.lf_src.vs_vars |+ (out,w) /\
   ss.vs_params = f.lf_src.vs_params /\ ss.vs_fmp = f.lf_src.vs_fmp` by
    (qpat_assum `exec_ext_call inst f.lf_src _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac ld_exec_ext_call_frame) >> simp[]) >>
  `ts.vs_vars = f.lf_tgt.vs_vars |+ (out,w) /\
   ts.vs_params = f.lf_tgt.vs_params /\ ts.vs_fmp = f.lf_tgt.vs_fmp` by
    (qpat_assum `exec_ext_call inst f.lf_tgt _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac ld_exec_ext_call_frame) >> simp[]) >>
  `step_taint inst f.lf_src ss tn = tn' with
     t_var := set_var_taint f.lf_tv [out] {}` by
    ((Q.SUBGOAL_THEN
       `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
        inst.inst_opcode = DELEGATECALL` assume_tac >- metis_tac[]) >>
     drule_all ld_oracle_call_taint >> simp[]) >>
  qpat_x_assum `tn' = _` kall_tac >>
  qexists_tac `ss` >> simp[] >> irule ld_oracle_call_vars >> simp[] >>
  conj_tac >- (qexists_tac `w` >> simp[]) >>
  irule ld_inst_output_ir >> qexists_tac `inst` >> simp[]
QED

Theorem ld_oracle_call_step:
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
  ((inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
    st = f.lf_tgt.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)) /\
  step_inst_base inst f.lf_tgt = OK ts ==>
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
  drule_all ld_oracle_call_operands >> strip_tac >>
  rename1 `eval_operand az f.lf_src = SOME n` >>
  `read_memory (w2n x) (w2n n) f.lf_src = read_memory (w2n y) (w2n n) f.lf_tgt /\
   (w2n rsize = 0 \/ (w2n r = w2n q /\ w2n r + w2n rsize <= lo) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n r = b+delta /\ w2n q = c+delta /\ delta + w2n rsize <= sz))` by
    (irule ld_oracle_call_ranges >>
     qpat_assum `access_ok _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >>
     simp[] >> qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >> metis_tac[]) >>
  `3 < LENGTH inst.inst_operands /\
   source_memory_write_ranges inst f.lf_src = [(w2n r,w2n rsize)]` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     simp[source_memory_write_ranges_def, fixed_source_write_range_def,
          memory_range_of_operands_def]) >>
  `f.lf_src.vs_call_ctx = f.lf_tgt.vs_call_ctx` by
    fs[ld_nonghost_def] >>
  qpat_assum `exec_ext_call inst f.lf_tgt _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac ld_oracle_call_observed_effect) >>
  disch_then (qspecl_then [`tn`,`r`,`lo`,`x`,`P`,`A`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    qpat_x_assum `inst.inst_opcode = CALL /\ _ \/ _` strip_assume_tac >>
    simp[] >> metis_tac[wordsTheory.w2n_eq_0])) >>
  strip_tac >> qexists_tac `ss` >> simp[] >>
  `f.lf_src.vs_call_ctx = f.lf_tgt.vs_call_ctx` by
    fs[ld_nonghost_def] >>
  qpat_x_assum `inst.inst_opcode = CALL /\ _ \/ _` strip_assume_tac >>
  gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  Cases_on `f.lf_tgt.vs_call_ctx.cc_static` >> FIRST [gvs[]]
QED

Theorem ld_set_prov_selected:
  (!a. q = SOME a ==> a IN FDOM A) /\
  (!a. a IN FRANGE (H : string |-> 'a) ==> a IN FDOM A) ==>
  !a. a IN FRANGE (set_prov H outs q) ==> a IN FDOM A
Proof
  strip_tac >> Cases_on `outs`
  >- (gvs[set_prov_def, IN_FRANGE, FDOM_DRESTRICT, DRESTRICT_DEF] >> metis_tac[]) >>
  Cases_on `t` >> Cases_on `q` >>
  gvs[set_prov_def, FAPPLY_FUPDATE_THM, FRANGE_FUPDATE, IN_FRANGE,
      FDOM_DRESTRICT, DRESTRICT_DEF] >> metis_tac[]
QED

Theorem ld_oracle_call_provenance:
  MEM inst.inst_opcode [CALL;STATICCALL] ==>
  step_prov PG (ld_erase A o_f H) inst ss =
    ld_erase A o_f set_prov H inst.inst_outputs NONE
Proof
  simp[MEM] >> strip_tac >>
  simp[step_prov_def, out_prov_def, ld_erase_set_prov]
QED

Theorem ld_sync_ptr_ok:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==> fn_ptr_ok P fn
Proof
  strip_tac >> drule ld_sync_active >> strip_tac >>
  `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
  qhdtm_x_assum `ld_sync` mp_tac >>
  simp[ld_sync_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ld_sync_slots:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  FDOM A = ld_slots A frames
Proof
  simp[ld_sync_def]
QED

Theorem ld_sync_maps:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  EVERY (ld_maps A) frames
Proof
  simp[ld_sync_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ld_active_inst_member:
  active_inst fn inst s ==> MEM inst (fn_insts fn)
Proof
  simp[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
  metis_tac[MEM_EL]
QED

Theorem ld_sync_oracle_call_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
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
  `fn_shape_ok fn /\ fn_inst_wf fn` by
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
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  gvs[step_inst_non_invoke] >>
  `?g a v ao az ro rz st.
    (inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
      st = f.lf_tgt.vs_call_ctx.cc_static) \/
    (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     pure_rewrite_tac[inst_wf_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  gvs[] >>
  (Q.SUBGOAL_THEN
    `((inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
      (if inst.inst_opcode = CALL then f.lf_tgt.vs_call_ctx.cc_static else T) =
        f.lf_tgt.vs_call_ctx.cc_static) \/
     (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\
      (if inst.inst_opcode = CALL then f.lf_tgt.vs_call_ctx.cc_static else T) = T))`
    assume_tac >- simp[]) >>
  `tn.t_var = f.lf_tv` by simp[] >>
  drule_all ld_oracle_call_step >> strip_tac >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >> (conj_tac >- (irule ld_oracle_call_provenance >> simp[])) >>
  qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
  gen_tac >> strip_tac >> irule ld_set_prov_selected >>
  qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
QED

(* Checked masked-to-exact consumer at SHA3's real operand shape. *)
Theorem ld_sha3_observed_bytes:
  ld_memory lo A tn s t /\
  access_ok lo (ld_erase A o_f H) fn inst s /\
  taint_ok fn tn inst s /\ ~about_to_revert fn inst s /\
  ~in_revert_forward fn s /\ inst.inst_opcode = SHA3 /\
  inst.inst_operands = [off;len] /\
  eval_operand off s = SOME x /\ eval_operand len s = SOME n /\
  (op_prov H off = NONE ==> x = y) /\
  (!k. op_prov H off = SOME k ==> ld_wordrel A (SOME k) x y) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
  TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w)
Proof
  strip_tac >>
  `mem_read_ops inst = SOME <|iao_ofst := off; iao_size := SOME len;
                             iao_max_size := SOME len|>` by
    simp[mem_read_ops_def] >>
  `MEM (w2n x,w2n n) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `~MEM inst.inst_opcode [MLOAD;ILOAD;MCOPY;RETURN]` by simp[] >>
  pure_rewrite_tac[GSYM read_memory_def] >>
  irule ld_observed_memory_read >> simp[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`H`, `fn`, `lo`, `tn`] >> simp[]
QED

val _ = if null (hyp ld_sha3_observed_bytes) then ()
        else raise Fail "SHA3 observation consumer has hypotheses";
