(* External completion observations: no equality of masked requests is required. *)
Theory lowerDloadExternalBoundary
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyValues lowerDloadSafetyWriteBytes
  regularCallEmitSim finite_map pred_set list arithmetic
  ptrDiscipline extCallOracle venomCallOracleDefs venomState pair vfmState
  venomExecSemantics

Theorem ld_take_outcome_rest:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  SND (take_outcome rq os) = SND (take_outcome rq' os)
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def] >>
  Cases_on `rq.cr_kind = MessageCall` >>
  Cases_on `rq'.cr_kind = MessageCall` >> simp[] >>
  Cases_on `h.co_success` >> simp[]
QED

Theorem ld_take_outcome_success:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_kind = rq'.cr_kind ==>
  (FST (take_outcome rq os)).co_success =
    (FST (take_outcome rq' os)).co_success
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def] >>
  Cases_on `rq'.cr_kind = MessageCall` >> simp[] >>
  Cases_on `h.co_success` >> simp[]
QED

Theorem ld_take_outcome_returndata:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_kind = rq'.cr_kind ==>
  (FST (take_outcome rq os)).co_returnData =
    (FST (take_outcome rq' os)).co_returnData
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def] >>
  Cases_on `rq'.cr_kind = MessageCall` >> simp[] >>
  Cases_on `h.co_success` >> simp[]
QED

Theorem ld_nonghost_accounts_empty:
  ld_nonghost tn s t /\ tn.t_stor = {} ==>
  s.vs_accounts = t.vs_accounts
Proof
  strip_tac >> fs[ld_nonghost_def] >>
  simp[FUN_EQ_THM] >> gen_tac >>
  qpat_x_assum `!a. _ /\ _` (qspec_then `x` strip_assume_tac) >>
  `(s.vs_accounts x).storage = (t.vs_accounts x).storage` by
    fs[storage_agree_except_def, key_taint_def, ld_word_agree_empty,
       FUN_EQ_THM] >>
  qpat_x_assum `(s.vs_accounts x).storage = _`
    (fn th => fs[GSYM th])
QED

Theorem ld_nonghost_transient_empty:
  ld_nonghost tn s t /\ tn.t_trans = {} ==>
  s.vs_transient = t.vs_transient
Proof
  strip_tac >> fs[ld_nonghost_def] >>
  fs[storage_agree_except_def, key_taint_def, ld_word_agree_empty,
     FUN_EQ_THM]
QED

Theorem ld_consume_adoption_cases[local]:
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_static = rq'.cr_static /\
  rq.cr_kind = MessageCall /\ rq.cr_kind = rq'.cr_kind /\
  (inst.inst_opcode = CALL ==> rq.cr_static = s.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = STATICCALL ==> rq.cr_static) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq ro rs s = (w,ss) /\
  consume_call_outcome rq' ro' rs' t = (w',ts) ==>
  if inst.inst_opcode = CALL /\
     (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
      ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success)
  then ss.vs_accounts = ts.vs_accounts /\ ss.vs_transient = ts.vs_transient
  else ss.vs_accounts = s.vs_accounts /\ ts.vs_accounts = t.vs_accounts /\
       ss.vs_transient = s.vs_transient /\ ts.vs_transient = t.vs_transient
Proof
  strip_tac >>
  namedCases_on `t.vs_outcomes` ["", "outcome rest"] >>
  gvs[consume_call_outcome_eq, take_outcome_def, adopt_outcome_def,
      failed_outcome_def] >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  Cases_on `rq'.cr_static` >> Cases_on `outcome.co_success` >>
  gvs[consume_call_outcome_eq, take_outcome_def, adopt_outcome_def,
      computed_precompile_def, failed_outcome_def] >>
  gvs[record_request_def, computed_precompile_def] >>
  Cases_on `x` >> gvs[failed_outcome_def]
QED

Theorem ld_consume_call_nonghost:
  ld_nonghost tn s t /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_static = rq'.cr_static /\
  rq.cr_kind = rq'.cr_kind /\ rq.cr_kind = MessageCall /\
  (inst.inst_opcode = CALL ==> rq.cr_static = s.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = STATICCALL ==> rq.cr_static) /\
  consume_call_outcome rq ro rs s = (w,ss) /\
  consume_call_outcome rq' ro' rs' t = (w',ts) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  tn'.t_imm = tn.t_imm /\
  tn'.t_stor = adopt_reset inst
    (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
     ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor /\
  tn'.t_trans = adopt_reset inst
    (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
     ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans ==>
  ld_nonghost tn' ss ts
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_nonghost_def] >>
  `SND (take_outcome rq s.vs_outcomes) =
   SND (take_outcome rq' t.vs_outcomes)` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_rest >> simp[]) >>
  `(FST (take_outcome rq s.vs_outcomes)).co_returnData =
   (FST (take_outcome rq' t.vs_outcomes)).co_returnData` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_returndata >> metis_tac[]) >>
  `if inst.inst_opcode = CALL /\
      (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
       ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success)
   then ss.vs_accounts = ts.vs_accounts /\ ss.vs_transient = ts.vs_transient
   else ss.vs_accounts = s.vs_accounts /\ ts.vs_accounts = t.vs_accounts /\
        ss.vs_transient = s.vs_transient /\ ts.vs_transient = t.vs_transient` by
    (irule ld_consume_adoption_cases >> metis_tac[]) >>
  pop_assum mp_tac >> IF_CASES_TAC >> strip_tac >>
  fs[adopt_reset_def] >>
  gvs[consume_call_outcome_eq] >>
  gvs[ld_nonghost_def, storage_agree_except_def, word_agree_except_def] >>
  metis_tac[]
QED

(* Only actual returned bytes are overwritten; an empty write has no bounds. *)
Theorem ld_memory_write_classified:
  ld_memory lo A tn s t /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  tn'.t_mem = tn.t_mem DIFF {ro+j | j < LENGTH xs} /\
  (xs = [] \/ (ro = rt /\ ro + LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta + LENGTH xs <= sz)) ==>
  ld_memory lo A tn'
    (write_memory_with_expansion ro xs s)
    (write_memory_with_expansion rt xs t)
Proof
  strip_tac
  >- (gvs[ld_memory_def, read_byte_write_memory_with_expansion] >> metis_tac[])
  >- (gvs[] >> irule ld_memory_write_low >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`{}`, `LENGTH xs`, `tn`] >> simp[ADD_COMM])
  >> gvs[] >> irule ld_memory_write_slot >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`{}`, `k`, `LENGTH xs`, `sz`, `tn`] >>
  simp[NoAsms, GSYM ADD_ASSOC] >> metis_tac[]
QED

Theorem ld_consume_call_effect:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_static = rq'.cr_static /\
  rq.cr_kind = rq'.cr_kind /\ rq.cr_kind = MessageCall /\
  (inst.inst_opcode = CALL ==> rq.cr_static = s.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = STATICCALL ==> rq.cr_static) /\
  consume_call_outcome rq ro rs s = (w,ss) /\
  consume_call_outcome rq' rt rs t = (w',ts) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  xs = TAKE rs ss.vs_returndata /\
  tn'.t_mem = tn.t_mem DIFF {ro+j | j < LENGTH xs} /\
  tn'.t_imm = tn.t_imm /\
  tn'.t_stor = adopt_reset inst
    (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
     ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor /\
  tn'.t_trans = adopt_reset inst
    (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
     ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans /\
  (xs = [] \/ (ro = rt /\ ro + LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta + LENGTH xs <= sz)) ==>
  w = w' /\ ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
  ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then strip_assume_tac >> (
  `ld_nonghost tn' ss ts` by (irule ld_consume_call_nonghost >> metis_tac[]) >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_nonghost_def] >>
  `(FST (take_outcome rq s.vs_outcomes)).co_success =
   (FST (take_outcome rq' t.vs_outcomes)).co_success` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_success >> metis_tac[]) >>
  `(FST (take_outcome rq s.vs_outcomes)).co_returnData =
   (FST (take_outcome rq' t.vs_outcomes)).co_returnData` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_returndata >> metis_tac[]) >>
  `ld_memory lo A tn'
    (write_memory_with_expansion ro xs s)
    (write_memory_with_expansion rt xs t)` by
    (irule ld_memory_write_classified >> metis_tac[]) >>
  conj_tac >- gvs[consume_call_outcome_eq] >>
  conj_tac
  >- (qpat_x_assum `ld_memory lo A tn' _ _` mp_tac >>
      qpat_x_assum `consume_call_outcome rq ro rs s = _` mp_tac >>
      qpat_x_assum `consume_call_outcome rq' rt rs t = _` mp_tac >>
      qpat_x_assum `xs = TAKE rs ss.vs_returndata` mp_tac >>
      qpat_x_assum `_.co_returnData = _.co_returnData` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[consume_call_outcome_eq] >> rpt strip_tac >>
      gvs[ld_memory_def] >> metis_tac[]) >>
  simp[] >> gvs[consume_call_outcome_eq])
QED

(* Exact current request projection; historical requests/logs need not agree. *)
Theorem ld_create_request_equal:
  ld_nonghost tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n off') (w2n sz) t ==>
  venom_create_request s value off sz salt =
    venom_create_request t value off' sz salt
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts` by
    metis_tac[ld_nonghost_accounts_empty] >>
  `s.vs_transient = t.vs_transient` by
    metis_tac[ld_nonghost_transient_empty] >>
  simp[venom_create_request_def]
QED

val _ = if null (hyp ld_create_request_equal) then ()
        else raise Fail "create request projection has hypotheses";

Theorem ld_extract_venom_effect:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  extract_venom_result t w rt n R = SOME (v,ts) /\
  xs = TAKE n ts.vs_returndata /\
  tn'.t_mem = tn.t_mem DIFF {ro+j | j < LENGTH xs} /\
  tn'.t_imm = tn.t_imm /\ tn'.t_stor = {} /\ tn'.t_trans = {} /\
  (xs = [] \/ (ro = rt /\ ro + LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta + LENGTH xs <= sz)) ==>
  ?ss. extract_venom_result s w ro n R = SOME (v,ss) /\
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
  `ld_memory lo A tn'
     (write_memory_with_expansion ro xs s)
     (write_memory_with_expansion rt xs t)` by
    (irule ld_memory_write_classified >> metis_tac[]) >>
  qpat_x_assum `extract_venom_result _ _ _ _ _ = _` mp_tac >>
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `result` >> gvs[] >>
  TRY (rename1 `case x of NONE => _ | SOME _ => _` >> Cases_on `x` >> gvs[]) >>
  gvs[ld_memory_def, ld_nonghost_def, storage_agree_except_def,
      word_agree_except_def] >> metis_tac[]
QED

val _ = if null (hyp ld_extract_venom_effect) then ()
        else raise Fail "delegate extraction transport has hypotheses";

(* CREATE consumes the same current oracle result, retaining separate locals. *)
Theorem ld_consume_create_effect:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  tn'.t_stor = {} /\ tn'.t_trans = {} /\
  consume_create_outcome rq s = (w,ss) /\
  consume_create_outcome rq t = (w',ts) ==>
  w = w' /\ ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
  ss.vs_vars = s.vs_vars /\ ts.vs_vars = t.vs_vars /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
  ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts` by
    metis_tac[ld_nonghost_accounts_empty] >>
  `s.vs_transient = t.vs_transient` by
    metis_tac[ld_nonghost_transient_empty] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_nonghost_def] >>
  gvs[consume_create_outcome_eq] >>
  Cases_on `rq.cr_static` >>
  Cases_on `(FST (take_outcome rq t.vs_outcomes)).co_success` >>
  gvs[adopt_outcome_def, ld_memory_def, ld_nonghost_def,
      storage_agree_except_def, word_agree_except_def] >>
  metis_tac[]
QED
