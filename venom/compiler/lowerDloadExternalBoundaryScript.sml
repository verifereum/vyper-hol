(* External completion observations: no equality of masked requests is required. *)
Theory lowerDloadExternalBoundary
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyValues lowerDloadSafetyWriteBytes
  regularCallEmitSim finite_map pred_set list arithmetic
  ptrDiscipline extCallOracle venomCallOracleDefs venomState pair vfmState

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
  Cases_on `result` >> simp[failed_outcome_def]
QED

Theorem ld_take_outcome_success:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_success =
    (FST (take_outcome rq' os)).co_success
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def]
QED

Theorem ld_take_outcome_returndata:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_returnData =
    (FST (take_outcome rq' os)).co_returnData
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def]
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
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq ro rs s = (w,ss) /\
  consume_call_outcome rq' ro' rs' t = (w',ts) ==>
  (ss.vs_accounts = s.vs_accounts /\ ts.vs_accounts = t.vs_accounts /\
   ss.vs_transient = s.vs_transient /\ ts.vs_transient = t.vs_transient) \/
  (ss.vs_accounts = ts.vs_accounts /\ ss.vs_transient = ts.vs_transient)
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rq'` by
    simp[computed_precompile_def] >>
  Cases_on `computed_precompile rq'`
  >- (Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
      fs[computed_precompile_def] >>
      rename1 `precompile_result _ _ = SOME result` >>
      Cases_on `result` >> Cases_on `rq'.cr_static` >>
      gvs[consume_call_outcome_eq, take_outcome_def, computed_precompile_def,
          failed_outcome_def, adopt_outcome_def]) >>
  Cases_on `t.vs_outcomes`
  >- gvs[consume_call_outcome_eq, take_outcome_def,
         failed_outcome_def, adopt_outcome_def] >>
  rename1 `t.vs_outcomes = outcome::rest` >>
  Cases_on `outcome.co_success /\ ~rq'.cr_static` >>
  gvs[consume_call_outcome_eq, take_outcome_def, adopt_outcome_def]
QED

Theorem ld_consume_call_nonghost:
  ld_nonghost tn s t /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data /\ rq.cr_static = rq'.cr_static /\
  consume_call_outcome rq ro rs s = (w,ss) /\
  consume_call_outcome rq' ro' rs' t = (w',ts) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  tn'.t_imm = tn.t_imm /\
  tn'.t_stor = adopt_reset inst (ss.vs_accounts <> s.vs_accounts) tn.t_stor /\
  tn'.t_trans = adopt_reset inst (ss.vs_transient <> s.vs_transient) tn.t_trans ==>
  ld_nonghost tn' ss ts
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_nonghost_def] >>
  `SND (take_outcome rq s.vs_outcomes) =
   SND (take_outcome rq' t.vs_outcomes)` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_rest >> simp[]) >>
  `(FST (take_outcome rq s.vs_outcomes)).co_returnData =
   (FST (take_outcome rq' t.vs_outcomes)).co_returnData` by
    (asm_rewrite_tac[] >> irule ld_take_outcome_returndata >> simp[]) >>
  drule_all ld_consume_adoption_cases >> strip_tac >>
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
