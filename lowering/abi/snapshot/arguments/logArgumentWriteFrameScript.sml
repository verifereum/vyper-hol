(* TOP-LEVEL: earlier Log arguments survive arbitrary writes outside
   their complete memory footprints, with unchanged operand values.
   This includes expression compilers which allocate and write RAM. *)
Theory logArgumentWriteFrame
Ancestors
  typedLogArgs abiFieldValueFrame abiMemoryFrame memoryValueTyping
  valueLoadProps valueEncoding compileEnv venomState list pair words
Libs tautLib

Definition log_args_writes_separated_def:
  log_args_writes_separated [] [] ss writes = T /\
  log_args_writes_separated ((src,ty)::args) (tv::tvs) ss writes =
    ((~is_word_type ty ==> !src_addr. eval_operand src ss = SOME src_addr ==>
      EVERY (\(base,write_len). abi_window_separated (w2n src_addr) (type_memory_size tv) base write_len) writes) /\
     log_args_writes_separated args tvs ss writes) /\
  log_args_writes_separated _ _ ss writes = F
End

Theorem lowered_value_rel_write_frame:
  !ty tv v src writes before after.
    lowered_value_rel ty tv v src before /\
    (~is_word_type ty ==> !src_addr. eval_operand src before = SOME src_addr ==>
      EVERY (\(base,write_len). abi_window_separated (w2n src_addr) (type_memory_size tv) base write_len) writes) /\
    eval_operand src after = eval_operand src before /\ abi_memory_frame writes before after ==>
    lowered_value_rel ty tv v src after
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty`
  >- (qpat_x_assum `lowered_value_rel _ _ _ _ before` mp_tac >> simp[lowered_value_rel_def]) >>
  qpat_x_assum `lowered_value_rel _ _ _ _ before` mp_tac >>
  asm_simp_tac bool_ss [lowered_value_rel_def] >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `src_addr` strip_assume_tac)) >>
  `val_wf tv v` by (drule value_has_type_val_wf >> simp[]) >>
  `EVERY (\(base,write_len). abi_window_separated (w2n src_addr) (type_memory_size tv) base write_len) writes` by
    (qpat_x_assum `~is_word_type ty ==> _` mp_tac >>
     asm_simp_tac bool_ss [] >> disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
  `memory_value_rel tv v (w2n src_addr) after.vs_memory` by
    (qspecl_then [`tv`, `v`, `w2n src_addr`, `writes`, `before`, `after`] mp_tac abi_memory_frame_value >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  simp[lowered_value_rel_def]
QED

Theorem log_args_rel_write_frame:
  !args tvs values writes before after.
    log_args_rel args tvs values before /\ log_args_writes_separated args tvs before writes /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args /\
    abi_memory_frame writes before after ==>
    log_args_rel args tvs values after
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `tvs` >> Cases_on `values` >> simp[log_args_rel_def]) >>
  rpt gen_tac >> rename1 `log_args_rel (arg::rest) _ _ _` >>
  Cases_on `arg` >> Cases_on `tvs` >> Cases_on `values` >>
  simp_tac (srw_ss()) [log_args_rel_def, log_args_writes_separated_def] >> strip_tac >>
  conj_tac >- (drule_all lowered_value_rel_write_frame >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_args_writes_separated_operand_frame:
  !args tvs writes before after.
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    (log_args_writes_separated args tvs after writes <=> log_args_writes_separated args tvs before writes)
Proof
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_writes_separated_def]) >>
  rpt gen_tac >> rename1 `EVERY _ (arg::rest)` >> Cases_on `arg` >> Cases_on `tvs` >>
  simp_tac (srw_ss()) [log_args_writes_separated_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_args_writes_separated_append:
  !args tvs ss left right.
    log_args_writes_separated args tvs ss (left ++ right) <=>
    log_args_writes_separated args tvs ss left /\ log_args_writes_separated args tvs ss right
Proof
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_writes_separated_def]) >>
  rpt gen_tac >> rename1 `log_args_writes_separated (arg::rest) _ _ _` >>
  Cases_on `arg` >> Cases_on `tvs` >>
  simp[log_args_writes_separated_def, EVERY_APPEND, FORALL_AND_THM, IMP_CONJ_THM] >> tautLib.TAUT_TAC
QED

Theorem log_args_safe_writes_separated:
  !args tvs ss base write_len.
    log_args_safe args tvs ss base write_len ==>
    log_args_writes_separated args tvs ss [(base,write_len)]
Proof
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_safe_def, log_args_writes_separated_def]) >>
  rpt gen_tac >> rename1 `log_args_safe (arg::rest) _ _ _ _` >>
  Cases_on `arg` >> Cases_on `tvs` >>
  simp_tac (srw_ss()) [log_args_safe_def, log_args_writes_separated_def] >> strip_tac >>
  conj_tac >- (fs[log_arg_safe_def, abi_window_separated_def, regions_disjoint_def] >>
    rpt strip_tac >> first_x_assum drule >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED
