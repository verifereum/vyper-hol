Theory concretizePtrWriteFootprint
Ancestors concretizePtrPrefixLedger ptrDiscipline codegenRel venomExecSemantics
  venomState venomInst arithmetic pred_set finite_map list

(* Footprints require successful evaluation of the VALUE as well as address.
   This checked probe refutes address-only interval characterization. *)
Theorem ptr_mstore_missing_value_probe:
  fixed_source_write_range (s with vs_vars := FEMPTY)
    (Lit 0w) (Var "missing") 32 = [] /\
  eval_operand (Lit 0w) (s with vs_vars := FEMPTY) = SOME 0w
Proof
  EVAL_TAC
QED

Theorem ptr_mstore_footprint_interval:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME x /\ eval_operand value s = SOME v ==>
  (i IN range_bytes (step_writes inst s post) <=> w2n x <= i /\ i < w2n x + 32)
Proof
  strip_tac >>
  simp[step_writes_def, source_memory_write_ranges_def,
    fixed_source_write_range_def, range_bytes_def]
QED

Theorem ptr_mstore_owned_footprint:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME x /\ eval_operand ta t = SOME y /\
  eval_operand sv s = SOME v /\ eval_operand tv t = SOME vt /\
  ptr_ledger_owned_site registry births token aid srcbase sz pos /\
  w2n x = srcbase + d /\ w2n y = pos + d /\ d + 32 <= sz ==>
  (j IN range_bytes (step_writes ti t postt) <=>
   ?k. d <= k /\ k < d + 32 /\ k < sz /\ j = pos + k /\
     srcbase + k IN range_bytes (step_writes si s post))
Proof
  strip_tac >>
  `!i. i IN range_bytes (step_writes si s post) <=>
       w2n x <= i /\ i < w2n x + 32` by
    metis_tac[ptr_mstore_footprint_interval] >>
  `!i. i IN range_bytes (step_writes ti t postt) <=>
       w2n y <= i /\ i < w2n y + 32` by
    metis_tac[ptr_mstore_footprint_interval] >>
  simp[] >> eq_tac >- (strip_tac >> qexists_tac `j - pos` >> decide_tac) >>
  rpt strip_tac >> decide_tac
QED

Theorem ptr_mstore_owned_relocation:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME x /\ eval_operand ta t = SOME y /\
  eval_operand sv s = SOME v /\ eval_operand tv t = SOME vt /\
  ptr_ledger_owned_site registry births token aid srcbase sz pos /\
  w2n x = srcbase + d /\ w2n y = pos + d /\ d + 32 <= sz /\
  i IN range_bytes (step_writes si s post) ==>
  srcbase <= i /\ i < srcbase + sz /\
  w2n y + (i - w2n x) = pos + (i - srcbase)
Proof
  strip_tac >>
  `w2n x <= i /\ i < w2n x + 32` by
    metis_tac[ptr_mstore_footprint_interval] >>
  decide_tac
QED

Theorem ptr_mstore_same_owner_exclusion:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME x /\ eval_operand ta t = SOME y /\
  eval_operand sv s = SOME v /\ eval_operand tv t = SOME vt /\
  ptr_ledger_owned_site registry births token aid srcbase sz pos /\
  w2n x = srcbase + d /\ w2n y = pos + d /\ d + 32 <= sz /\
  k < sz /\ srcbase + k NOTIN range_bytes (step_writes si s post) ==>
  pos + k NOTIN range_bytes (step_writes ti t postt)
Proof
  strip_tac >>
  drule_all ptr_mstore_owned_footprint >>
  disch_then (qspecl_then [`postt`,`post`,`pos + k`] mp_tac) >>
  gvs[ADD_COMM]
QED

Theorem ptr_mstore_fixed_footprint:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME x /\ eval_operand ta t = SOME y /\
  eval_operand sv s = SOME v /\ eval_operand tv t = SOME vt /\
  w2n x = w2n y /\ w2n x + 32 <= lo ==>
  (j IN range_bytes (step_writes ti t postt) <=>
   j IN range_bytes (step_writes si s post)) /\
  (j IN range_bytes (step_writes ti t postt) ==> j < lo)
Proof
  strip_tac >>
  `j IN range_bytes (step_writes si s post) <=>
       w2n x <= j /\ j < w2n x + 32` by
    metis_tac[ptr_mstore_footprint_interval] >>
  `j IN range_bytes (step_writes ti t postt) <=>
       w2n y <= j /\ j < w2n y + 32` by
    metis_tac[ptr_mstore_footprint_interval] >>
  simp[] >> decide_tac
QED

Theorem ptr_copy_footprint_interval:
  MEM ti.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
  ti.inst_operands = [dst;src;cnt] /\
  eval_operand dst ts = SOME y /\ eval_operand src ts = SOME z /\
  eval_operand cnt ts = SOME n ==>
  (i IN range_bytes (step_writes ti ts post) <=> w2n y <= i /\ i < w2n y + w2n n)
Proof
  simp[MEM] >> strip_tac >>
  simp[step_writes_def, source_memory_write_ranges_def,
    sized_source_write_range_def, range_bytes_def]
QED
