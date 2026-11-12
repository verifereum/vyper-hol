Theory o1LabelFlowMiddleOperandOwners
Ancestors
  o1MakeSsaOwnership o1MakeSsaPrefixNames makeSsaDefs list alist pair

Theorem current_fixed_owner_latest:
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  v IN V ==> (latest_current_name rs v,v) IN H
Proof
  PairCases_on `rs` >> simp[latest_current_name_def] >> strip_tac >>
  Cases_on `ALOOKUP rs1 v`
  >- (simp[] >> metis_tac[current_name_owner_identity]) >>
  rename1 `ALOOKUP rs1 v = SOME ns` >> Cases_on `ns` >> simp[]
  >- metis_tac[current_name_owner_identity] >>
  drule_all current_stack_owner_lookup >> simp[]
QED

Theorem current_fixed_owner_push:
  push_current_name s rs v = (rt,t,n) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  (n,v) IN H ==> current_stack_owner V H (SND rt)
Proof
  PairCases_on `rs` >> simp[push_current_name_def] >>
  Cases_on `ALOOKUP rs0 v` >> simp[] >>
  TRY (rename1 `ALOOKUP rs0 v = SOME k` >> Cases_on `k = 0` >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  irule current_stack_owner_push >>
  gvs[current_name_owner_def] >> metis_tac[]
QED

Theorem current_fixed_owner_outputs:
  !vs s rs rt t ns.
  rename_current_outputs s rs vs = (rt,t,ns) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  LIST_REL (\v n. (n,v) IN H) vs ns ==>
  current_stack_owner V H (SND rt)
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[current_fixed_owner_push]
QED

Theorem current_fixed_owner_inst:
  rename_current_inst s rs i = (rt,t,j) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  LIST_REL (\v n. (n,v) IN H) i.inst_outputs j.inst_outputs ==>
  current_stack_owner V H (SND rt)
Proof
  simp[rename_current_inst_def] >>
  Cases_on `i.inst_opcode = PHI` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[current_fixed_owner_outputs]
QED

Theorem current_fixed_owner_block:
  !xs s rs rt t ys.
  rename_current_block_insts s rs xs = (rt,t,ys) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
    i.inst_outputs j.inst_outputs) xs ys ==>
  current_stack_owner V H (SND rt)
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[current_fixed_owner_inst]
QED

Theorem current_fixed_owner_operand:
  rename_current_inst s rs i = (rt,t,j) /\ i.inst_opcode <> PHI /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  k < LENGTH i.inst_operands /\ EL k i.inst_operands = Var v /\ v IN V ==>
  ?n. EL k j.inst_operands = Var n /\ (n,v) IN H
Proof
  strip_tac >>
  qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
  simp[rename_current_inst_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qexists `latest_current_name rs v` >> conj_tac
  >- metis_tac[o1MakeSsaPrefixNamesTheory.current_operand_var_at] >>
  metis_tac[current_fixed_owner_latest]
QED

Theorem current_fixed_owner_block_operand:
  !xs s rs rt t ys k j v.
  rename_current_block_insts s rs xs = (rt,t,ys) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
    i.inst_outputs j.inst_outputs) xs ys /\
  k < LENGTH xs /\ (EL k xs).inst_opcode <> PHI /\
  j < LENGTH (EL k xs).inst_operands /\
  EL j (EL k xs).inst_operands = Var v /\ v IN V ==>
  ?n. EL j (EL k ys).inst_operands = Var n /\ (n,v) IN H
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[]
  >- metis_tac[current_fixed_owner_operand] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[current_fixed_owner_inst]
QED

Theorem current_rename_operands_nonvar:
  !ops k op. k < LENGTH ops /\ EL k ops = op /\
    (!v. op <> Var v) ==>
    EL k (rename_current_operands rs ops) = op
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `k` >> simp[] >>
  Cases_on `h` >> simp[rename_current_operands_def]
QED

Theorem current_rename_inst_nonvar:
  rename_current_inst s rs i = (rt,t,j) /\ i.inst_opcode <> PHI /\
  k < LENGTH i.inst_operands /\ EL k i.inst_operands = op /\
  (!v. op <> Var v) ==> EL k j.inst_operands = op
Proof
  strip_tac >>
  qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
  simp[rename_current_inst_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[current_rename_operands_nonvar]
QED

Theorem current_rename_block_nonvar:
  !xs s rs rt t ys k j op.
  rename_current_block_insts s rs xs = (rt,t,ys) /\
  k < LENGTH xs /\ (EL k xs).inst_opcode <> PHI /\
  j < LENGTH (EL k xs).inst_operands /\
  EL j (EL k xs).inst_operands = op /\ (!v. op <> Var v) ==>
  EL j (EL k ys).inst_operands = op
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[] >> metis_tac[current_rename_inst_nonvar]
QED
