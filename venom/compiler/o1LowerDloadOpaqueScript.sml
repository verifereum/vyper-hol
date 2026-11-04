(* Opaque return-PC boundaries for LowerDload relocation.
   These are syntactic exclusions, not a frame simulation. *)
Theory o1LowerDloadOpaque
Ancestors
  unitShapeDefs venomExecSemantics venomState list rich_list

Theorem non_retpc_assign_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\
  ~retpc_var fn x ==> ~retpc_var fn y
Proof
  rw[retpc_var_def] >>
  metis_tac[copy_phi_var_assign]
QED

Theorem non_retpc_phi_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  MEM (Var y) i.inst_operands /\ MEM x i.inst_outputs /\
  ~retpc_var fn x ==> ~retpc_var fn y
Proof
  rw[retpc_var_def] >>
  metis_tac[copy_phi_var_phi]
QED

Theorem ret_front_non_retpc:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RET /\ i.inst_operands <> [] /\
  MEM (Var v) (FRONT i.inst_operands) ==> ~retpc_var fn v
Proof
  rpt strip_tac >>
  `MEM (Var v) i.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  gvs[FRONT_APPEND_NOT_NIL]
QED

(* Definedness transfer deliberately permits differing operand values. *)
Theorem eval_operands_defined_iff:
  !ops s t.
    (!op. MEM op ops ==>
      (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) ==>
    (IS_SOME (eval_operands ops s) <=> IS_SOME (eval_operands ops t))
Proof
  Induct >> simp[eval_operands_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >>
  `IS_SOME (eval_operands ops s) <=> IS_SOME (eval_operands ops t)` by
    (first_x_assum irule >> simp[]) >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >> gvs[] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >>
  gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem eval_operands_front_agree:
  !ops s t xs.
    ops <> [] /\
    (!op. MEM op ops ==>
      (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) /\
    (!op. MEM op (FRONT ops) ==> eval_operand op s = eval_operand op t) /\
    eval_operands ops s = SOME xs ==>
    ?ys. eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH xs /\
         FRONT ys = FRONT xs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ops`
  >- (gvs[eval_operands_def, AllCaseEqs()] >>
      Cases_on `eval_operand h t` >> gvs[] >> qexists_tac `[x]` >> simp[]) >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`s`, `t`, `v'::vs'`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `v::ys` >> gvs[eval_operands_def]
QED

(* Conditional RET boundary: availability includes the opaque final token,
   while value agreement is required only for the ordinary operands. *)
Theorem ret_front_transfer:
  i.inst_opcode = RET /\
  (!op. MEM op i.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) /\
  (!op. MEM op (FRONT i.inst_operands) ==>
    eval_operand op s = eval_operand op t) /\
  step_inst_base i s = IntRet ir s' ==>
  ?jr. step_inst_base i t = IntRet jr t /\
       jr.iret_values = ir.iret_values /\
       ir.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE /\ s' = s
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base i s = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operands i.inst_operands s` >> simp[] >>
  rename1 `eval_operands i.inst_operands s = SOME xs` >>
  Cases_on `xs` >> simp[] >> strip_tac >> gvs[] >>
  `i.inst_operands <> []` by
    (strip_tac >> gvs[eval_operands_def]) >>
  drule_all eval_operands_front_agree >> strip_tac >>
  Cases_on `ys` >> gvs[] >>
  simp[step_inst_base_def] >>
  qexists_tac `<| iret_values := FRONT (h'::t'); iret_adopt_fmp := NONE |>` >>
  simp[]
QED
