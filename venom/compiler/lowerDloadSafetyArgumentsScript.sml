(* Value-only call argument boundary; no execution or stack claims. *)
Theory lowerDloadSafetyArguments
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline venomExecSemantics venomState finite_map list pred_set

Theorem ld_vars_operand_wordrel:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  eval_operand op f.lf_src = SOME x /\
  eval_operand op f.lf_tgt = SOME y /\
  (!v. op = Var v ==> ~retpc_var f.lf_fn v) /\
  (op_prov f.lf_H op = NONE ==>
    !v. op = Var v ==>
      (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}) ==>
  ld_wordrel A (op_prov f.lf_H op) x y
Proof
  Cases_on `op_prov f.lf_H op`
  >- (simp[ld_wordrel_def] >> strip_tac >>
      irule ld_vars_operand_scalar >> metis_tac[]) >>
  strip_tac >> drule_all ld_vars_operand_selected >> simp[]
QED

Theorem ld_arguments_erasure:
  MAP (OPTION_MAP (ld_erase A)) (MAP (op_prov H) args) =
  MAP (op_prov (ld_erase A o_f H)) args
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[ld_erase_op_prov]
QED

Theorem ld_vars_arguments:
  !args xs ys.
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  eval_operands args f.lf_src = SOME xs /\
  eval_operands args f.lf_tgt = SOME ys /\
  (!op. MEM op args ==>
    (!v. op = Var v ==> ~retpc_var f.lf_fn v) /\
    (op_prov f.lf_H op = NONE ==>
      !v. op = Var v ==>
        (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {})) ==>
  LENGTH xs = LENGTH args /\ LENGTH ys = LENGTH args /\
  !j. j < LENGTH xs ==>
    ld_wordrel A (EL j (MAP (op_prov f.lf_H) args)) (EL j xs) (EL j ys)
Proof
  Induct_on `args` >> rpt gen_tac >>
  simp[eval_operands_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `!op. MEM op args ==>
    (!v. op = Var v ==> ~retpc_var f.lf_fn v) /\
    (op_prov f.lf_H op = NONE ==> !v. op = Var v ==>
      (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {})` by
    (simp[AllCaseEqs()] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> simp[] >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j` >> simp[]
  >- (irule ld_vars_operand_wordrel >> simp[AllCaseEqs()] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem ld_arguments_live:
  (!v a. FLOOKUP H v = SOME a ==> a IN FDOM A) /\
  MEM (SOME a) (MAP (op_prov H) args) ==>
  a IN FDOM A
Proof
  simp[MEM_MAP] >> strip_tac >> Cases_on `y` >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem ld_arguments_permission:
  ld_vars P A f /\ ptr_use_ok P (fn_pv P f.lf_fn) inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  k < LENGTH args /\ EL k (MAP (op_prov f.lf_H) args) = SOME a ==>
  k IN P nm
Proof
  strip_tac >>
  `op_prov f.lf_H (EL k args) = SOME a` by gvs[EL_MAP] >>
  Cases_on `EL k args` >> gvs[op_prov_def] >>
  `s IN fn_pv P f.lf_fn` by
    (gvs[ld_vars_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_ok_def] >> metis_tac[]
QED
