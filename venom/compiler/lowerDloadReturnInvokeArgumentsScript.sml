(* Correlated internal INVOKE arguments; pointer arguments need not be equal. *)
Theory lowerDloadReturnInvokeArguments
Ancestors
  lowerDloadSafetyArguments lowerDloadSafetyValues unitShapeDefs
  ptrDiscipline venomExecSemantics venomState venomInst finite_map list

Theorem ld_invoke_argument_admissible:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) ==>
  !arg. MEM arg ops ==>
    (!v. arg = Var v ==> ~retpc_var fn v) /\ op_taint tn arg = {}
Proof
  strip_tac >>
  `inst.inst_operands = Label nm :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  qx_gen_tac `arg` >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `retpc_use_ok inst v` by
        (irule opaque_use_ok_retpc_use >> metis_tac[MEM]) >>
      gvs[retpc_use_ok_def]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  simp[taint_ok_def] >> metis_tac[MEM]
QED

(* General list-domain boundary, independent of INVOKE and scalar equality. *)
Theorem ld_vars_operands_defined:
  !ops argsT.
    ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
    (!arg v. MEM arg ops /\ arg = Var v ==> MEM v (fn_ir_vars f.lf_fn)) /\
    eval_operands ops f.lf_tgt = SOME argsT ==>
    ?argsS. eval_operands ops f.lf_src = SOME argsS
Proof
  Induct_on `ops` >- simp[eval_operands_def] >>
  rpt gen_tac >> simp[eval_operands_def, AllCaseEqs()] >> strip_tac >>
  `?x. eval_operand h f.lf_src = SOME x` by
    (drule ld_vars_operand_defined >>
     disch_then (qspec_then `h` mp_tac) >> simp[] >>
     Cases_on `eval_operand h f.lf_src` >> simp[]) >>
  `?xs. eval_operands ops f.lf_src = SOME xs` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  simp[eval_operands_def] >> metis_tac[]
QED

Theorem ld_invoke_arguments_related:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_tv = tn.t_var /\ opaque_use_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  eval_operands ops f.lf_tgt = SOME argsT ==>
  ?argsS. eval_operands ops f.lf_src = SOME argsS /\
    LENGTH argsS = LENGTH ops /\ LENGTH argsT = LENGTH ops /\
    (!j. j < LENGTH argsS ==>
      ld_wordrel A (EL j (MAP (op_prov f.lf_H) ops))
        (EL j argsS) (EL j argsT))
Proof
  strip_tac >>
  `!arg. MEM arg ops ==>
    (!v. arg = Var v ==> ~retpc_var f.lf_fn v) /\ op_taint tn arg = {}` by
    (metis_tac[ld_invoke_argument_admissible]) >>
  `inst.inst_operands = Label nm :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `?argsS. eval_operands ops f.lf_src = SOME argsS` by
    (irule ld_vars_operands_defined >>
     simp[] >> metis_tac[ld_inst_input_ir, MEM]) >>
  qexists_tac `argsS` >> simp[] >>
  irule ld_vars_arguments >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[op_taint_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Permission, identity liveness and erased provenance remain the existing
   ld_arguments_permission, ld_arguments_live and ld_arguments_erasure;
   these are not reproved as INVOKE-specific duplicates. *)
val _ = List.app (fn th => if null (hyp th) then ()
          else raise Fail "invoke argument boundary has kernel hypotheses")
  [ld_invoke_argument_admissible, ld_vars_operands_defined,
   ld_invoke_arguments_related];
