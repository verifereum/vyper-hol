(* Compiler boundary for the resource-carrying struct field traversal. *)
Theory bodyIntCallFamAggStructFields
Ancestors
  bodyIntCallJointAggCore exprLowering compileEnv state_transformer
  exprSimWordArgs exprSimHypsDefs gasOutcome gasSummary fragGasMode
  vyperInterpreter vyperState

Theorem compile_struct_lit_cons_inv:
  ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case ty of StructT n => nsid_to_string n | _ => "")) name = SOME (fty,sz) /\
  compile_struct_lit cfn ce ty ((name,e)::fields) buf off sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    cfn ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst fty (lowered_value_type ce e) su = ((),st) /\
    compile_struct_lit cfn ce ty fields buf (off+sz) st = (out,sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_struct_lit _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_struct_lit_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,st)` >>
  Cases_on `u` >> simp[] >> metis_tac[]
QED

(* Only the source gas-observation queue is normalized at a counted endpoint. *)
Theorem intcall_joint_res_gas_obs[simp]:
  intcall_joint_res fp ce env (es with gas_obs := gs) sa s <=>
  intcall_joint_res fp ce env es sa s
Proof
  simp[bodyIntCallJointContractTheory.intcall_joint_res_def]
QED

Theorem intcall_expr_cont_end_gas_obs[simp]:
  intcall_expr_cont fp ce env es sa s (ee with gas_obs := gs) sb u <=>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[bodyIntCallJointContractTheory.intcall_expr_cont_def]
QED

Theorem intcall_struct_fields_nil:
  intcall_expr_cont fp ce env es0 sa0 s0 es sa s ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx []) (es,s)
    (\res ee u. res = INL [] /\ u = s /\
      ee = es with gas_obs := [] /\
      intcall_expr_cont fp ce env es0 sa0 s0 ee sa u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `~s.vs_halted` by fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, Once evaluate_def, return_def,
       gas_marked_path_def, fragGasPathTheory.gas_path_rules,
       bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  gvs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >> gvs[]
QED

(* Pure source result maps do not change the counted target segment. *)
Theorem gas_marked_exec_return_map:
  gas_marked_exec memory (ctx,func) source (es,s) marks rr mid r ==>
  gas_marked_exec memory (ctx,func)
    (bind source (\v. return (f v))) (es,s) marks
    (case rr of INL v => INL (f v) | INR ex => INR ex) mid r
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  simp[] >> gen_tac >> simp[bind_def] >> Cases_on `rr` >> simp[return_def]
QED

Theorem gas_outcome_return_map:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!rr ee t. Q rr ee t ==>
    Q' (case rr of INL v => INL (f v) | INR ex => INR ex) ee t) /\
  (!rr ee r. R rr ee r ==>
    R' (case rr of INL v => INL (f v) | INR ex => INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind source (\v. return (f v))) (es,s) Q' R'
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >> metis_tac[]
QED
