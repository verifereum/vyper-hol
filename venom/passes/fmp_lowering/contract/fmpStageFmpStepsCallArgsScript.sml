(* Argument transport for the FMP stage's internal calls. *)
Theory fmpStageFmpStepsCallArgs
Ancestors
  fmpStageOpBase fmpStageRel unitShapeDefs
  venomExecSemantics venomState venomInst ptrDiscipline o1PassContract list

Theorem eval_operands_transport[local]:
  !ops xs.
    eval_operands ops s = SOME xs /\
    (!op x. MEM op ops /\ eval_operand op s = SOME x ==>
       ?y. eval_operand op t = SOME y /\ R op x y) ==>
    ?ys. eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH xs /\
      LENGTH xs = LENGTH ops /\
      (!k. k < LENGTH xs ==> R (EL k ops) (EL k xs) (EL k ys))
Proof
  Induct_on `ops` >- simp[eval_operands_def] >>
  rpt gen_tac >> simp[eval_operands_def, AllCaseEqs()] >> strip_tac >>
  rename1 `eval_operand h s = SOME x` >>
  `?y. eval_operand h t = SOME y /\ R h x y` by metis_tac[MEM] >>
  first_x_assum (qspec_then `vs` mp_tac) >>
  impl_tac >- metis_tac[MEM] >>
  strip_tac >> qexists_tac `y::ys` >>
  gvs[eval_operands_def] >>
  Cases >> simp[]
QED

Theorem fmp_stage_invoke_arguments:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  eval_operands ops s = SOME args /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  ?ys. eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH args /\
    LENGTH args = LENGTH ops /\
    (!k. k < LENGTH args ==>
      fmp_value_rel sm (EL k (MAP (op_prov G) ops)) {}
        (EL k args) (EL k ys))
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `opaque_use_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `inst.inst_operands = Label nm :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `!arg. MEM arg ops ==>
     (!v. arg = Var v ==> ~retpc_var fn v) /\ op_taint tn arg = {}` by
    (rpt strip_tac
     >- (spose_not_then assume_tac >>
         `retpc_use_ok inst v` by metis_tac[opaque_use_ok_retpc_use, MEM] >>
         gvs[retpc_use_ok_def]) >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> metis_tac[MEM]) >>
  drule eval_operands_transport >>
  disch_then (qspecl_then [`t`, `\op x y. fmp_value_rel sm (op_prov G op) {} x y`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      `inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
       (!v. op = Var v ==> ~retpc_var fn v) /\ op_taint tn op = {}` by
        (simp[] >> metis_tac[MEM]) >>
      drule_all fmp_stage_operand >> simp[]) >>
  strip_tac >> qexists_tac `ys` >> gvs[EL_MAP]
QED

Theorem fmp_params_rel_append:
  s.vs_params = xs /\ t.vs_params = ys ++ extra /\
  LENGTH PG = LENGTH xs /\ LENGTH ys = LENGTH xs /\
  (!k. k < LENGTH xs ==>
    fmp_value_rel sm (EL k PG) {} (EL k xs) (EL k ys)) ==>
  fmp_params_rel sm PG s t
Proof
  simp[fmp_params_rel_def] >> rpt strip_tac >> simp[EL_APPEND_EQN]
QED
