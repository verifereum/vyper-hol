(* Native visits in the administrative materialization of a selected IfExp arm. *)
Theory entryCreateIfExpArmVisit
Ancestors
  entryIntCallStageBuffer entryCreateFocusSpec entryCreatePathScope
  exprSimAbiEncodeObliviousCode createSizeCutCode createSizeCutRegion
  exprLowering compileEnv bodySim fragExec venomInst venomRunBounded list pair

Triviality ifexp_arm_admin_action:
  code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
    (compile_ifexp_arm ce rt aty vv)
Proof
  simp[compile_ifexp_arm_def] >> IF_CASES_TAC >>
  simp[code_action_bind, code_action_ignore_bind, code_action_return,
       code_action_alloc_buffer, buffer_unwrap_action, buffer_store_action]
QED

Triviality ifexp_arm_admin_code:
  compile_ifexp_arm ce rt aty vv a = (op,b) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)
Proof
  strip_tac >> drule (REWRITE_RULE [code_action_def] ifexp_arm_admin_action) >>
  simp[code_step_def]
QED

Theorem ifexp_materialization_visit_disjoint:
  compile_ifexp_arm ce rt aty vv a = (op,b) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  create_interior_visit a b E C f (p,d,k) s (before,hit,after) ==>
  ?d' u inst. hit = ((p,d',inst.inst_id),f,inst,u) /\
              ~MEM inst.inst_opcode [INVOKE; CREATE; CREATE2]
Proof
  strip_tac >> drule ifexp_arm_admin_code >> strip_tac >>
  drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region a b s` by
    (fs[create_interior_visit_def, create_operand_at_def] >> metis_tac[]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region a b u` by metis_tac[create_expr_prefix_cut_region] >>
  `MEM inst (frag_code a b)` by
    (fs[create_operand_fetch_def, create_operand_at_def] >> metis_tac[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ifexp_materialization_visit_size_ok:
  compile_ifexp_arm ce rt aty vv a = (op,b) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  create_interior_visit a b E C f (p,d,k) s (before,hit,after) ==>
  case hit of (_,_,inst,t) => inst_create_size_ok inst t
Proof
  strip_tac >> drule_all ifexp_materialization_visit_disjoint >>
  strip_tac >> fs[inst_create_size_ok_def]
QED
