(* CODECOPY source classification and relocated emitted execution. *)
Theory symEmitCodecopyOwn
Ancestors symEmitSim codegenSymOwnRel

Theorem codecopy_source_flow_mode:
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; sz] ==>
  (src = Label "runtime_begin" \/ (?x. src = Var x /\ code_end_var fn x) \/
   (allow_own /\ ~is_label_operand src /\
    !x. src = Var x ==> ~code_end_var fn x /\ ~retpc_var fn x)) /\
  (!x. dst = Var x \/ sz = Var x ==> ~code_end_var fn x)
Proof
  Cases_on `allow_own` >>
  simp[codegenSymOwnRelTheory.label_flow_own_ok_def, label_flow_ok_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[MEM] >> metis_tac[]
QED

Theorem codecopy_source_numeric_kind_mode:
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; sz] /\ label_positions_ok inst /\
  (op = dst \/ op = sz) ==>
  (op_kind_ok fn ret op sv <=> ?w. sv = Val w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all codecopy_source_flow_mode >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  match_mp_tac op_kind_ok_numeric >> conj_tac
  >- (Cases_on `src` >>
      gvs[unitShapeDefsTheory.label_positions_ok_def, MEM,
          stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]) >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule frameViewFactsTheory.ordinary_operand_not_retpc >> simp[] >>
      qexists `inst` >> fs[MEM] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem codecopy_source_kind_mode:
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; sz] /\
  retpc_shape_ok fn /\ op_kind_ok fn ret src sv ==>
  (?d. sv = Lab "code_end" d) \/ sv = Lab "runtime_begin" 0 \/
  (allow_own /\ ?w. sv = Val w)
Proof
  strip_tac >> drule_all codecopy_source_flow_mode >> strip_tac >>
  gvs[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def,
      stackPlanTypesTheory.is_label_operand_def, AllCaseEqs()] >>
  gvs[code_end_var_not_retpc_var, AllCaseEqs()] >>
  Cases_on `src` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem sym_codecopy_prepared_layout_mode:
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; sz] /\ label_positions_ok inst /\
  retpc_shape_ok fn /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ [sz; src; dst] ==>
  ?dw sw nw tail. ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
    ((?d. sw = Lab "code_end" d) \/ sw = Lab "runtime_begin" 0 \/
     (allow_own /\ ?w. sw = Val w))
Proof
  strip_tac >>
  `!sv. (op_kind_ok fn ret dst sv <=> ?w. sv = Val w) /\
        (op_kind_ok fn ret sz sv <=> ?w. sv = Val w)` by
    (gen_tac >> conj_tac >> irule codecopy_source_numeric_kind_mode >> metis_tac[]) >>
  gvs[sym_kinds_ok_def, REVERSE_APPEND, LIST_REL_SPLIT1, LIST_REL_CONS1] >>
  drule_all codecopy_source_kind_mode >> metis_tac[]
QED

Theorem asm_sym_codecopy_values_core:
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
  eval_operands [dst; src; sz] vs = SOME (TAKE 3 cs.as_stack) ==>
  eval_operand dst vs = SOME dw /\ eval_operand sz vs = SOME nw /\
  IS_SOME (eval_operand src vs)
Proof
  strip_tac >>
  gvs[LIST_REL_CONS1, asmSymBridgeTheory.sval_conc_def,
      venomStateTheory.eval_operands_def, AllCaseEqs()]
QED
