(*
 * raw_call of msg.data under the pointer judgments: the case holds
 * vacuously.  Its lowering copies msg.data to memory through a DALLOCA
 * (compile_msg_data_to_memory), which lands in the function the judgments
 * run, and stmt_state_rel's alloca_room makes that function one of ctx's,
 * so ctx_has_dalloca ctx, which the judgments exclude.
 *
 * TOP-LEVEL:
 *   raw_call_calldata_ptr_vacuous -- expr_sim_ptr and expr_vv_sim_ptr of
 *     a well-typed raw_call of msg.data
 *
 * Helpers:
 *   stmt_state_rel_dalloca -- the function stmt_state_rel runs is ctx's;
 *     rawCallCalldataDalloca shows the lowering puts a DALLOCA in it
 *)
Theory bodyPtrCallCalldata
Ancestors
  rawCallCalldataDalloca bodyPtrDefs exprSimSend exprSimHypsDefs exprLoweringProps fragExec
  compileEnv exprLowering builtinSystem context ptrDiscipline venomInst
  stmtLoweringMono vyperTypeSystem vyperAST list rich_list pair

(* A function stmt_state_rel runs is one of ctx's. *)
Theorem stmt_state_rel_dalloca:
  !ctx func cenv cx vs ss.
    stmt_state_rel H ctx func cenv cx vs ss /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) ==>
    ctx_has_dalloca ctx
Proof
  rw[stmt_state_rel_def, alloca_room_def] >>
  drule lookup_function_MEM >> rw[ctx_has_dalloca_def, EXISTS_MEM] >>
  qexists_tac `func` >> fs[EXISTS_MEM] >> metis_tac[]
QED

Theorem raw_call_calldata_ptr_vacuous:
  !d ctx PG func cenv cx ty env ann rcf args dflt es.
    well_typed_expr env (Call ann (RawCallCalldataTarget rcf) args dflt) ==>
    expr_sim_ptr d ctx PG func cenv cx ty
      (Call ann (RawCallCalldataTarget rcf) args dflt) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Call ann (RawCallCalldataTarget rcf) args dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  `args <> []` by (strip_tac >> gvs[well_typed_expr_def]) >>
  rw[expr_sim_ptr_def, expr_vv_sim_ptr_def] >>
  `ctx_has_dalloca ctx` suffices_by simp[] >>
  irule stmt_state_rel_dalloca >> first_assum (irule_at Any)
  >- (drule lower_value_compile_expr_split >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
  drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
QED
