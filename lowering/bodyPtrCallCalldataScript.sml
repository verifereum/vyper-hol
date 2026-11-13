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
 *   msg_data_to_memory_dalloca, compile_raw_call_calldata_dalloca -- the
 *     DALLOCA is emitted, between two cs_extends steps
 *   compile_expr_raw_call_calldata_dalloca,
 *   lower_value_raw_call_calldata_dalloca -- so the function has it
 *   stmt_state_rel_no_dalloca -- and ~ctx_has_dalloca says it doesn't
 *)
Theory bodyPtrCallCalldata
Ancestors
  bodyPtrDefs exprSimSend exprSimHypsDefs exprLoweringProps fragExec
  compileEnv exprLowering builtinSystem context ptrDiscipline venomInst
  stmtLoweringMono vyperTypeSystem vyperAST list rich_list pair

(* compile_msg_data_to_memory emits its DALLOCA at some sm in between. *)
Theorem msg_data_to_memory_dalloca:
  !st r st'.
    compile_msg_data_to_memory st = (r, st') ==>
    ?sm i. cs_extends st sm /\ cs_extends sm st' /\
           MEM i sm.cs_current_insts /\ i.inst_opcode = DALLOCA
Proof
  rpt gen_tac >>
  simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_op CALLDATASIZE [] st` >> simp[] >>
  rename1 `emit_op CALLDATASIZE [] st = (len, s1)` >>
  Cases_on `emit_op DALLOCA [len] s1` >> simp[] >>
  rename1 `emit_op DALLOCA [len] s1 = (dp, s2)` >>
  Cases_on `emit_void CALLDATACOPY [dp; Lit 0w; len] s2` >> simp[] >>
  rename1 `emit_void _ _ s2 = (u, s3)` >> strip_tac >> gvs[] >>
  qexists_tac `s2` >>
  `ci_mono st s1` by
    (qspecl_then [`CALLDATASIZE`, `[]`, `st`] mp_tac ci_mono_emit_op >>
     simp[]) >>
  `ci_mono s1 s2` by
    (qspecl_then [`DALLOCA`, `[len]`, `s1`] mp_tac ci_mono_emit_op >>
     simp[]) >>
  `ci_mono s2 s3` by
    (qspecl_then [`CALLDATACOPY`, `[dp; Lit 0w; len]`, `s2`] mp_tac
       ci_mono_emit_void >> simp[]) >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  gvs[ci_mono_def] >>
  qexists_tac `mk_inst s1.cs_next_id DALLOCA [len]
                 [STRING #"%" (toString s1.cs_next_var)]` >>
  simp[mk_inst_def] >>
  irule cs_extends_trans >> qexists_tac `s1` >> simp[]
QED

(* Reads a ci_mono fact about SND of a step off the step's equation. *)
Theorem ci_mono_eq[local]:
  !p x sb sa. p = (x, sb) ==> ci_mono sa (SND p) ==> ci_mono sa sb
Proof
  rw[] >> gvs[]
QED

(* The raw_call of msg.data emits its DALLOCA at some sm in between. *)
Theorem compile_raw_call_calldata_dalloca:
  !cenv ann ty rcf addr_e kw_es dflt sa vv sb.
    compile_call compile_expr cenv ann ty (RawCallCalldataTarget rcf)
      (addr_e :: kw_es) dflt sa = (vv, sb) ==>
    ?sm i. cs_extends sa sm /\ cs_extends sm sb /\
           MEM i sm.cs_current_insts /\ i.inst_opcode = DALLOCA
Proof
  rpt gen_tac >>
  `!ks es st. ci_mono st
     (SND (compile_ext_call_kwargs compile_expr cenv NoneT ks es st))` by
    (Induct >> Cases_on `es` >> rpt strip_tac >>
     simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
     ho_match_mp_tac ci_mono_bind >> conj_tac
     >- (rpt strip_tac >> irule ci_mono_compile_ext_call_kwarg >>
         simp[cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa]) >>
     rpt strip_tac >> simp[UNCURRY] >>
     ho_match_mp_tac ci_mono_bind >> simp[UNCURRY, ci_mono_comp_return]) >>
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `sb = st7` by (Cases_on `rcf.rcf_max_outsize = 0` >> gvs[]) >>
  drule msg_data_to_memory_dalloca >> strip_tac >>
  qexists_tac `sm` >> qexists_tac `i` >> simp[] >>
  `ci_mono sa st1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` (irule o
       MATCH_MP ci_mono_eq) >>
     irule ci_mono_lower_value_cfn >>
     simp[cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa]) >>
  `ci_mono st1 st2` by
    (qpat_x_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` (irule o
       MATCH_MP ci_mono_eq) >> simp[]) >>
  `ci_mono st2 st3` by
    (Cases_on `gas_opt` >> gvs[ci_mono_refl] >>
     qpat_x_assum `emit_op GAS _ _ = _` (irule o
       MATCH_MP ci_mono_eq) >> simp[ci_mono_emit_op]) >>
  `ci_mono st3 st4` by
    (qpat_x_assum `compile_raw_call_outbuf _ _ = _` (irule o
       MATCH_MP ci_mono_eq) >> simp[ci_mono_compile_raw_call_outbuf]) >>
  `ci_mono st5 st6` by
    (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`
       (irule o MATCH_MP ci_mono_eq) >>
     simp[ci_mono_compile_raw_call_finish]) >>
  `ci_mono st6 st7` by
    (qpat_x_assum `emit_void SETFMP _ _ = _` (irule o
       MATCH_MP ci_mono_eq) >> simp[ci_mono_emit_void]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

(* An instruction of the current block at sm, for sa <= sm <= sb, lies in
   the function holding the code from sa to sb. *)
Theorem fn_has_code_current_inst:
  !sa sm sb func i.
    cs_extends sa sm /\ cs_extends sm sb /\ fn_has_code sa sb func /\
    MEM i sm.cs_current_insts ==> MEM i (fn_insts func)
Proof
  rpt strip_tac >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  qspecl_then [`sm`, `sb`, `func`] mp_tac fn_has_code_start >>
  simp[] >> strip_tac >>
  irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`, `sm.cs_current_bb`] >> simp[] >>
  metis_tac[IS_PREFIX_MEM]
QED

(* The function holding a raw_call of msg.data has a DALLOCA. *)
Theorem compile_expr_raw_call_calldata_dalloca:
  !cenv ty ann rcf args dflt sa vv sb func.
    compile_expr cenv ty (Call ann (RawCallCalldataTarget rcf) args dflt) sa =
      (vv, sb) /\ args <> [] /\ fn_has_code sa sb func ==>
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)
Proof
  rpt strip_tac >> Cases_on `args` >> gvs[compile_expr_call] >>
  drule compile_raw_call_calldata_dalloca >> strip_tac >>
  simp[EXISTS_MEM] >> qexists_tac `i` >> simp[] >>
  irule fn_has_code_current_inst >> qexistsl_tac [`sa`, `sb`, `sm`] >>
  simp[]
QED

(* lower_value runs compile_expr first. *)
Theorem lower_value_compile_expr_split:
  !cenv ty e sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) ==>
    ?vv sm. compile_expr cenv ty e sa = (vv, sm) /\
            cs_extends sa sm /\ cs_extends sm sb
Proof
  rpt gen_tac >> simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> simp[] >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> simp[] >> strip_tac >>
  qspecl_then [`cenv`, `q`, `r`] mp_tac ci_mono_unwrap_value >>
  gvs[ci_mono_def]
QED

(* A function stmt_state_rel runs is one of ctx's. *)
Theorem stmt_state_rel_dalloca:
  !ctx func cenv cx vs ss.
    stmt_state_rel ctx func cenv cx vs ss /\
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
