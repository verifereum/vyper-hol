(* Slice source lengths are scalar reads, including the external-code case. *)
Theory bodyFullBuiltinBytestringQuery
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice bodyFullUnwrapRun
  fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport instMemFrontier
  memSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  freshWrites fragExec fragExecMem bodyPtrDefs allocaHistory list finite_map

Theorem bytestring_source_size_full_run:
  emit_op opc ops sa = (limit,sb) /\ fn_has_code sa sb func /\
  MEM opc [CALLDATASIZE;CODESIZE;EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) wl s) /\
  allocas_from lo s /\ alloca_inv s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'.
    limit = Var out /\ not_fresh_at sb out /\
    t = update_var out wl s with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var out t = SOME wl /\
    op_prov G' limit = NONE /\ op_taint tn' limit = {} /\
    G' = DRESTRICT G (COMPL {out}) /\
    tn' = tn with t_var := tn.t_var |+ (out,{}) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (alloca_history func s ==> alloca_history func t)
Proof
  strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var out wl s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc ops [out]` >>
  `limit = Var out /\ not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [i]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, Abbr `out`, Abbr `i`] >>
     simp[not_fresh_at_def]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (rpt strip_tac >> fs[not_fresh_at_def, Abbr `out`] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  `step_inst_base i s = OK u` by simp[Abbr `i`, Abbr `u`, Abbr `out`] >>
  `step_prov PG G i u = DRESTRICT G (COMPL {out}) /\
   step_taint i s u tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[Abbr `i`] >> irule external_size_ghost >>
     simp[Abbr `u`, update_var_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i] s
     (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     simp[Abbr `i`] >> irule external_size_inst_check >>
     simp[Abbr `u`, update_var_def] >> metis_tac[]) >>
  `run_inst_seq [i] s = OK u /\
   run_inst_seq_mem_ok [i] s /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [i]` by
    (gvs[] >> simp[Abbr `i`, run_inst_seq_def, run_inst_seq_mem_ok_last,
                   mk_inst_def, is_terminator_def, below_frontier_no_ranges,
                   inst_dload_in_section_def]) >>
  `alloca_history func s ==>
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
     `get_instruction bb s.vs_inst_idx = SOME i` by
       (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     `alloca_history func (s with vs_inst_idx := SUC s.vs_inst_idx)` by
       (irule history_nonalloca_advance >> simp[] >>
        qexists_tac `i` >> simp[Abbr `i`, mk_inst_def] >>
        gvs[MEM, mk_inst_def]) >>
     irule alloca_history_frame >>
     qexists_tac `s with vs_inst_idx := SUC s.vs_inst_idx` >>
     simp[Abbr `u`, update_var_def]) >>
  qexistsl_tac [`out`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `DRESTRICT G (COMPL {out})`,
                `tn with t_var := tn.t_var |+ (out,{})`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[Abbr `u`] >>
  conj_tac
  >- (gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`[i]`,`sa`] >> simp[]) >>
  simp[Abbr `u`, lookup_var_update_var, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       op_prov_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[]
QED
