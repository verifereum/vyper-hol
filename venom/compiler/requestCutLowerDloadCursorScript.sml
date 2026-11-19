Theory requestCutLowerDloadCursor
Ancestors
  lowerDloadRecursiveInterface lowerDloadNormalData lowerDloadSourceInterface
  lowerDloadCoverageInvariant lowerDloadSharedState lowerDloadPtrForward
  lowerDloadOracleCallAssembly lowerDloadDefs requestCutOracleFrames
  o1PassContract contextCodegenRel unitShapeDefs ptrDiscipline venomState list

(* An external opcode in the target is exactly an original instruction at
   the start of a singleton expansion. *)
Theorem request_cut_lower_dload_cursor:
  ctx_pass_stage rp (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_initial_state_ok clip0 /\ clip0.vs_fmp = clip0.vs_initial_fmp /\
  code_layout_valid clip0 /\
  o1_src_inv D CS clip0 /\ callee_first names CS.ctx_functions /\
  frame_reachable clip0 CT stk PG G un gn i t /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  t.vs_outcomes = [] ==>
  ?A AG AP BH BP E H L U V astk d f fn gstk j keys live s (suspended:(num -> bool) list) tn.
    ld_annotated_reachable clip0 CS astk j L AP AG tn fn i s /\
    active_inst fn i s /\ ~in_revert_forward fn s /\ s.vs_outcomes = [] /\
    opaque_use_ok fn /\ U = {v | v IN V /\ ~retpc_var fn v} /\
    (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
    ld_normal_data CS fn V U clip0.vs_alloca_next E L H AP BP AG BH tn un s t
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `clip0.vs_alloca_next`, `vs0` |-> `clip0`,
    `rpolicy` |-> `rp`] ld_recursive_combined_coverage_static) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`stk`,`PG`,`G`,`un`,`gn`,`i`,`t`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o MATCH_MP (SPEC_ALL ld_recursive_combined_saved_forget)) >>
  disch_then (mp_tac o MATCH_MP (SPEC_ALL ld_recursive_saved_forget)) >>
  BETA_TAC >> disch_then (DISJ_CASES_THEN2 mp_tac mp_tac)
  >- (strip_tac >>
      `MEM i code` by
        (FIRST [qpat_x_assum `i = HD code` SUBST1_TAC >>
                  Cases_on `code` >> fs[],
                qpat_x_assum `i = EL n code` SUBST1_TAC >>
                  irule EL_MEM >> simp[]]) >>
      `code = [i'] /\ i = i'` by
        (qpat_assum `lower_dload_inst_supply _ i' = (code,_)` mp_tac >>
         qpat_assum `MEM i code` mp_tac >>
         qpat_assum `MEM i.inst_opcode _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         Cases_on `i'.inst_opcode = DLOAD` >>
         Cases_on `i'.inst_opcode = DLOADBYTES` >>
         gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
      `n = 0` by (Cases_on `n` >> gvs[]) >>
      `t = ta /\ un = ua /\ i = HD code` by fs[] >>
      `s.vs_outcomes = []` by
        (drule ld_normal_data_frame >>
         disch_then (mp_tac o MATCH_MP ld_frame_data_shared) >>
         simp[ld_shared_state_def] >> metis_tac[]) >>
      `opaque_use_ok fn` by
        (qpat_assum `o1_ctx_shape CS` mp_tac >>
         qpat_assum `CS.ctx_functions = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def]) >>
      `!v. MEM (Var v) i'.inst_operands ==> v IN V` by
        (simp[] >> metis_tac[ld_active_inst_member, ld_original_operand_support]) >>
      qexistsl_tac [`A`,`AG`,`AP`,`BH`,`BP`,`E`,`H`,`L`,`U`,`V`,
        `astk`,`32 * SUM (MAP CARD (suspended:(num -> bool) list))`,`f`,`fn`,`gstk`,`k`,`keys`,
        `live`,`s`,`suspended`,`tn`] >> fs[]) >>
  strip_tac >> drule_all revert_forward_pair_interval_opcode >> fs[MEM]
QED
