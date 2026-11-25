(* The Array header updates the comparison register and branches on it. *)
Theory bodyForArrayTestPathMods
Ancestors
  bodyPtrBopInLiteralSuffix fragGasSeqPtr decoderNavigationPtr instMemFrontier
  emitHelperProps arithmeticProps allocaHistory
  venomInst venomState venomExecSemantics ptrDiscipline ptrSafeRun
  memSafeRun finite_map fragGasOriginPtr fragExec codegenRel contextCodegenRel
  unitTransformDefs

Theorem for_array_eq_jnz_path_mods:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst eid EQ [Var idx;len_op] [dv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var dv;Label exit;Label bod] []) /\
  ~s.vs_halted /\
  eval_operand (Var idx) s = SOME x /\ eval_operand len_op s = SOME y /\
  op_taint tn (Var idx) = {} /\ op_taint tn len_op = {} /\
  op_prov G (Var idx) = NONE /\ op_prov G len_op = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let b = (x = y) in
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if b then exit else bod) (update_var dv (bool_to_word b) s)),
       DRESTRICT G (COMPL {dv}), tn with t_var := tn.t_var |+ (dv,{}))
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `i = mk_inst eid EQ [Var idx;len_op] [dv]` >>
  qabbrev_tac `w = bool_to_word (x = y)` >>
  qabbrev_tac `u = update_var dv w s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (dv,{})` >>
  `step_inst_base i s = OK u` by simp[Abbr `i`, Abbr `u`, Abbr `w`, step_EQ] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u`, update_var_def] >>
     conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     qx_gen_tac `op` >> Cases_on `op = Var idx` >> Cases_on `op = len_op` >> simp[]) >>
  `step_prov PG G i u = G1 /\ step_taint i s u tn = tn1` by
    simp[Abbr `i`, Abbr `G1`, Abbr `tn1`, Abbr `u`, membership_scalar_ghost_frame,
         step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   (ctx_has_dalloca ctx ==> dalloca_no_wrap i s) /\ i.inst_opcode <> GAS` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def,
         inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G1,tn1)` by
    (drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[Abbr `v`]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G1,tn1) []
     (OK (jump_to (if x = y then exit else bod) u),G1,tn1)` by
    (`lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb v.vs_inst_idx =
        SOME (mk_inst jid JNZ [Var dv;Label exit;Label bod] []) /\
      ~v.vs_halted /\ eval_operand (Var dv) v = SOME w /\
      op_taint tn1 (Var dv) = {} /\ allocas_from lo v /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
       simp[Abbr `v`, Abbr `u`, Abbr `tn1`, update_var_def, eval_operand_def,
            lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
            allocas_from_def, allocas_below_fmp_def] >>
     drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
     simp[Abbr `w`, Abbr `v`, jump_to_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED
