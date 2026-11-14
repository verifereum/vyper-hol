Theory bodyFullBopRestWordLoads
Ancestors
  bodyPtrBopInSlotLoad bodyPtrBopInCodeLoad bodyPtrBopInElementLoad
  bodyPtrBopInLoopContract fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr
  fragExecMem instMemFrontier memSafeRun ptrSafeRun ptrDiscipline
  stmtAppendStorageRunPtr exprLoweringProps venomExecSemantics venomInst
  venomState contextCodegenRel codegenRel finite_map words list rich_list

(* The final slot-read instruction of the compiled membership body.  The
   address prefix is handled separately; the concrete endpoint here is shared
   by the whole guarded horizon family. *)
Theorem rest_word_membership_slot_read_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  (!H:num. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {} /\
    key_taint (if tr then (Ts H).t_trans else (Ts H).t_stor) w = {}) ==>
  ?t Gt Tt. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (if tr then tload w s else sload w s) /\
    FLOOKUP (Gt H) dst = NONE /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  qexists_tac `update_var dst (if tr then tload w s else sload w s) s
    with vs_inst_idx := 3+delta` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta)
    (if tr then TLOAD else SLOAD) [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (if tr then tload w s else sload w s) s` >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by
    (Cases_on `tr` >> gvs[Abbr `ins`]) >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn (Gs H) (Ts H) ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_slot_header_operand_step >> simp[eval_operand_def] >> metis_tac[]) >>
  qabbrev_tac `g = step_prov PG (Gs H) ins u` >>
  qabbrev_tac `tn = (Ts H) with t_var := (Ts H).t_var |+ (dst,{})` >>
  `step_taint ins s u (Ts H) = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule scalar_storage_load_taint >> simp[eval_operand_def, update_var_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP (Gs H) x /\
      op_taint tn (Var x) = op_taint (Ts H) (Var x))` by
    (Cases_on `tr` >> simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  `inst_seq_ptr (DF H) 0 ctx fn PG (Gs H) (Ts H) [ins] s g tn` by
    simp[inst_seq_ptr_def, Abbr `g`] >>
  `run_inst_seq_mem_ok [ins] s` by
    (Cases_on `tr` >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_def, Abbr `ins`,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
    ins.inst_opcode <> ALLOCA /\ ins.inst_opcode <> GAS` by
    (Cases_on `tr` >> simp[Abbr `ins`, mk_inst_def, is_terminator_def]) >>
  `isPREFIX [ins] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule bodyMemAssignTopCopyPathsTheory.topcopy_instruction_prefix >> simp[] >> metis_tac[]) >>
  `run_inst_seq [ins] s = OK u` by simp[run_inst_seq_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK (u with vs_inst_idx := 3+delta),g,tn) /\
    allocas_from lo u` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
       (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
     disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> simp[]) >>
  `membership_loop_frame sa (G0 H) (T0 H) s0 g tn
      (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs H`, `Ts H`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs H`, `Ts H`] >> simp[]) >>
  qexistsl_tac [`g`, `tn`] >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >>
  gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED
