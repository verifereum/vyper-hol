Theory bodyFullBopRestWordLoads
Ancestors
  bodyPtrBopInSlotLoad bodyPtrBopInCodeLoad bodyPtrBopInElementLoad
  bodyPtrBopInLoopContract bodyPtrBopInLoopLayout
  augAssignPtrScalarRun
  augAssignPtrScalarCertificate fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr
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

(* The scalar address prefix is the actual initial slice of the emitted body,
   not a freestanding instruction toolkit. *)
Theorem rest_word_membership_runtime_prefix_code:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  product = "%" ++ toString (sa.cs_next_var+3) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+3+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+4+delta) /\
  code = [mk_inst (sa.cs_next_id+6) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  ((?w. arr = Lit w) \/ (?x. arr = Var x))
  ==> ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
       fn.fn_blocks = SOME bb /\ isPREFIX code bb.bb_instructions /\
       scalar_code A code /\
       EVERY (\ins. ins.inst_opcode <> INVOKE /\
         ~is_terminator ins.inst_opcode /\ ins.inst_opcode <> ALLOCA /\
         ins.inst_opcode <> GAS) code /\
       (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/
          x = "%" ++ toString (sa.cs_next_var+1) ==>
          ~MEM x (FLAT (MAP (\ins. ins.inst_outputs) code))) /\
       (!s i bw. lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i) /\
          eval_operand arr s = SOME bw ==>
          ?t. run_inst_seq code s = OK t /\
              lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
              (t with vs_vars := s.vs_vars) = s /\
              (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/
                 x = "%" ++ toString (sa.cs_next_var+1) ==>
                 lookup_var x t = lookup_var x s))
Proof
  strip_tac >>
  gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >> Cases_on `loc` >>
  gvs[scalar_code_def, scalar_shape_def, scalar_binary_def,
    scalar_available_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  gvs[loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    is_terminator_def, GSYM word_mul_n2w, GSYM word_add_n2w,
    loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem rest_word_membership_runtime_address_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  product = "%" ++ toString (sa.cs_next_var+3) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+3+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+4+delta) /\
  code = [mk_inst (sa.cs_next_id+6) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  ((?w. arr = Lit w) \/ (?x. arr = Var x)) /\
  (!H:num. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_prov (G0 H) arr = NONE /\ op_taint (T0 H) arr = {}) ==>
  ?t Gt Tt. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP (Gt H) dst = NONE /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_code >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >>
  simp[] >> strip_tac >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `?u. run_inst_seq code s = OK u /\
       lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
       (u with vs_vars := s.vs_vars) = s /\
       (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/
          x = "%" ++ toString (sa.cs_next_var+1) ==>
          lookup_var x u = lookup_var x s)` by (gvs[]) >>
  `!v. v IN A ==> op_prov (Gs H) (Var v) = NONE /\
                    op_taint (Ts H) (Var v) = {}` by
    (Cases_on `arr` >> gvs[membership_loop_registers_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  `scalar_code A code` by gvs[] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `DF H`, `s`] strip_assume_tac) >>
  `op_prov H' (Var dst) = NONE /\ op_taint tm (Var dst) = {}` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) scalar_seq_success_clean >>
     disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
     disch_then (qspec_then `A` (qspec_then `dst` mp_tac)) >>
     simp[mk_inst_def] >> gvs[]) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >>
  simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`H'`, `tm`] >>
  Cases_on `0 < skip` >> gvs[op_prov_def] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  qpat_x_assum `!s i bw. _ ==> ?t. _` kall_tac >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >>
  gvs[op_taint_def] >> metis_tac[]
QED

(* Runtime code read at the compiler's exact membership element cursor. *)
Theorem rest_word_membership_code_read_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) /\
  w2n w <= LENGTH s.vs_data_section /\
  (!H:num. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {}) ==>
  ?t Gt Tt. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME value /\
    FLOOKUP (Gt H) dst = NONE /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  qexists_tac `update_var dst value s with vs_inst_idx := 3+delta` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta) DLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst value s` >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn (Gs H) (Ts H) ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_code_header_operand_step >>
     simp[eval_operand_def] >> metis_tac[]) >>
  qabbrev_tac `g = step_prov PG (Gs H) ins u` >>
  qabbrev_tac `tn = (Ts H) with t_var := (Ts H).t_var |+ (dst,{})` >>
  `step_taint ins s u (Ts H) = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`, step_taint_def,
      set_var_taint_def, mk_inst_def, out_taint_def, update_var_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      new_site_bytes_def, FLOOKUP_DEF, range_bytes_def,
      taint_component_equality, DRESTRICT_UNIV, pred_setTheory.EXTENSION,
      SF CONJ_ss, eval_operand_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP (Gs H) x /\
      op_taint tn (Var x) = op_taint (Ts H) (Var x))` by
    simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr (DF H) 0 ctx fn PG (Gs H) (Ts H) [ins] s g tn` by
    simp[inst_seq_ptr_def, Abbr `g`] >>
  `run_inst_seq_mem_ok [ins] s` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_def, Abbr `ins`,
      unitTransformDefsTheory.inst_mem_below_frontier_def,
      inst_dload_in_section_def, mk_inst_def, eval_operand_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
    ins.inst_opcode <> ALLOCA /\ ins.inst_opcode <> GAS` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  `isPREFIX [ins] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule bodyMemAssignTopCopyPathsTheory.topcopy_instruction_prefix >> simp[] >> metis_tac[]) >>
  `run_inst_seq [ins] s = OK u` by simp[run_inst_seq_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[] >> strip_tac >> strip_tac >>
  `membership_loop_frame sa (G0 H) (T0 H) s0 g tn
      (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs H`, `Ts H`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs H`, `Ts H`] >> simp[]) >>
  qexistsl_tac [`g`, `tn`] >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED
