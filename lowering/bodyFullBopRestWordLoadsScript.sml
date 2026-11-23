Theory bodyFullBopRestWordLoads
Ancestors
  bodyPtrBopInSlotLoad bodyPtrBopInCodeContents[qualified] bodyPtrBopInElementLoad
  bodyPtrBopInLoopContract bodyPtrBopInLoopLayout bodyPtrBopInBoundedAddress bodyPtrBopInBoundedLayout
  augAssignPtrScalarRun typedCopyOriginPtrBase typedCopyLoopHeaderPtr typedCopyPtr instSeqComposePtr
  augAssignPtrScalarCertificate fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr
  fragGasCopySeqLiftProps
  fragExecMem instMemFrontier memSafeRun ptrSafeRun ptrDiscipline
  stmtAppendStorageRunPtr exprLoweringProps venomExecSemantics venomInst
  entryReachBodyFirstEmissionSupport exprSimBopRestWordLoadPath exprLowering compileEnv fragExec
  venomState contextCodegenRel codegenRel finite_map words list rich_list

(* The final slot-read instruction of the compiled membership body.  The
   address prefix is handled separately; the concrete endpoint here is shared
   by the whole guarded horizon family. *)
Theorem rest_word_membership_slot_read_joint_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {} /\
    key_taint (if tr then (Ts H).t_trans else (Ts H).t_stor) w = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
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
  Cases_on `0 < skip` >> Cases_on `loc` >> gvs[] >>
  gvs[scalar_code_def, scalar_shape_def, scalar_binary_def,
    scalar_available_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  FIRST [gvs[loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, lookup_var_def]] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    is_terminator_def, GSYM word_mul_n2w, GSYM word_add_n2w,
    loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem rest_word_membership_runtime_prefix_checked:
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
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  ((?w. arr = Lit w) \/ (?x. arr = Var x)) /\
  membership_loop_frame sa G0 T0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {} /\ ~s.vs_halted ==>
  ?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}
Proof
  strip_tac >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `ins1 = mk_inst (sa.cs_next_id+6) MUL
    [Var idx;Lit (n2w stride)] [product]` >>
  qabbrev_tac `u1 = update_var product (n2w i * n2w stride) s` >>
  qabbrev_tac `g1 = step_prov PG G ins1 u1` >>
  qabbrev_tac `t1 = step_taint ins1 s u1 tn` >>
  `lookup_var idx s = SOME (n2w i) /\ op_taint tn (Var idx) = {}` by
    gvs[membership_loop_registers_def, Abbr `idx`] >>
  `step_inst_base ins1 s = OK u1` by
    simp[Abbr `ins1`, Abbr `u1`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn ins1 s` by
    (simp[Abbr `ins1`] >> irule typed_copy_loop_test_check >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def]) >>
     qexists_tac `u1` >> gvs[Abbr `u1`, update_var_def]) >>
  `op_taint t1 (Var product) = {} /\
   t1.t_mem = tn.t_mem /\ t1.t_imm = tn.t_imm /\
   t1.t_stor = tn.t_stor /\ t1.t_trans = tn.t_trans /\
   (!x. x <> product ==> FLOOKUP g1 x = FLOOKUP G x /\
      op_taint t1 (Var x) = op_taint tn (Var x)) /\
   FLOOKUP g1 product = NONE` by
    (simp[Abbr `t1`, Abbr `g1`, Abbr `ins1`, Abbr `u1`] >>
     simp[typed_copy_origin_ptr_binop_ghost_frame, op_taint_def]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      x <> product` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g1 t1 u1` by
    (gvs[membership_loop_frame_def, Abbr `u1`, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  `membership_loop_registers sa i r g1 t1 u1` by
    (gvs[membership_loop_registers_def, Abbr `u1`, Abbr `idx`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def] >>
     metis_tac[]) >>
  qabbrev_tac `mid = if 0 < skip then
    [mk_inst (sa.cs_next_id+7) ADD [Lit (n2w skip);Var product] [offset]] else []` >>
  `scalar_code {product} mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, scalar_code_def,
      scalar_shape_def, scalar_binary_def, scalar_available_def, mk_inst_def]) >>
  `!v. v IN {product} ==> op_prov g1 (Var v) = NONE /\ op_taint t1 (Var v) = {}` by
    gvs[op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (u1 with vs_inst_idx := SUC s.vs_inst_idx)` by simp[] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG g1 t1 mid _ g2 t2` >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qabbrev_tac `u2 = (if 0 < skip then update_var offset
    (n2w skip + n2w i * n2w stride) u1 else u1)
      with vs_inst_idx := s.vs_inst_idx+1+delta` >>
  `run_inst_seq mid (u1 with vs_inst_idx := SUC s.vs_inst_idx) =
      OK (u2 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (Cases_on `0 < skip` >>
     simp[Abbr `mid`, Abbr `u2`, Abbr `u1`, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var offset u2 = SOME (n2w (skip+stride*i)) /\
   FLOOKUP g2 offset = NONE /\ op_taint t2 (Var offset) = {}` by
    (Cases_on `0 < skip`
     >- (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) scalar_seq_success_clean >>
         disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
         disch_then (qspec_then `{product}` (qspec_then `offset` mp_tac)) >>
         simp[Abbr `mid`, mk_inst_def] >> strip_tac >>
         gvs[Abbr `u2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           GSYM word_mul_n2w, GSYM word_add_n2w, arithmeticTheory.MULT_COMM, op_prov_def]) >>
     gvs[Abbr `mid`, inst_seq_ptr_def, Abbr `u2`, Abbr `u1`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       GSYM word_mul_n2w, arithmeticTheory.MULT_COMM]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      ~MEM x (FLAT (MAP (\ins. ins.inst_outputs) mid))` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, Abbr `idx`,
      loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `membership_loop_frame sa G0 T0 s0 g2 t2 u2 /\
   membership_loop_registers sa i r g2 t2 u2` by
    (Cases_on `0 < skip` >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u2`, Abbr `mid`, mk_inst_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand arr u2 = SOME bw /\ op_prov g2 arr = op_prov G0 arr /\
   op_taint t2 arr = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  qabbrev_tac `last = mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]` >>
  qabbrev_tac `u3 = update_var dst (bw+n2w (skip+stride*i)) u2` >>
  qabbrev_tac `g3 = step_prov PG g2 last u3` >>
  qabbrev_tac `t3 = step_taint last u2 u3 t2` >>
  `step_inst_base last u2 = OK u3` by
    gvs[Abbr `last`, Abbr `u3`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 last u2` by
    (simp[Abbr `last`] >> irule ptr_inst_ok_copy_len_binop >> gvs[]) >>
  `op_taint t3 (Var dst) = {} /\
   t3.t_mem = t2.t_mem /\ t3.t_imm = t2.t_imm /\
   t3.t_stor = t2.t_stor /\ t3.t_trans = t2.t_trans /\
   (!x. x <> dst ==> FLOOKUP g3 x = FLOOKUP g2 x /\
      op_taint t3 (Var x) = op_taint t2 (Var x))` by
    simp[Abbr `t3`, Abbr `g3`, Abbr `last`, Abbr `u3`,
      typed_copy_origin_ptr_binop_ghost_frame] >>
  `FLOOKUP g3 dst = op_prov G0 arr` by
    (Cases_on `op_prov G0 arr` >> gvs[] >>
     simp[Abbr `g3`, Abbr `last`, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, mk_inst_def] >>
     gvs[op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==> x <> dst` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3 u3 /\
   membership_loop_registers sa i r g3 t3 u3` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 G tn s` kall_tac >>
     qpat_x_assum `membership_loop_frame sa G0 T0 s0 g1 t1 u1` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r G tn s` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r g1 t1 u1` kall_tac >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     qx_gen_tac `protected` >> strip_tac >>
     `protected <> "%" ++ toString (sa.cs_next_var + (if 0 < skip then 1 else 0) + 4)` by
       (strip_tac >> gvs[]) >>
     simp[] >>
     first_x_assum (qspec_then `protected` mp_tac) >>
     simp[] >>
     qpat_x_assum `!v. ~MEM v _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x \/ _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `protected` mp_tac) >>
     rpt strip_tac >> gvs[stringTheory.STRCAT_EQNS]) >>
  `LENGTH mid = delta /\ EVERY (\ins. ~is_terminator ins.inst_opcode) mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, is_terminator_def]) >>
  `inst_seq_ptr D 0 ctx fn PG g2 t2 [last] u2 g3 t3` by
    simp[inst_seq_ptr_def, Abbr `g3`, Abbr `t3`] >>
  `inst_seq_ptr D 0 ctx fn PG g1 t1 (mid ++ [last])
    (u1 with vs_inst_idx := SUC s.vs_inst_idx) g3 t3` by
    (irule inst_seq_ptr_append_ok >> conj_tac >- simp[] >>
     qexistsl_tac [`g2`, `u2 with vs_inst_idx := SUC s.vs_inst_idx`, `t2`] >>
     gvs[Abbr `u2`, arithmeticTheory.ADD1]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s g3 t3` by
    (gvs[] >> simp[Once inst_seq_ptr_def, Abbr `g1`, Abbr `t1`,
       Abbr `ins1`, mk_inst_def, is_terminator_def] >>
     gvs[mk_inst_def]) >>
  `run_inst_seq code s = OK (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `ins1`, Abbr `last`, Abbr `idx`,
       run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, mk_inst_def, is_terminator_def,
       GSYM word_mul_n2w, GSYM word_add_n2w, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_ADD_0] >>
     gvs[eval_operand_def, lookup_var_def, stringTheory.STRCAT_EQNS,
         FLOOKUP_UPDATE, wordsTheory.WORD_ADD_0]) >>
  `lookup_var dst (u3 with vs_inst_idx := s.vs_inst_idx) =
    SOME (bw + n2w (skip + stride*i))` by
    simp[NoAsms, Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx) /\
   membership_loop_registers sa i r g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 g3 t3 u3` mp_tac >>
     qpat_x_assum `membership_loop_registers sa i r g3 t3 u3` mp_tac >>
     simp[NoAsms, membership_loop_frame_def, membership_loop_registers_def,
          lookup_var_def] >>
     rpt strip_tac >> qpat_x_assum `u3 = _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`u3 with vs_inst_idx := s.vs_inst_idx`, `g3`, `t3`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
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
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `DF H`] strip_assume_tac) >>
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
Theorem rest_word_membership_code_read_joint_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) /\
  w2n w <= LENGTH s.vs_data_section /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
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

Theorem rest_word_membership_memory_read_joint_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ ptr_covers (Gs H) (Ts H) src s 32 /\
    mem_word_taint (Ts H).t_mem (w2n w) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (mload (w2n w) s) /\
    FLOOKUP (Gt H) dst = NONE /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  qexists_tac `update_var dst (mload (w2n w) s) s with vs_inst_idx := 3+delta` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta) MLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (mload (w2n w) s) s` >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u` by
    (asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, step_inst_base_opcode_eqs,
      mk_inst_def, instruction_accessors, instruction_accfupds,
      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok (DF H) 0 0 ctx fn (Gs H) (Ts H) ins s` by
    (simp[Abbr `ins`] >> irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[Abbr `u`, update_var_def]) >>
  qabbrev_tac `g = step_prov PG (Gs H) ins u` >>
  qabbrev_tac `tn = (Ts H) with t_var := (Ts H).t_var |+ (dst,{})` >>
  `step_taint ins s u (Ts H) = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule bodyPtrBopInLoadRunTheory.readonly_load_taint >> simp[eval_operand_def, update_var_def]) >>
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
      below_frontier_MLOAD, inst_dload_in_section_def, mk_inst_def,
      eval_operand_def] >>
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

Theorem rest_word_membership_runtime_address_preserving_joint_indexed:
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
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint (T0 H) arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP (Gt H) dst = op_prov (G0 H) arr /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_code >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >> simp[] >> strip_tac >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr (DF H) 0 ctx fn PG (Gs H) (Ts H) code s gf tf /\
    membership_loop_frame sa (G0 H) (T0 H) s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov (G0 H) arr /\ op_taint tf (Var dst) = {}` by
    (irule rest_word_membership_runtime_prefix_checked >> simp[] >> metis_tac[]) >>
  `eval_operand arr s = SOME bw` by
    (qpat_assum `membership_loop_frame _ _ _ _ (Gs H) (Ts H) s`
       (mp_then Any mp_tac membership_loop_frame_operand) >> simp[]) >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `?v. run_inst_seq code s = OK v /\ (v with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `!s i bw. _` (qspecl_then [`s`, `i`, `bw`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`gf`, `tf`] >>
  Cases_on `0 < skip` >> gvs[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >> metis_tac[]
QED

Theorem rest_word_membership_runtime_prefix_code_bounded:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
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
  gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >> Cases_on `loc` >> gvs[] >>
  gvs[scalar_code_def, scalar_shape_def, scalar_binary_def,
    scalar_available_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  FIRST [gvs[loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, lookup_var_def]] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    is_terminator_def, GSYM word_mul_n2w, GSYM word_add_n2w,
    loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem rest_word_membership_runtime_prefix_operational:
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
  (!x. arr = Var x ==> not_fresh_at sa x)
  ==> ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
       fn.fn_blocks = SOME bb /\ isPREFIX code bb.bb_instructions /\
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
  (* Settle the block prefix before pruning layout facts from execution. *)
  conj_tac >- (Cases_on `0 < skip` >> simp[]) >>
  rpt (qpat_x_assum `lookup_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!bb'. MEM bb' _ ==> lookup_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `isPREFIX _ _` kall_tac) >>
  Cases_on `arr` >> Cases_on `0 < skip` >> gvs[] >>
  gvs[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, lookup_var_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[GSYM word_mul_n2w, GSYM word_add_n2w,
    loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem rest_word_membership_runtime_prefix_checked_operand:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  product = "%" ++ toString (sa.cs_next_var+3) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+3+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+4+delta) /\
  code = [mk_inst (sa.cs_next_id+6) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]] /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  membership_loop_frame sa G0 T0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {} /\ ~s.vs_halted ==>
  ?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}
Proof
  strip_tac >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `ins1 = mk_inst (sa.cs_next_id+6) MUL
    [Var idx;Lit (n2w stride)] [product]` >>
  qabbrev_tac `u1 = update_var product (n2w i * n2w stride) s` >>
  qabbrev_tac `g1 = step_prov PG G ins1 u1` >>
  qabbrev_tac `t1 = step_taint ins1 s u1 tn` >>
  `lookup_var idx s = SOME (n2w i) /\ op_taint tn (Var idx) = {}` by
    gvs[membership_loop_registers_def, Abbr `idx`] >>
  `step_inst_base ins1 s = OK u1` by
    simp[Abbr `ins1`, Abbr `u1`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn ins1 s` by
    (simp[Abbr `ins1`] >> irule typed_copy_loop_test_check >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def]) >>
     qexists_tac `u1` >> gvs[Abbr `u1`, update_var_def]) >>
  `op_taint t1 (Var product) = {} /\
   t1.t_mem = tn.t_mem /\ t1.t_imm = tn.t_imm /\
   t1.t_stor = tn.t_stor /\ t1.t_trans = tn.t_trans /\
   (!x. x <> product ==> FLOOKUP g1 x = FLOOKUP G x /\
      op_taint t1 (Var x) = op_taint tn (Var x)) /\
   FLOOKUP g1 product = NONE` by
    (simp[Abbr `t1`, Abbr `g1`, Abbr `ins1`, Abbr `u1`] >>
     simp[typed_copy_origin_ptr_binop_ghost_frame, op_taint_def]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      x <> product` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g1 t1 u1` by
    (gvs[membership_loop_frame_def, Abbr `u1`, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  `membership_loop_registers sa i r g1 t1 u1` by
    (gvs[membership_loop_registers_def, Abbr `u1`, Abbr `idx`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def] >>
     metis_tac[]) >>
  qabbrev_tac `mid = if 0 < skip then
    [mk_inst (sa.cs_next_id+7) ADD [Lit (n2w skip);Var product] [offset]] else []` >>
  `scalar_code {product} mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, scalar_code_def,
      scalar_shape_def, scalar_binary_def, scalar_available_def, mk_inst_def]) >>
  `!v. v IN {product} ==> op_prov g1 (Var v) = NONE /\ op_taint t1 (Var v) = {}` by
    gvs[op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (u1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`allocas_below_fmp (u1 with vs_inst_idx := SUC s.vs_inst_idx) <=>
       allocas_below_fmp s` by simp[Abbr `u1`, update_var_def, allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG g1 t1 mid _ g2 t2` >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qabbrev_tac `u2 = (if 0 < skip then update_var offset
    (n2w skip + n2w i * n2w stride) u1 else u1)
      with vs_inst_idx := s.vs_inst_idx+1+delta` >>
  `run_inst_seq mid (u1 with vs_inst_idx := SUC s.vs_inst_idx) =
      OK (u2 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (Cases_on `0 < skip` >>
     simp[Abbr `mid`, Abbr `u2`, Abbr `u1`, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var offset u2 = SOME (n2w (skip+stride*i)) /\
   FLOOKUP g2 offset = NONE /\ op_taint t2 (Var offset) = {}` by
    (Cases_on `0 < skip`
     >- (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) scalar_seq_success_clean >>
         disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
         disch_then (qspec_then `{product}` (qspec_then `offset` mp_tac)) >>
         simp[Abbr `mid`, mk_inst_def] >> strip_tac >>
         gvs[Abbr `u2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           GSYM word_mul_n2w, GSYM word_add_n2w, arithmeticTheory.MULT_COMM, op_prov_def]) >>
     gvs[Abbr `mid`, inst_seq_ptr_def, Abbr `u2`, Abbr `u1`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       GSYM word_mul_n2w, arithmeticTheory.MULT_COMM]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      ~MEM x (FLAT (MAP (\ins. ins.inst_outputs) mid))` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, Abbr `idx`,
      loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `membership_loop_frame sa G0 T0 s0 g2 t2 u2 /\
   membership_loop_registers sa i r g2 t2 u2` by
    (Cases_on `0 < skip` >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u2`, Abbr `mid`, mk_inst_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand arr u2 = SOME bw /\ op_prov g2 arr = op_prov G0 arr /\
   op_taint t2 arr = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  qabbrev_tac `last = mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]` >>
  qabbrev_tac `u3 = update_var dst (bw+n2w (skip+stride*i)) u2` >>
  qabbrev_tac `g3 = step_prov PG g2 last u3` >>
  qabbrev_tac `t3 = step_taint last u2 u3 t2` >>
  `step_inst_base last u2 = OK u3` by
    gvs[Abbr `last`, Abbr `u3`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u2` by
    (`allocas_below_fmp u2 <=> allocas_below_fmp s` by
       (Cases_on `0 < skip` >>
        simp[Abbr `u2`, Abbr `u1`, update_var_def, allocas_below_fmp_def]) >>
     asm_rewrite_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 last u2` by
    (simp[Abbr `last`] >> irule ptr_inst_ok_copy_len_binop >> gvs[]) >>
  `op_taint t3 (Var dst) = {} /\
   t3.t_mem = t2.t_mem /\ t3.t_imm = t2.t_imm /\
   t3.t_stor = t2.t_stor /\ t3.t_trans = t2.t_trans /\
   (!x. x <> dst ==> FLOOKUP g3 x = FLOOKUP g2 x /\
      op_taint t3 (Var x) = op_taint t2 (Var x))` by
    simp[Abbr `t3`, Abbr `g3`, Abbr `last`, Abbr `u3`,
      typed_copy_origin_ptr_binop_ghost_frame] >>
  `FLOOKUP g3 dst = op_prov G0 arr` by
    (Cases_on `op_prov G0 arr` >> gvs[] >>
     simp[Abbr `g3`, Abbr `last`, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, mk_inst_def] >>
     gvs[op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==> x <> dst` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3 u3 /\
   membership_loop_registers sa i r g3 t3 u3` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 G tn s` kall_tac >>
     qpat_x_assum `membership_loop_frame sa G0 T0 s0 g1 t1 u1` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r G tn s` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r g1 t1 u1` kall_tac >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     qx_gen_tac `protected` >> strip_tac >>
     `protected <> "%" ++ toString (sa.cs_next_var + (if 0 < skip then 1 else 0) + 4)` by
       (strip_tac >> gvs[]) >>
     simp[] >>
     first_x_assum (qspec_then `protected` mp_tac) >>
     simp[] >>
     qpat_x_assum `!v. ~MEM v _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x \/ _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `protected` mp_tac) >>
     rpt strip_tac >> gvs[stringTheory.STRCAT_EQNS]) >>
  `LENGTH mid = delta /\ EVERY (\ins. ~is_terminator ins.inst_opcode) mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, is_terminator_def]) >>
  `inst_seq_ptr D 0 ctx fn PG g2 t2 [last] u2 g3 t3` by
    simp[inst_seq_ptr_def, Abbr `g3`, Abbr `t3`] >>
  `inst_seq_ptr D 0 ctx fn PG g1 t1 (mid ++ [last])
    (u1 with vs_inst_idx := SUC s.vs_inst_idx) g3 t3` by
    (irule inst_seq_ptr_append_ok >> conj_tac >- simp[] >>
     qexistsl_tac [`g2`, `u2 with vs_inst_idx := SUC s.vs_inst_idx`, `t2`] >>
     gvs[Abbr `u2`, arithmeticTheory.ADD1]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s g3 t3` by
    (gvs[] >> simp[Once inst_seq_ptr_def, Abbr `g1`, Abbr `t1`,
       Abbr `ins1`, mk_inst_def, is_terminator_def] >>
     gvs[mk_inst_def]) >>
  `run_inst_seq code s = OK (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (Cases_on `arr` >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     Cases_on `0 < skip` >> simp[Abbr `mid`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `ins1`, Abbr `last`, Abbr `idx`,
       run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, mk_inst_def, is_terminator_def,
       GSYM word_mul_n2w, GSYM word_add_n2w, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_ADD_0] >>
     gvs[eval_operand_def, lookup_var_def, stringTheory.STRCAT_EQNS,
         FLOOKUP_UPDATE, wordsTheory.WORD_ADD_0]) >>
  `lookup_var dst (u3 with vs_inst_idx := s.vs_inst_idx) =
    SOME (bw + n2w (skip + stride*i))` by
    simp[NoAsms, Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx) /\
   membership_loop_registers sa i r g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 g3 t3 u3` mp_tac >>
     qpat_x_assum `membership_loop_registers sa i r g3 t3 u3` mp_tac >>
     simp[NoAsms, membership_loop_frame_def, membership_loop_registers_def,
          lookup_var_def] >>
     rpt strip_tac >> qpat_x_assum `u3 = _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`u3 with vs_inst_idx := s.vs_inst_idx`, `g3`, `t3`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rest_word_membership_runtime_address_operand_joint_indexed:
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
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint (T0 H) arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP (Gt H) dst = op_prov (G0 H) arr /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_operational >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >> simp[] >> strip_tac >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr (DF H) 0 ctx fn PG (Gs H) (Ts H) code s gf tf /\
    membership_loop_frame sa (G0 H) (T0 H) s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov (G0 H) arr /\ op_taint tf (Var dst) = {}` by
    (irule rest_word_membership_runtime_prefix_checked_operand >> simp[] >> metis_tac[]) >>
  `eval_operand arr s = SOME bw` by
    (qpat_assum `membership_loop_frame _ _ _ _ (Gs H) (Ts H) s`
       (mp_then Any mp_tac membership_loop_frame_operand) >> simp[]) >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `?v. run_inst_seq code s = OK v /\ (v with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `!s i bw. _` (qspecl_then [`s`, `i`, `bw`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`gf`, `tf`] >>
  Cases_on `0 < skip` >> gvs[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >> metis_tac[]
QED

Theorem rest_word_membership_runtime_prefix_operational_bounded:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x)
  ==> ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
       fn.fn_blocks = SOME bb /\ isPREFIX code bb.bb_instructions /\
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
  gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  (* Keep compiler layout facts out of the operational calculation. *)
  conj_tac >- (Cases_on `0 < skip` >> Cases_on `loc` >> simp[]) >>
  rpt (qpat_x_assum `lookup_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!bb'. MEM bb' _ ==> lookup_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `isPREFIX _ _` kall_tac) >>
  Cases_on `arr` >> Cases_on `0 < skip` >> gvs[] >>
  gvs[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, lookup_var_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
    eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, is_terminator_def] >>
  simp[GSYM word_mul_n2w, GSYM word_add_n2w,
    loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem rest_word_membership_runtime_prefix_checked_operand_bounded:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  membership_loop_frame sa G0 T0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {} /\ ~s.vs_halted ==>
  ?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}
Proof
  strip_tac >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `ins1 = mk_inst (sa.cs_next_id+9) MUL
    [Var idx;Lit (n2w stride)] [product]` >>
  qabbrev_tac `u1 = update_var product (n2w i * n2w stride) s` >>
  qabbrev_tac `g1 = step_prov PG G ins1 u1` >>
  qabbrev_tac `t1 = step_taint ins1 s u1 tn` >>
  `lookup_var idx s = SOME (n2w i) /\ op_taint tn (Var idx) = {}` by
    gvs[membership_loop_registers_def, Abbr `idx`] >>
  `step_inst_base ins1 s = OK u1` by
    simp[Abbr `ins1`, Abbr `u1`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn ins1 s` by
    (simp[Abbr `ins1`] >> irule typed_copy_loop_test_check >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def]) >>
     qexists_tac `u1` >> gvs[Abbr `u1`, update_var_def]) >>
  `op_taint t1 (Var product) = {} /\
   t1.t_mem = tn.t_mem /\ t1.t_imm = tn.t_imm /\
   t1.t_stor = tn.t_stor /\ t1.t_trans = tn.t_trans /\
   (!x. x <> product ==> FLOOKUP g1 x = FLOOKUP G x /\
      op_taint t1 (Var x) = op_taint tn (Var x)) /\
   FLOOKUP g1 product = NONE` by
    (simp[Abbr `t1`, Abbr `g1`, Abbr `ins1`, Abbr `u1`] >>
     simp[typed_copy_origin_ptr_binop_ghost_frame, op_taint_def]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      x <> product` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g1 t1 u1` by
    (gvs[membership_loop_frame_def, Abbr `u1`, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  `membership_loop_registers sa i r g1 t1 u1` by
    (gvs[membership_loop_registers_def, Abbr `u1`, Abbr `idx`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def] >>
     metis_tac[]) >>
  qabbrev_tac `mid = if 0 < skip then
    [mk_inst (sa.cs_next_id+10) ADD [Lit (n2w skip);Var product] [offset]] else []` >>
  `scalar_code {product} mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, scalar_code_def,
      scalar_shape_def, scalar_binary_def, scalar_available_def, mk_inst_def]) >>
  `!v. v IN {product} ==> op_prov g1 (Var v) = NONE /\ op_taint t1 (Var v) = {}` by
    gvs[op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (u1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`allocas_below_fmp (u1 with vs_inst_idx := SUC s.vs_inst_idx) <=>
       allocas_below_fmp s` by simp[Abbr `u1`, update_var_def, allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG g1 t1 mid _ g2 t2` >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qabbrev_tac `u2 = (if 0 < skip then update_var offset
    (n2w skip + n2w i * n2w stride) u1 else u1)
      with vs_inst_idx := s.vs_inst_idx+1+delta` >>
  `run_inst_seq mid (u1 with vs_inst_idx := SUC s.vs_inst_idx) =
      OK (u2 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (Cases_on `0 < skip` >>
     simp[Abbr `mid`, Abbr `u2`, Abbr `u1`, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var offset u2 = SOME (n2w (skip+stride*i)) /\
   FLOOKUP g2 offset = NONE /\ op_taint t2 (Var offset) = {}` by
    (Cases_on `0 < skip`
     >- (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) scalar_seq_success_clean >>
         disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
         disch_then (qspec_then `{product}` (qspec_then `offset` mp_tac)) >>
         simp[Abbr `mid`, mk_inst_def] >> strip_tac >>
         gvs[Abbr `u2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           GSYM word_mul_n2w, GSYM word_add_n2w, arithmeticTheory.MULT_COMM, op_prov_def]) >>
     gvs[Abbr `mid`, inst_seq_ptr_def, Abbr `u2`, Abbr `u1`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       GSYM word_mul_n2w, arithmeticTheory.MULT_COMM]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==>
      ~MEM x (FLAT (MAP (\ins. ins.inst_outputs) mid))` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, Abbr `idx`,
      loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `membership_loop_frame sa G0 T0 s0 g2 t2 u2 /\
   membership_loop_registers sa i r g2 t2 u2` by
    (Cases_on `0 < skip` >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u2`, Abbr `mid`, mk_inst_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand arr u2 = SOME bw /\ op_prov g2 arr = op_prov G0 arr /\
   op_taint t2 arr = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  qabbrev_tac `last = mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]` >>
  qabbrev_tac `u3 = update_var dst (bw+n2w (skip+stride*i)) u2` >>
  qabbrev_tac `g3 = step_prov PG g2 last u3` >>
  qabbrev_tac `t3 = step_taint last u2 u3 t2` >>
  `step_inst_base last u2 = OK u3` by
    gvs[Abbr `last`, Abbr `u3`, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u2` by
    (`allocas_below_fmp u2 <=> allocas_below_fmp s` by
       (Cases_on `0 < skip` >>
        simp[Abbr `u2`, Abbr `u1`, update_var_def, allocas_below_fmp_def]) >>
     asm_rewrite_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn g2 t2 last u2` by
    (simp[Abbr `last`] >> irule ptr_inst_ok_copy_len_binop >> gvs[]) >>
  `op_taint t3 (Var dst) = {} /\
   t3.t_mem = t2.t_mem /\ t3.t_imm = t2.t_imm /\
   t3.t_stor = t2.t_stor /\ t3.t_trans = t2.t_trans /\
   (!x. x <> dst ==> FLOOKUP g3 x = FLOOKUP g2 x /\
      op_taint t3 (Var x) = op_taint t2 (Var x))` by
    simp[Abbr `t3`, Abbr `g3`, Abbr `last`, Abbr `u3`,
      typed_copy_origin_ptr_binop_ghost_frame] >>
  `FLOOKUP g3 dst = op_prov G0 arr` by
    (Cases_on `op_prov G0 arr` >> gvs[] >>
     simp[Abbr `g3`, Abbr `last`, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, mk_inst_def] >>
     gvs[op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var \/ x = idx ==> x <> dst` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `idx`] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3 u3 /\
   membership_loop_registers sa i r g3 t3 u3` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 G tn s` kall_tac >>
     qpat_x_assum `membership_loop_frame sa G0 T0 s0 g1 t1 u1` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r G tn s` kall_tac >>
     qpat_x_assum `membership_loop_registers sa i r g1 t1 u1` kall_tac >>
     gvs[membership_loop_frame_def, membership_loop_registers_def,
       Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `idx`, op_prov_def, venom_state_component_equality] >>
     qx_gen_tac `protected` >> strip_tac >>
     `protected <> "%" ++ toString (sa.cs_next_var + (if 0 < skip then 1 else 0) + 6)` by
       (strip_tac >> gvs[]) >>
     simp[] >>
     first_x_assum (qspec_then `protected` mp_tac) >>
     simp[] >>
     qpat_x_assum `!v. ~MEM v _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x \/ _ ==> _` (qspec_then `protected` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `protected` mp_tac) >>
     rpt strip_tac >> gvs[stringTheory.STRCAT_EQNS]) >>
  `LENGTH mid = delta /\ EVERY (\ins. ~is_terminator ins.inst_opcode) mid` by
    (Cases_on `0 < skip` >> simp[Abbr `mid`, mk_inst_def, is_terminator_def]) >>
  `inst_seq_ptr D 0 ctx fn PG g2 t2 [last] u2 g3 t3` by
    simp[inst_seq_ptr_def, Abbr `g3`, Abbr `t3`] >>
  `inst_seq_ptr D 0 ctx fn PG g1 t1 (mid ++ [last])
    (u1 with vs_inst_idx := SUC s.vs_inst_idx) g3 t3` by
    (irule inst_seq_ptr_append_ok >> conj_tac >- simp[] >>
     qexistsl_tac [`g2`, `u2 with vs_inst_idx := SUC s.vs_inst_idx`, `t2`] >>
     gvs[Abbr `u2`, arithmeticTheory.ADD1]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s g3 t3` by
    (gvs[] >> simp[Once inst_seq_ptr_def, Abbr `g1`, Abbr `t1`,
       Abbr `ins1`, mk_inst_def, is_terminator_def] >>
     gvs[mk_inst_def]) >>
  `run_inst_seq code s = OK (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (Cases_on `arr` >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     Cases_on `0 < skip` >> simp[Abbr `mid`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `ins1`, Abbr `last`, Abbr `idx`,
       run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operands_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, mk_inst_def, is_terminator_def,
       GSYM word_mul_n2w, GSYM word_add_n2w, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_ADD_0] >>
     fs[eval_operand_def, lookup_var_def] >>
     simp[stringTheory.STRCAT_EQNS, FLOOKUP_UPDATE, wordsTheory.WORD_ADD_0]) >>
  `lookup_var dst (u3 with vs_inst_idx := s.vs_inst_idx) =
    SOME (bw + n2w (skip + stride*i))` by
    simp[NoAsms, Abbr `u3`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx) /\
   membership_loop_registers sa i r g3 t3
    (u3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_x_assum `membership_loop_frame sa G0 T0 s0 g3 t3 u3` mp_tac >>
     qpat_x_assum `membership_loop_registers sa i r g3 t3 u3` mp_tac >>
     simp[NoAsms, membership_loop_frame_def, membership_loop_registers_def,
          lookup_var_def] >>
     rpt strip_tac >> qpat_x_assum `u3 = _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`u3 with vs_inst_idx := s.vs_inst_idx`, `g3`, `t3`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rest_word_membership_runtime_prefix_checked_bounded:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  ((?w. arr = Lit w) \/ (?x. arr = Var x)) /\
  membership_loop_frame sa G0 T0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {} /\ ~s.vs_halted ==>
  ?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr D 0 ctx fn PG G tn code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}
Proof
  strip_tac >> irule rest_word_membership_runtime_prefix_checked_operand_bounded >>
  simp[] >> metis_tac[]
QED

Theorem rest_word_membership_runtime_address_operand_joint_bounded_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint (T0 H) arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP (Gt H) dst = op_prov (G0 H) arr /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_operational_bounded >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >> simp[] >> strip_tac >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr (DF H) 0 ctx fn PG (Gs H) (Ts H) code s gf tf /\
    membership_loop_frame sa (G0 H) (T0 H) s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov (G0 H) arr /\ op_taint tf (Var dst) = {}` by
    (irule rest_word_membership_runtime_prefix_checked_operand_bounded >> simp[] >> metis_tac[]) >>
  `eval_operand arr s = SOME bw` by
    (qpat_assum `membership_loop_frame _ _ _ _ (Gs H) (Ts H) s`
       (mp_then Any mp_tac membership_loop_frame_operand) >> simp[]) >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `?v. run_inst_seq code s = OK v /\ (v with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `!s i bw. _` (qspecl_then [`s`, `i`, `bw`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`gf`, `tf`] >>
  Cases_on `0 < skip` >> gvs[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >> metis_tac[]
QED

Theorem rest_word_membership_runtime_address_preserving_joint_bounded_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  ((?w. arr = Lit w) \/ (?x. arr = Var x)) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint (T0 H) arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP (Gt H) dst = op_prov (G0 H) arr /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >> irule rest_word_membership_runtime_address_operand_joint_bounded_indexed >>
  simp[] >> metis_tac[]
QED

Theorem rest_word_membership_slot_read_joint_bounded_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {} /\
    key_taint (if tr then (Ts H).t_trans else (Ts H).t_stor) w = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
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
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta)
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

Theorem rest_word_membership_code_read_joint_bounded_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) /\
  w2n w <= LENGTH s.vs_data_section /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint (Ts H) (Var src) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
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
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta) DLOAD [Var src] [dst]` >>
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

Theorem rest_word_membership_memory_read_joint_bounded_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i r (Gs H) (Ts H) s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ ptr_covers (Gs H) (Ts H) src s 32 /\
    mem_word_taint (Ts H).t_mem (w2n w) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa i r (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (mload (w2n w) s) /\
    FLOOKUP (Gt H) dst = NONE /\ op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >>
  qexists_tac `update_var dst (mload (w2n w) s) s with vs_inst_idx := 3+delta` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta) MLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (mload (w2n w) s) s` >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u` by
    (asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, step_inst_base_opcode_eqs,
      mk_inst_def, instruction_accessors, instruction_accfupds,
      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok (DF H) 0 0 ctx fn (Gs H) (Ts H) ins s` by
    (simp[Abbr `ins`] >> irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[Abbr `u`, update_var_def]) >>
  qabbrev_tac `g = step_prov PG (Gs H) ins u` >>
  qabbrev_tac `tn = (Ts H) with t_var := (Ts H).t_var |+ (dst,{})` >>
  `step_taint ins s u (Ts H) = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule bodyPtrBopInLoadRunTheory.readonly_load_taint >> simp[eval_operand_def, update_var_def]) >>
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
      below_frontier_MLOAD, inst_dload_in_section_def, mk_inst_def,
      eval_operand_def] >>
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

Theorem rest_word_membership_header_joint_indexed:
  vv_location vv = SOME loc /\ (~cenv.ce_is_ctor \/ loc <> LocCode) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!H:'h. guard H ==> ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand (vv_operand vv) s = SOME w /\ op_taint (TF H) (vv_operand vv) = {} /\
    (case loc of
       LocMemory =>
         (?x. vv_operand vv = Var x /\ ptr_covers (G H) (TF H) x s 32) /\
         w2n w + 32 <= s.vs_alloca_next /\ mem_word_taint (TF H).t_mem (w2n w) = {} /\
         mload (w2n w) s = n2w n
     | LocStorage => key_taint (TF H).t_stor w = {} /\ sload w s = n2w n
     | LocTransient => key_taint (TF H).t_trans w = {} /\ tload w s = n2w n
     | LocCode => w2n w <= LENGTH s.vs_data_section /\
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) = n2w n
     | _ => F)) ==>
  ?len sm t GF TFF.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sm = (op,sb) /\
    (!H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G H,TF H) [] (OK t,GF H,TFF H) /\
      membership_loop_frame sa (G H) (TF H) s (GF H) (TFF H) t /\
      eval_operand len t = SOME (n2w n) /\ op_prov (GF H) len = NONE /\ op_taint (TFF H) len = {} /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_var_array_membership_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_array_membership_loop _ _ len _ _ _ _ _ sm = _` >>
  `fn_has_code sa sm fn` by
    (irule (cj 1 fn_has_code_split) >> conj_tac
     >- metis_tac[first_emission_ptr_load] >>
     qexists_tac `sb` >> simp[] >> metis_tac[membership_bounded_loop_extends]) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
     compile_ptr_load F cenv.ce_imm_alloca loc` by
    (Cases_on `loc` >> gvs[FUN_EQ_THM, contextTheory.compile_ptr_load_def,
       contextTheory.compile_imm_load_word_def]) >>
  `compile_ptr_load F cenv.ce_imm_alloca loc (vv_operand vv) sa = (len,sm)` by metis_tac[] >>
  drule_all membership_length_header_code >> strip_tac >>
  drule membership_length_header_layout >>
  disch_then (qspec_then `(case loc of LocMemory => MLOAD | LocStorage => SLOAD |
    LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)` mp_tac) >>
  simp[] >> strip_tac >>
  simp[] >>
  qabbrev_tac `dst = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id
    (case loc of LocMemory => MLOAD | LocStorage => SLOAD | LocTransient => TLOAD |
      LocCalldata => CALLDATALOAD | LocCode => DLOAD) [vv_operand vv] [dst]` >>
  qabbrev_tac `u = update_var dst (n2w n) s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `\H. step_prov PG (G H) ins u`, `\H. step_taint ins s u (TF H)`] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `step_inst_base ins s = OK u` by
    (Cases_on `loc` >>
     asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, mk_inst_def,
       step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     gvs[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx fn (G H) (TF H) ins s` by
    suspend "checks" >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,fn,PG) (s,G H,TF H) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG (G H) ins u, step_taint ins s u (TF H))` by
    suspend "edge" >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]) >>
  suspend "post"
QED

Resume rest_word_membership_header_joint_indexed[checks]:
  markerLib.RESUME_TAC >>
  Cases_on `loc` >> gvs[Abbr `ins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    memLocDefsTheory.mem_read_ops_def, step_inst_non_invoke, Abbr `u`, update_var_def,
    allocas_from_def] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, eval_operand_def] >>
  first_assum ACCEPT_TAC
QED

Resume rest_word_membership_header_joint_indexed[edge]:
  markerLib.RESUME_TAC >>
  `ins.inst_opcode <> GAS /\ ins.inst_opcode <> INVOKE /\
   ~is_terminator ins.inst_opcode /\
   inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
    (Cases_on `loc` >> gvs[Abbr `ins`, mk_inst_def, is_terminator_def,
      unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME ins` by simp[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    unitTransformDefs$dalloca_no_wrap ins s)` by simp[] >>
  drule_all straight_line_origin_ptr_edge >> simp[]
QED

Resume rest_word_membership_header_joint_indexed[post]:
  markerLib.RESUME_TAC >> gvs[]
  >>~- ([`gas_origin_ptr_path _ _ _ _`],
    `~(u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)).vs_halted` by
      simp[Abbr `u`, update_var_def] >>
    drule (cj 2 gas_origin_ptr_path_rules) >>
    disch_then (qspec_then `[]` mp_tac) >> simp[] >>
    disch_then match_mp_tac >>
    irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  simp[Abbr `ins`, Abbr `u`, membership_loop_frame_def,
    step_taint_def, set_var_taint_def, out_taint_def,
    step_prov_def, set_prov_def, out_prov_def, op_prov_def,
    mk_inst_def, update_var_def, eval_operand_def, lookup_var_def,
    op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, allocas_from_def] >>
  simp[mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    new_site_bytes_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
    venom_state_component_equality] >>
  rpt conj_tac >> gvs[allocas_from_def, FLOOKUP_DEF] >>
  qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst` by
    gvs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`,
        stringTheory.STRCAT_EQNS] >>
  simp[]
QED

Finalise rest_word_membership_header_joint_indexed

(* Transport the opcode certificate across the selected prefix split. *)
val membership_nowrap_tac =
  disch_tac >> map_every qx_gen_tac [`pre`, `selected`, `post`, `v`] >>
  strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
  qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
  qpat_x_assum `_ = pre ++ selected::post`
    (fn th => pure_once_rewrite_tac [th] >> simp[EVERY_APPEND]);

(* Use the established implication as a whole, not as a conditional rewrite. *)
val simp_membership_nowrap_tac =
  qpat_assum `ctx_has_dalloca ctx ==> !pre i post v. _`
    (fn th => simp[EQT_INTRO (SRULE [] th)]);

Theorem rest_word_membership_slot_read_joint_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint Ts (Var src) = {} /\
    key_taint (if tr then Ts.t_trans else Ts.t_stor) w = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (if tr then tload w s else sload w s) /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta)
    (if tr then TLOAD else SLOAD) [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (if tr then tload w s else sload w s) s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by
    (Cases_on `tr` >> gvs[Abbr `ins`]) >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_slot_header_operand_step >> simp[eval_operand_def] >> metis_tac[]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule scalar_storage_load_taint >> simp[eval_operand_def, update_var_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    (Cases_on `tr` >> simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
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
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       (Cases_on `tr` >> simp[Abbr `ins`, mk_inst_def]) >>
     membership_nowrap_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK (u with vs_inst_idx := 3+delta),g,tn) /\
    allocas_from lo u` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
       (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
     disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac) >>
  `membership_loop_frame sa G0 T0 s0 g tn
      (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_code_read_joint_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) /\
  w2n w <= LENGTH s.vs_data_section /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint Ts (Var src) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME value /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta) DLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst value s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_code_header_operand_step >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`, step_taint_def,
      set_var_taint_def, mk_inst_def, out_taint_def, update_var_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      new_site_bytes_def, FLOOKUP_DEF, range_bytes_def,
      taint_component_equality, DRESTRICT_UNIV, pred_setTheory.EXTENSION,
      SF CONJ_ss, eval_operand_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
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
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       simp[Abbr `ins`, mk_inst_def] >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac >>
  strip_tac >>
  `membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_memory_read_joint_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ ptr_covers Gs Ts src s 32 /\
    mem_word_taint Ts.t_mem (w2n w) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (mload (w2n w) s) /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+8+delta) MLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (mload (w2n w) s) s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u` by
    (asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, step_inst_base_opcode_eqs,
      mk_inst_def, instruction_accessors, instruction_accfupds,
      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`] >> irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[Abbr `u`, update_var_def]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule bodyPtrBopInLoadRunTheory.readonly_load_taint >> simp[eval_operand_def, update_var_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
    simp[inst_seq_ptr_def, Abbr `g`] >>
  `run_inst_seq_mem_ok [ins] s` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_def, Abbr `ins`,
      below_frontier_MLOAD, inst_dload_in_section_def, mk_inst_def,
      eval_operand_def] >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
    ins.inst_opcode <> ALLOCA /\ ins.inst_opcode <> GAS` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  `isPREFIX [ins] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule bodyMemAssignTopCopyPathsTheory.topcopy_instruction_prefix >> simp[] >> metis_tac[]) >>
  `run_inst_seq [ins] s = OK u` by simp[run_inst_seq_def] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       simp[Abbr `ins`, mk_inst_def] >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac >>
  strip_tac >>
  `membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_slot_read_joint_bounded_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint Ts (Var src) = {} /\
    key_taint (if tr then Ts.t_trans else Ts.t_stor) w = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (if tr then tload w s else sload w s) /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta)
    (if tr then TLOAD else SLOAD) [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (if tr then tload w s else sload w s) s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by
    (Cases_on `tr` >> gvs[Abbr `ins`]) >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_slot_header_operand_step >> simp[eval_operand_def] >> metis_tac[]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule scalar_storage_load_taint >> simp[eval_operand_def, update_var_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    (Cases_on `tr` >> simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
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
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       (Cases_on `tr` >> simp[Abbr `ins`, mk_inst_def]) >>
     membership_nowrap_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK (u with vs_inst_idx := 3+delta),g,tn) /\
    allocas_from lo u` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
       (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
     disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac) >>
  `membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_code_read_joint_bounded_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) /\
  w2n w <= LENGTH s.vs_data_section /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ op_taint Ts (Var src) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME value /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta) DLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst value s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u /\ ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`, Abbr `u`] >>
     irule bodyPtrBopInBaseBoundaryTheory.membership_code_header_operand_step >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`, step_taint_def,
      set_var_taint_def, mk_inst_def, out_taint_def, update_var_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      new_site_bytes_def, FLOOKUP_DEF, range_bytes_def,
      taint_component_equality, DRESTRICT_UNIV, pred_setTheory.EXTENSION,
      SF CONJ_ss, eval_operand_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
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
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       simp[Abbr `ins`, mk_inst_def] >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac >>
  strip_tac >>
  `membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_memory_read_joint_bounded_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  delta = (if 0 < skip then 1 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 2+delta /\
    lookup_var src s = SOME w /\ ptr_covers Gs Ts src s 32 /\
    mem_word_taint Ts.t_mem (w2n w) = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (mload (w2n w) s) /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  qabbrev_tac `ins = mk_inst (sa.cs_next_id+11+delta) MLOAD [Var src] [dst]` >>
  qabbrev_tac `u = update_var dst (mload (w2n w) s) s` >>
  qabbrev_tac `g = step_prov PG Gs ins u` >>
  qabbrev_tac `tn = Ts with t_var := Ts.t_var |+ (dst,{})` >>
  qexistsl_tac [`u with vs_inst_idx := 3+delta`, `g`, `tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK u` by
    (asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, step_inst_base_opcode_eqs,
      mk_inst_def, instruction_accessors, instruction_accfupds,
      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok (DF H) 0 0 ctx fn Gs Ts ins s` by
    (simp[Abbr `ins`] >> irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[Abbr `u`, update_var_def]) >>
  `step_taint ins s u Ts = tn` by
    (simp[Abbr `ins`, Abbr `u`, Abbr `tn`] >>
     irule bodyPtrBopInLoadRunTheory.readonly_load_taint >> simp[eval_operand_def, update_var_def]) >>
  `FLOOKUP g dst = NONE /\
   (!x. x <> dst ==> FLOOKUP g x = FLOOKUP Gs x /\
      op_taint tn (Var x) = op_taint Ts (Var x))` by
    simp[Abbr `g`, Abbr `ins`, Abbr `u`, Abbr `tn`,
      bodyPtrBopInLoadOutputTheory.scalar_load_output_prov,
      scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts [ins] s g tn` by
    simp[inst_seq_ptr_def, Abbr `g`] >>
  `run_inst_seq_mem_ok [ins] s` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_def, Abbr `ins`,
      below_frontier_MLOAD, inst_dload_in_section_def, mk_inst_def,
      eval_operand_def] >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
    ins.inst_opcode <> ALLOCA /\ ins.inst_opcode <> GAS` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  `isPREFIX [ins] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule bodyMemAssignTopCopyPathsTheory.topcopy_instruction_prefix >> simp[] >> metis_tac[]) >>
  `run_inst_seq [ins] s = OK u` by simp[run_inst_seq_def] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) [ins]` by
       simp[Abbr `ins`, mk_inst_def] >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp_membership_nowrap_tac >>
  strip_tac >>
  `membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_frame_scalar_update >>
     conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tn`]) >>
  `membership_loop_registers sa i r g tn (u with vs_inst_idx := 3+delta)` by
    (simp[Abbr `u`] >> irule membership_registers_scalar_update >> simp[] >>
     qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >> gvs[] >>
  simp[Abbr `u`, Abbr `tn`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED

Theorem rest_word_membership_runtime_address_operand_joint_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint T0 arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP Gt dst = op_prov G0 arr /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_operational >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >> simp[] >> strip_tac >>
  qabbrev_tac `ins1 = mk_inst (sa.cs_next_id+6) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]` >>
  qabbrev_tac `u1 = update_var product (n2w i * n2w stride) s` >>
  qabbrev_tac `g1 = step_prov PG Gs ins1 u1` >>
  qabbrev_tac `t1 = step_taint ins1 s u1 Ts` >>
  qabbrev_tac `v1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `ins2 = mk_inst (sa.cs_next_id+7) ADD
    [Lit (n2w skip);Var product] [offset]` >>
  qabbrev_tac `u2 = update_var offset (n2w skip + n2w i * n2w stride) v1` >>
  qabbrev_tac `g2 = if 0 < skip then step_prov PG g1 ins2 u2 else g1` >>
  qabbrev_tac `t2 = if 0 < skip then step_taint ins2 v1 u2 t1 else t1` >>
  qabbrev_tac `v2 = if 0 < skip then
    u2 with vs_inst_idx := SUC v1.vs_inst_idx else v1` >>
  qabbrev_tac `last = mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [dst]` >>
  qabbrev_tac `u3 = update_var dst (bw+n2w (skip+stride*i)) v2` >>
  qabbrev_tac `g3 = step_prov PG g2 last u3` >>
  qabbrev_tac `t3 = step_taint last v2 u3 t2` >>
  qexistsl_tac [`case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s`, `g3`, `t3`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}` by
    (irule rest_word_membership_runtime_prefix_checked_operand >>
     simp[Abbr `ins1`, Abbr `ins2`, Abbr `last`] >>
     Cases_on `0 < skip` >> gvs[] >> metis_tac[]) >>
  `eval_operand arr s = SOME bw` by
    (qpat_assum `membership_loop_frame _ _ _ _ Gs Ts s`
       (mp_then Any mp_tac membership_loop_frame_operand) >> simp[]) >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `gf = g3 /\ tf = t3` by suspend "ghosts" >>
  qpat_x_assum `gf = g3` SUBST_ALL_TAC >>
  qpat_x_assum `tf = t3` SUBST_ALL_TAC >>
  qunabbrev_tac `ins1` >> qunabbrev_tac `ins2` >> qunabbrev_tac `last` >>
  `?v. run_inst_seq code s = OK v /\ (v with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `!s i bw. _` (qspecl_then [`s`, `i`, `bw`] mp_tac) >>
     simp[] >> strip_tac >> Cases_on `0 < skip` >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. code = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) code` by
       (Cases_on `0 < skip` >> simp[mk_inst_def]) >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  simp_membership_nowrap_tac >> strip_tac >>
  Cases_on `0 < skip` >> gvs[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >> metis_tac[]
QED

Resume rest_word_membership_runtime_address_operand_joint_const[ghosts]:
  `!k w v. sa.cs_next_var <= k ==> eval_operand arr
     (update_var (STRING #"%" (toString k)) w v) = eval_operand arr v` by
    (rpt strip_tac >>
     irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `eval_operand arr u1 = SOME bw` by simp[Abbr `u1`] >>
  `eval_operand arr v1 = SOME bw` by simp[Abbr `v1`] >>
  `eval_operand arr u2 = SOME bw` by simp[Abbr `u2`] >>
  `eval_operand arr v2 = SOME bw` by
    (Cases_on `0 < skip` >> simp[Abbr `v2`]) >>
  fs[lookup_var_def] >>
  Cases_on `0 < skip` >>
  fs[Abbr `u1`, Abbr `u2`, Abbr `v1`, Abbr `v2`, update_var_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  unabbrev_all_tac >> fs[] >>
  simp[inst_seq_ptr_def,
    step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    GSYM word_add_n2w, GSYM word_mul_n2w, arithmeticTheory.MULT_COMM] >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `step_taint _ _ _ ts` >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, mk_inst_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def]
QED

Finalise rest_word_membership_runtime_address_operand_joint_const

Theorem rest_word_membership_header_joint_const:
  vv_location vv = SOME loc /\ (~cenv.ce_is_ctor \/ loc <> LocCode) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!H:'h. guard H ==> ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand (vv_operand vv) s = SOME w /\ op_taint TF (vv_operand vv) = {} /\
    (case loc of
       LocMemory =>
         (?x. vv_operand vv = Var x /\ ptr_covers G TF x s 32) /\
         w2n w + 32 <= s.vs_alloca_next /\ mem_word_taint TF.t_mem (w2n w) = {} /\
         mload (w2n w) s = n2w n
     | LocStorage => key_taint TF.t_stor w = {} /\ sload w s = n2w n
     | LocTransient => key_taint TF.t_trans w = {} /\ tload w s = n2w n
     | LocCode => w2n w <= LENGTH s.vs_data_section /\
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) = n2w n
     | _ => F)) ==>
  ?len sm t GF TFF.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sm = (op,sb) /\
    (!H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,TF) [] (OK t,GF,TFF) /\
      membership_loop_frame sa G TF s GF TFF t /\
      eval_operand len t = SOME (n2w n) /\ op_prov GF len = NONE /\ op_taint TFF len = {} /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_var_array_membership_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_array_membership_loop _ _ len _ _ _ _ _ sm = _` >>
  `fn_has_code sa sm fn` by
    (irule (cj 1 fn_has_code_split) >> conj_tac
     >- metis_tac[first_emission_ptr_load] >>
     qexists_tac `sb` >> simp[] >> metis_tac[membership_bounded_loop_extends]) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
     compile_ptr_load F cenv.ce_imm_alloca loc` by
    (Cases_on `loc` >> gvs[FUN_EQ_THM, contextTheory.compile_ptr_load_def,
       contextTheory.compile_imm_load_word_def]) >>
  `compile_ptr_load F cenv.ce_imm_alloca loc (vv_operand vv) sa = (len,sm)` by metis_tac[] >>
  drule_all membership_length_header_code >> strip_tac >>
  drule membership_length_header_layout >>
  disch_then (qspec_then `(case loc of LocMemory => MLOAD | LocStorage => SLOAD |
    LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  qabbrev_tac `dst = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id
    (case loc of LocMemory => MLOAD | LocStorage => SLOAD | LocTransient => TLOAD |
      LocCalldata => CALLDATALOAD | LocCode => DLOAD) [vv_operand vv] [dst]` >>
  qabbrev_tac `u = update_var dst (n2w n) s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G ins u`, `step_taint ins s u TF`] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `step_inst_base ins s = OK u` by
    (Cases_on `loc` >>
     asm_simp_tac bool_ss [Abbr `ins`, Abbr `u`, mk_inst_def,
       step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     gvs[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx fn G TF ins s` by suspend "checks" >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,fn,PG) (s,G,TF) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G ins u, step_taint ins s u TF)` by suspend "edge" >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]) >>
  suspend "post"
QED

Resume rest_word_membership_header_joint_const[checks]:
  markerLib.RESUME_TAC >>
  Cases_on `loc` >> gvs[Abbr `ins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    memLocDefsTheory.mem_read_ops_def, step_inst_non_invoke, Abbr `u`, update_var_def,
    allocas_from_def] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, eval_operand_def] >> first_assum ACCEPT_TAC
QED

Resume rest_word_membership_header_joint_const[edge]:
  markerLib.RESUME_TAC >>
  `ins.inst_opcode <> GAS /\ ins.inst_opcode <> INVOKE /\
   ~is_terminator ins.inst_opcode /\
   inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
    (Cases_on `loc` >> gvs[Abbr `ins`, mk_inst_def, is_terminator_def,
      unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME ins` by simp[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    unitTransformDefs$dalloca_no_wrap ins s)` by
    (strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     Cases_on `loc` >> simp[Abbr `ins`, mk_inst_def]) >>
  drule_all straight_line_origin_ptr_edge >> simp[]
QED

Resume rest_word_membership_header_joint_const[post]:
  markerLib.RESUME_TAC >> gvs[]
  >>~- ([`gas_origin_ptr_path _ _ _ _`],
    `~(u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)).vs_halted` by
      simp[Abbr `u`, update_var_def] >>
    drule (cj 2 gas_origin_ptr_path_rules) >>
    disch_then (qspec_then `[]` mp_tac) >> simp[] >>
    disch_then match_mp_tac >>
    irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  simp[Abbr `ins`, Abbr `u`, membership_loop_frame_def,
    step_taint_def, set_var_taint_def, out_taint_def,
    step_prov_def, set_prov_def, out_prov_def, op_prov_def,
    mk_inst_def, update_var_def, eval_operand_def, lookup_var_def,
    op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, allocas_from_def] >>
  simp[mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    new_site_bytes_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
    venom_state_component_equality] >>
  rpt conj_tac >> gvs[allocas_from_def, FLOOKUP_DEF] >>
  qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst` by
    gvs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`, stringTheory.STRCAT_EQNS] >>
  simp[]
QED

Finalise rest_word_membership_header_joint_const


Theorem rest_word_membership_runtime_address_operand_joint_bounded_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  product = "%" ++ toString (sa.cs_next_var+5) /\
  delta = (if 0 < skip then 1 else 0) /\
  offset = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  code = [mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+10) ADD
      [Lit (n2w skip);Var product] [offset]] else []) ++
    [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]] /\
  A = {"%" ++ toString (sa.cs_next_var+1)} UNION
    (case arr of Var x => {x} | _ => {}) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  (!H:'h. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i r Gs Ts s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
    op_taint T0 arr = {}) ==>
  ?t Gt Tt. !H:'h. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i r Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP Gt dst = op_prov G0 arr /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  drule rest_word_membership_runtime_prefix_operational_bounded >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `code = _`)) >> simp[] >> strip_tac >>
  qabbrev_tac `ins1 = mk_inst (sa.cs_next_id+9) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [product]` >>
  qabbrev_tac `u1 = update_var product (n2w i * n2w stride) s` >>
  qabbrev_tac `g1 = step_prov PG Gs ins1 u1` >>
  qabbrev_tac `t1 = step_taint ins1 s u1 Ts` >>
  qabbrev_tac `v1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `ins2 = mk_inst (sa.cs_next_id+10) ADD
    [Lit (n2w skip);Var product] [offset]` >>
  qabbrev_tac `u2 = update_var offset (n2w skip + n2w i * n2w stride) v1` >>
  qabbrev_tac `g2 = if 0 < skip then step_prov PG g1 ins2 u2 else g1` >>
  qabbrev_tac `t2 = if 0 < skip then step_taint ins2 v1 u2 t1 else t1` >>
  qabbrev_tac `v2 = if 0 < skip then
    u2 with vs_inst_idx := SUC v1.vs_inst_idx else v1` >>
  qabbrev_tac `last = mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [dst]` >>
  qabbrev_tac `u3 = update_var dst (bw+n2w (skip+stride*i)) v2` >>
  qabbrev_tac `g3 = step_prov PG g2 last u3` >>
  qabbrev_tac `t3 = step_taint last v2 u3 t2` >>
  qexistsl_tac [`case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta | _ => s`, `g3`, `t3`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u gf tf. run_inst_seq code s = OK u /\
    lookup_var dst u = SOME (bw+n2w (skip+stride*i)) /\
    inst_seq_ptr (DF H) 0 ctx fn PG Gs Ts code s gf tf /\
    membership_loop_frame sa G0 T0 s0 gf tf u /\
    membership_loop_registers sa i r gf tf u /\
    FLOOKUP gf dst = op_prov G0 arr /\ op_taint tf (Var dst) = {}` by
    (irule rest_word_membership_runtime_prefix_checked_operand_bounded >>
     simp[Abbr `ins1`, Abbr `ins2`, Abbr `last`] >>
     Cases_on `0 < skip` >> gvs[] >> metis_tac[]) >>
  `eval_operand arr s = SOME bw` by
    (qpat_assum `membership_loop_frame _ _ _ _ Gs Ts s`
       (mp_then Any mp_tac membership_loop_frame_operand) >> simp[]) >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i)` by
    gvs[membership_loop_registers_def] >>
  `gf = g3 /\ tf = t3` by suspend "ghosts" >>
  qpat_x_assum `gf = g3` SUBST_ALL_TAC >>
  qpat_x_assum `tf = t3` SUBST_ALL_TAC >>
  qunabbrev_tac `ins1` >> qunabbrev_tac `ins2` >> qunabbrev_tac `last` >>
  `?v. run_inst_seq code s = OK v /\ (v with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `!s i bw. _` (qspecl_then [`s`, `i`, `bw`] mp_tac) >>
     simp[] >> strip_tac >> Cases_on `0 < skip` >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `0 < skip` >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post v. code = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) code` by
       (Cases_on `0 < skip` >> simp[mk_inst_def]) >>
     membership_nowrap_tac) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL run_inst_seq_origin_ptr_lift) >> simp[] >>
  disch_then (qspecl_then [`lo`, `explicit`] mp_tac) >>
  simp_membership_nowrap_tac >> strip_tac >>
  Cases_on `0 < skip` >> gvs[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (gvs[membership_loop_frame_def, venom_state_component_equality,
         lookup_var_def] >> metis_tac[]) >>
  gvs[membership_loop_registers_def, lookup_var_def, op_taint_def,
      op_prov_def, allocas_from_def] >>
  gvs[] >>
  gvs[membership_loop_frame_def, venom_state_component_equality,
      lookup_var_def] >> gvs[] >> metis_tac[]
QED

Resume rest_word_membership_runtime_address_operand_joint_bounded_const[ghosts]:
  `!k w v. sa.cs_next_var <= k ==> eval_operand arr
     (update_var (STRING #"%" (toString k)) w v) = eval_operand arr v` by
    (rpt strip_tac >>
     irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `eval_operand arr u1 = SOME bw` by simp[Abbr `u1`] >>
  `eval_operand arr v1 = SOME bw` by simp[Abbr `v1`] >>
  `eval_operand arr u2 = SOME bw` by simp[Abbr `u2`] >>
  `eval_operand arr v2 = SOME bw` by
    (Cases_on `0 < skip` >> simp[Abbr `v2`]) >>
  fs[lookup_var_def] >>
  Cases_on `0 < skip` >>
  fs[Abbr `u1`, Abbr `u2`, Abbr `v1`, Abbr `v2`, update_var_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  unabbrev_all_tac >> fs[] >>
  simp[inst_seq_ptr_def,
    step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    GSYM word_add_n2w, GSYM word_mul_n2w, arithmeticTheory.MULT_COMM] >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `step_taint _ _ _ ts` >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, mk_inst_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def]
QED

Finalise rest_word_membership_runtime_address_operand_joint_bounded_const
