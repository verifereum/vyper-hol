(* Operational member navigation for arbitrary calldata. *)
Theory calldataMembers
Ancestors
  valueEncodingDefs loweringStateRelDefs calldataChildFrame valueEncodingProps abiDecoderReentry calldataDynOwned safeSequence fragExecMem abiDecoderMemberBound abiDecoderReservation
  abiDecoderBytesBound abiDecoderGuards abiDecoderRange calldataWordLeaf abiDecoderClampedWord
  abiDecoderAppend fragExec abiDecoderFrameCompose
  abiDecoderComposition abiDecoderContract abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper venomExecSemantics venomState
  venomInst words arithmetic list rich_list

Theorem calldata_member_pointer_sequence:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) st = (ep,mid) /\
  eval_operand src s = SOME p /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st mid) s = OK t /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
       else p + n2w ao) /\
    fresh_vars_wrt mid t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st mid
Proof
  strip_tac >> Cases_on `dyn`
  >- (`abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
      `eval_operand src s = SOME (n2w (w2n p))` by simp[] >>
      `abi_decode_load CALLDATALOAD (n2w (w2n p + ao) : bytes32) s =
       n2w (w2n (abi_decode_load CALLDATALOAD (p + n2w ao) s))` by
        simp[GSYM word_add_n2w] >>
      drule_all abi_decode_dynamic_member_pointer_sentinel >>
      simp[GSYM word_add_n2w]) >>
  `eval_operand src s = SOME (n2w (w2n p))` by simp[] >>
  drule_all abi_decode_static_member_pointer >> simp[GSYM word_add_n2w]
QED

Theorem calldata_member_address_shape:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) ==>
  inst_extends st mid /\ mid.cs_blocks = st.cs_blocks /\
  mid.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode /\ (!s. inst_mem_below_frontier i s) /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st mid)
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem calldata_member_address_sequence:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME q /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st mid) s = OK t /\
    eval_operand dp t = SOME (q + n2w vo) /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
       else p + n2w ao) /\ fresh_vars_wrt mid t /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) st = (ep,c1)` >>
  drule_all calldata_member_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME q` by metis_tac[] >>
  `eval_operand (Lit (n2w vo)) s1 = SOME (n2w vo)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem calldata_member_address_frag_mem:
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME q /\
  fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st mid (\s. s = initial)
    (\t. eval_operand dp t = SOME (q + n2w vo) /\
      eval_operand ep t = SOME
        (if dec_info_needs_offset ei then
           p + abi_decode_load CALLDATALOAD (p + n2w ao) initial
         else p + n2w ao) /\ fresh_vars_wrt mid t /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w))
    (K F)
Proof
  strip_tac >> drule calldata_member_address_shape >> strip_tac >>
  drule_all calldata_member_address_sequence >> strip_tac >>
  `t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists_tac `emitted_insts st mid` >> simp[] >> fs[EVERY_MEM]) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
  fs[inst_extends_def, fresh_vars_wrt_def,
     instIdxIndepTheory.eval_op_inst_idx, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem calldata_members_cons_split[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    ((ei,az,mz)::rest) ao vo st = ((),final) ==>
  ?mid.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) st = ((),mid) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      rest (ao+az) (vo+mz) mid = ((),final)
Proof
  simp[Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_members_invariant_rule:
  !dst src ctx I R.
  (!ei az mz rest ao vo st mid.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) st = ((),mid) ==>
    cs_extends st mid /\
    frag_exec_mem ctx st mid (I ((ei,az,mz)::rest) ao vo st)
      (I rest (ao+az) (vo+mz) mid) R) /\
  (!xs ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) ==>
  !xs ao vo st final.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo st = ((),final) ==>
    frag_exec_mem ctx st final (I xs ao vo st)
      (I [] (ao + SUM (MAP (\(ei,az,mz). az) xs))
            (vo + SUM (MAP (\(ei,az,mz). mz) xs)) final) R
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> irule frag_exec_mem_refl >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  drule calldata_members_cons_split >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!ei az mz rest ao vo st mid. _` drule >>
  disch_then (qspecl_then [`h1`, `h2`, `xs`] strip_assume_tac) >>
  `cs_extends mid final` by metis_tac[] >>
  simp_tac pure_ss [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  irule frag_exec_mem_seq >>
  qexistsl_tac [`I' xs (ao+h1) (vo+h2) mid`, `mid`] >>
  asm_rewrite_tac[GSYM ADD_ASSOC]
QED

Theorem calldata_member_invariant_intro:
  !dst src ei ao vo st ep dp addr mid ctx I H R az mz rest.
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),addr) /\
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei addr = ((),mid) /\
  cs_extends st addr /\ cs_extends addr mid /\
  frag_exec_mem ctx st addr (I ((ei,az,mz)::rest) ao vo st) H R /\
  (!u. H u ==> frag_exec_mem ctx addr mid (\s. s = u)
    (I rest (ao+az) (vo+mz) mid) R) ==>
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) st = ((),mid) /\
  cs_extends st mid /\
  frag_exec_mem ctx st mid (I ((ei,az,mz)::rest) ao vo st)
    (I rest (ao+az) (vo+mz) mid) R
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `(do ep <- _; _ od) st = _` mp_tac >>
      simp[comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  irule frag_exec_mem_seq_pointwise >> qexistsl_tac [`H`, `addr`] >> simp[]
QED

Theorem calldata_unclamped_member_frag_mem:
  (do ep <- compile_getelemptr_abi src F ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord NoClamp) od)
    st = ((),mid) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d + vo + 32 < dimword (:256) /\ d + vo + 32 <= initial.vs_alloca_next /\
  fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st mid (\s. s = initial)
    (\t. mem_word_at (d+vo) t.vs_memory =
           abi_decode_load CALLDATALOAD (p + n2w ao) initial /\
      abi_decode_frame (d+vo) 32 initial t /\ fresh_vars_wrt mid t /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w)) (K F)
Proof
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] st = (ep,c1)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] c1 = (dp,c2)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset (DecPrimWord NoClamp)) ao CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),c2)` by
    simp[dec_info_needs_offset_def, compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def] >>
  drule_all calldata_member_address_frag_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends st c2` by (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `cs_extends c2 mid` by (irule cs_extends_same_block >> simp[]) >>
  drule frag_exec_mem_seq_pointwise >> disch_then irule >> simp[] >>
  gen_tac >> strip_tac >> gvs[dec_info_needs_offset_def] >>
  `eval_operand dp t = SOME (n2w (d+vo))` by simp[GSYM word_add_n2w] >>
  `d+vo < dimword (:256)` by decide_tac >>
  `d+vo+32 <= t.vs_alloca_next` by simp[] >>
  `abi_clamp_ok NoClamp (abi_decode_load CALLDATALOAD (p+n2w ao) t)` by
    simp[entryDecodePropsTheory.abi_clamp_ok_def] >>
  drule_all calldata_word_accepted_frag_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
  simp[abi_decode_frame_def, abi_decode_load_def, abi_decode_source_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A bounded consumer audit: the invariant distinguishes its three suffixes. *)
Theorem calldata_two_word_invariant:
  !dst src ctx initial d p z k.
  d + 64 < dimword (:256) /\ d + 64 <= initial.vs_alloca_next /\
  (z+k <= d \/ d+64 <= z) ==>
  !xs ao vo st final.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo st = ((),final) ==>
    frag_exec_mem ctx st final
      (\s.
        ((xs = [(DecPrimWord NoClamp,32,32);(DecPrimWord NoClamp,32,32)] /\ ao=0 /\ vo=0) \/
         (xs = [(DecPrimWord NoClamp,32,32)] /\ ao=32 /\ vo=32) \/
         (xs = [] /\ ao=64 /\ vo=64)) /\
        eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
        fresh_vars_wrt st s /\ s.vs_call_ctx = initial.vs_call_ctx /\
        s.vs_allocas = initial.vs_allocas /\ s.vs_alloca_next = initial.vs_alloca_next /\
        (!op w. eval_operand op initial = SOME w ==> eval_operand op s = SOME w) /\
        (32 <= vo ==> mem_word_at d s.vs_memory = abi_decode_load CALLDATALOAD p initial) /\
        (64 <= vo ==> mem_word_at (d+32) s.vs_memory = abi_decode_load CALLDATALOAD (p+32w) initial) /\
        mem_bytes_at z k s.vs_memory = mem_bytes_at z k initial.vs_memory)
      (\s.
        (([] = [(DecPrimWord NoClamp,32,32);(DecPrimWord NoClamp,32,32)] /\
            ao + SUM (MAP (\(ei,az,mz). az) xs) = 0 /\
            vo + SUM (MAP (\(ei,az,mz). mz) xs) = 0) \/
         ([] = [(DecPrimWord NoClamp,32,32)] /\
            ao + SUM (MAP (\(ei,az,mz). az) xs) = 32 /\
            vo + SUM (MAP (\(ei,az,mz). mz) xs) = 32) \/
         (([] : (abi_dec_info # num # num) list) = [] /\ ao + SUM (MAP (\(ei,az,mz). az) xs) = 64 /\
            vo + SUM (MAP (\(ei,az,mz). mz) xs) = 64)) /\
        eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
        fresh_vars_wrt final s /\ s.vs_call_ctx = initial.vs_call_ctx /\
        s.vs_allocas = initial.vs_allocas /\ s.vs_alloca_next = initial.vs_alloca_next /\
        (!op w. eval_operand op initial = SOME w ==> eval_operand op s = SOME w) /\
        (32 <= vo + SUM (MAP (\(ei,az,mz). mz) xs) ==>
          mem_word_at d s.vs_memory = abi_decode_load CALLDATALOAD p initial) /\
        (64 <= vo + SUM (MAP (\(ei,az,mz). mz) xs) ==>
          mem_word_at (d+32) s.vs_memory = abi_decode_load CALLDATALOAD (p+32w) initial) /\
        mem_bytes_at z k s.vs_memory = mem_bytes_at z k initial.vs_memory) (K F)
Proof
  rpt gen_tac >> disch_tac >>
  qabbrev_tac `Inv = \xs ao vo st s.
    ((xs = [(DecPrimWord NoClamp,32,32);(DecPrimWord NoClamp,32,32)] /\ ao=0 /\ vo=0) \/
     (xs = [(DecPrimWord NoClamp,32,32)] /\ ao=32 /\ vo=32) \/
     (xs = [] /\ ao=64 /\ vo=64)) /\
    eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
    fresh_vars_wrt st s /\ s.vs_call_ctx = initial.vs_call_ctx /\
    s.vs_allocas = initial.vs_allocas /\ s.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. eval_operand op initial = SOME w ==> eval_operand op s = SOME w) /\
    (32 <= vo ==> mem_word_at d s.vs_memory = abi_decode_load CALLDATALOAD p initial) /\
    (64 <= vo ==> mem_word_at (d+32) s.vs_memory = abi_decode_load CALLDATALOAD (p+32w) initial) /\
    mem_bytes_at z k s.vs_memory = mem_bytes_at z k initial.vs_memory` >>
  qpat_assum `Abbrev (Inv = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac calldata_members_invariant_rule >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- suspend "step_extends" >>
      irule frag_exec_mem_pointwise >> gen_tac >>
      simp[Abbr `Inv`] >> strip_tac >> gvs[] >>
      gvs[dec_info_needs_offset_def] >>
      `d+0+32 < dimword (:256) /\ d+0+32 <= s0.vs_alloca_next /\
       d+32+32 < dimword (:256) /\ d+32+32 <= s0.vs_alloca_next` by decide_tac >>
      drule_all calldata_unclamped_member_frag_mem >>
      disch_then (qspec_then `ctx` assume_tac) >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
      gen_tac >> strip_tac >>
      `s.vs_call_ctx = initial.vs_call_ctx` by fs[abi_decode_frame_def] >>
      `mem_bytes_at z k s.vs_memory = mem_bytes_at z k s0.vs_memory` by
        (irule abi_decode_frame_bytes >> goal_assum (drule_at Any) >> decide_tac) >>
      simp[abi_decode_load_def, abi_decode_source_def, WORD_ADD_0] >>
      drule abi_decode_frame_mem_word >> simp[] >> strip_tac >>
      fs[abi_decode_load_def, abi_decode_source_def]) >>
  suspend "tail_extends"
QED

Resume calldata_two_word_invariant[step_extends]:
  qpat_x_assum `(do ep <- _; _ od) st = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_abi_member_pointer) >>
  imp_res_tac (SRULE [cs_appends_def] (cj 1 cs_appends_abi_decode_mutual)) >>
  `cs_appends (emit_op ADD [dst; Lit (n2w vo)])` by simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >> metis_tac[cs_extends_trans]
QED
Resume calldata_two_word_invariant[tail_extends]:
  rpt strip_tac >>
  mp_tac (SRULE [cs_appends_def] (cj 2 cs_appends_abi_decode_mutual)) >>
  disch_then drule >> simp[]
QED
Finalise calldata_two_word_invariant

Theorem calldata_two_word_frag_mem:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    [(DecPrimWord NoClamp,32,32);(DecPrimWord NoClamp,32,32)] 0 0 st = ((),final) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  fresh_vars_wrt st initial /\
  d+64 < dimword (:256) /\ d+64 <= initial.vs_alloca_next /\
  (z+k <= d \/ d+64 <= z) ==>
  frag_exec_mem ctx st final (\s. s = initial)
    (\t. mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_word_at (d+32) t.vs_memory = abi_decode_load CALLDATALOAD (p+32w) initial /\
      mem_bytes_at z k t.vs_memory = mem_bytes_at z k initial.vs_memory /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      t.vs_call_ctx = initial.vs_call_ctx /\ fresh_vars_wrt final t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w)) (K F)
Proof
  strip_tac >>
  qspecl_then [`dst`, `src`, `ctx`, `initial`] mp_tac calldata_two_word_invariant >>
  disch_then (qspecl_then [`d`, `p`, `z`, `k`] mp_tac) >>
  simp[LET_THM] >> disch_then drule >> strip_tac >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]
QED

(* Reentrant member navigation preserves older live operands, not arbitrary
   stale registers which the generated code is allowed to overwrite. *)
Theorem calldata_member_pointer_repeat:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) st = (ep,mid) /\
  eval_operand src s = SOME p /\ abi_decoder_operand_live st.cs_next_var src ==>
  ?t. run_inst_seq (emitted_insts st mid) s = OK t /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
       else p + n2w ao) /\
    abi_decoder_operand_live mid.cs_next_var ep /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st mid /\
    st.cs_next_var <= mid.cs_next_var
Proof
  Cases_on `dyn`
  >- (simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      rename1 `emit_op ADD [src; Lit (n2w ao)] st = (head,c1)` >>
      rename1 `emit_op CALLDATALOAD [head] c1 = (off,c2)` >>
      pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      imp_res_tac emitted_insts_emit_op >>
      imp_res_tac abi_decoder_operand_live_emit >>
      `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
      drule_all (SIMP_RULE (srw_ss()) []
        (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
      drule_all calldata_read_repeat >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
      `eval_operand src s2 = SOME p` by
        (`abi_decoder_operand_live c1.cs_next_var src` by
          (irule abi_decoder_operand_live_mono >>
           qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
      drule_all (SIMP_RULE (srw_ss()) []
        (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts c2 mid) s2 = OK t` >>
      `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
        (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
      `run_inst_seq (emitted_insts st mid) s = OK t /\ inst_extends st mid` by
        (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
      `!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s` by
        (rpt strip_tac >>
         `abi_decoder_operand_live c1.cs_next_var op /\
          abi_decoder_operand_live c2.cs_next_var op` by
          (conj_tac >> irule abi_decoder_operand_live_mono >>
           qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
      qexists_tac `t` >>
      gvs[abi_decode_load_def, abi_decode_source_def, update_var_def]) >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_member_address_repeat:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME q /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st mid) s = OK t /\
    eval_operand dp t = SOME (q + n2w vo) /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
       else p + n2w ao) /\
    abi_decoder_operand_live mid.cs_next_var ep /\
    abi_decoder_operand_live mid.cs_next_var dp /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st mid /\
    st.cs_next_var <= mid.cs_next_var
Proof
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) st = (ep,c1)` >>
  drule_all calldata_member_pointer_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME q` by metis_tac[] >>
  `eval_operand (Lit (n2w vo)) s1 = SOME (n2w vo)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 mid) s1 = OK t` >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  `abi_decoder_operand_live mid.cs_next_var ep` by
    (irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> imp_res_tac emitted_insts_emit_op >> simp[]) >>
  `run_inst_seq (emitted_insts st mid) s = OK t /\ inst_extends st mid` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
        simp[]) >> metis_tac[]) >>
  imp_res_tac emitted_insts_emit_op >>
  qexists_tac `t` >> simp[]
QED

Theorem calldata_member_address_repeat_frag_mem:
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME q /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  frag_exec_mem ctx st mid (\s. s = initial)
    (\t. eval_operand dp t = SOME (q + n2w vo) /\
      eval_operand ep t = SOME
        (if dec_info_needs_offset ei then
           p + abi_decode_load CALLDATALOAD (p + n2w ao) initial
         else p + n2w ao) /\
      abi_decoder_operand_live mid.cs_next_var ep /\
      abi_decoder_operand_live mid.cs_next_var dp /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial)) (K F)
Proof
  strip_tac >> drule calldata_member_address_shape >> strip_tac >>
  drule_all calldata_member_address_repeat >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
  fs[inst_extends_def, instIdxIndepTheory.eval_op_inst_idx, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* A completed member is protected by its containing output allocation,
   including from later decoder scratch writes. *)
Theorem calldata_member_value_preserved:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= p /\ p+type_memory_size tv <= base_addr+cap /\
  (p+type_memory_size tv <= d \/ d+sz <= p) /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  val_wf tv x /\ val_in_memory tv x p s.vs_memory ==>
  val_in_memory tv x p t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at p (type_memory_size tv) t.vs_memory =
   mem_bytes_at p (type_memory_size tv) s.vs_memory` by
    (irule (cj 2 calldata_child_preserves_allocated_region) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`,`s.vs_memory`] >> simp[]
QED

Theorem calldata_members_fixed_fn_invariant_rule:
  !ctx fn dst src I.
  (!xs ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!ei az mz rest ao vo a b s.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I ((ei,az,mz)::rest) ao vo a s ==>
    (?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s) \/
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\
      !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I xs ao vo a s ==>
    (?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s) \/
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      I [] (ao+SUM (MAP (\(ei,az,mz). az) xs))
           (vo+SUM (MAP (\(ei,az,mz). mz) xs)) b t /\
      !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  drule calldata_members_cons_split >> strip_tac >>
  `cs_extends a mid /\ cs_extends mid b` by metis_tac[] >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `!ei az mz rest ao vo a b s. _` drule >>
  disch_then (qspecl_then [`h1`,`h2`,`xs`,`s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  first_x_assum drule >>
  disch_then (qspec_then `t` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qpat_x_assum `!fuel r. _` drule >>
      simp[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `t'` >>
  simp_tac (srw_ss()) [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  metis_tac[]
QED

Theorem calldata_member_prefix_preserved:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  d <= base_addr+cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  EVERY (\(tv,x,p). base_addr <= p /\ p+type_memory_size tv <= d /\
    val_wf tv x /\ val_in_memory tv x p s.vs_memory) prefix ==>
  EVERY (\(tv,x,p). base_addr <= p /\ p+type_memory_size tv <= d /\
    val_wf tv x /\ val_in_memory tv x p t.vs_memory) prefix
Proof
  strip_tac >> fs[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  PairCases_on `e` >> gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
  simp[] >> irule calldata_member_value_preserved >>
  qpat_assum `abi_decode_footprint_frame _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
  qexistsl_tac [`lo`,`hi`] >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

(* Metadata is position-indexed, not keyed by potentially repeated triples. *)
Theorem calldata_members_owned_repeat:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao0 vo0 st = ((),final) /\
  fn_has_code st final fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d+vo0 /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  (!i. i < LENGTH xs ==> type_memory_size (ty_at i) <= (\(ei,az,mz). mz) (EL i xs)) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (ty_at i) <= base_addr+cap /\
      e+type_memory_size (ty_at i) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ Pred i x /\ val_wf (ty_at i) x /\
        val_in_memory (ty_at i) x e v.vs_memory /\
        (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
          ?fuel'. run_from fuel' ctx fn u = r /\
            (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
        v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
        alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        u.vs_alloca_next <= v.vs_alloca_next /\
        (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          FLOOKUP v.vs_allocas id = SOME (q,k)) /\
        (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
          FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
        (!op. abi_decoder_operand_live mid.cs_next_var op ==>
          eval_operand op v = eval_operand op u) /\
        abi_decode_footprint_frame ((e,type_memory_size (ty_at i))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ LENGTH vs = LENGTH xs /\
    (!i. i < LENGTH xs ==> Pred i (EL i vs) /\ val_wf (ty_at i) (EL i vs) /\
      val_in_memory (ty_at i) (EL i vs)
        (d+(vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) t.vs_memory) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame
      ((d+vo0,SUM (MAP (\(ei,az,mz). mz) xs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \l h s. !id q k.
    l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Wit = \l h s sc. !q k. MEM (q,k) sc ==>
    ?id. l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (Wit = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Back = \u v. !fuel r.
    run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn u = r /\
      (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)` >>
  qpat_assum `Abbrev (Back = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Reject = \u. ?fuel z.
    run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u` >>
  qpat_assum `Abbrev (Reject = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Frame = \a b u v e sz sc.
    v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    Own a.cs_next_id b.cs_next_id v /\ u.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < a.cs_next_id \/ b.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
    (!op. abi_decoder_operand_live a.cs_next_var op ==>
      eval_operand op v = eval_operand op u) /\
    abi_decode_footprint_frame ((e,sz)::sc) u v /\
    Wit a.cs_next_id b.cs_next_id v sc` >>
  qpat_assum `Abbrev (Frame = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `AZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). az) ys)` >>
  qpat_assum `Abbrev (AZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `MZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). mz) ys)` >>
  qpat_assum `Abbrev (MZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `A = \i. ao0 + AZ (TAKE i xs)` >>
  qabbrev_tac `V = \i. vo0 + MZ (TAKE i xs)` >>
  qpat_assum `Abbrev (A = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qpat_assum `Abbrev (V = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Inv = \rest ao vo a s. ?n vs scratch.
    n <= LENGTH xs /\ LENGTH vs = n /\ rest = DROP n xs /\ ao = A n /\ vo = V n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) rest ao vo a = ((),final) /\
    cs_extends st a /\ cs_extends a final /\ ci_mono st a /\ ci_mono a final /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live a.cs_next_var src /\
    abi_decoder_operand_live a.cs_next_var dst /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    Frame st final initial s (d+vo0) (MZ xs) scratch /\
    (!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
      val_in_memory (ty_at j) (EL j vs) (d+V j) s.vs_memory)` >>
  qspecl_then [`ctx`,`fn`,`dst`,`src`,`Inv`] mp_tac calldata_members_fixed_fn_invariant_rule >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> suspend "member_step")) >>
  disch_then (qspecl_then [`xs`,`ao0`,`vo0`,`st`,`final`,`initial`] mp_tac) >>
  (impl_tac >- (simp[] >> suspend "initial_invariant")) >>
  strip_tac
  >- (disj1_tac >> simp[Abbr `Reject`] >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `Inv [] _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  `LENGTH vs = LENGTH xs` by
    (qpat_x_assum `[] = DROP _ _` (mp_tac o SYM) >>
     pure_rewrite_tac [DROP_EQ_NIL] >> decide_tac) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >>
  simp[Abbr `Back`]
QED

Resume calldata_members_owned_repeat[initial_invariant]:
  simp_tac bool_ss [Abbr `Inv`] >>
  qexistsl_tac [`[]`,`[]`] >>
  simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`,
       Abbr `Frame`, Abbr `Wit`, cs_extends_refl,
       abiDecoderFrameTheory.abi_decode_footprint_frame_refl] >>
  `ci_mono st final` by
    (mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`xs`,`ao0`,`vo0`,`st`] mp_tac) >>
     simp[]) >>
  fs[ci_mono_def, ci_mono_refl, cs_extends_refl]
QED

Resume calldata_members_owned_repeat[member_step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  rename1 `LENGTH vs <= LENGTH xs` >>
  qabbrev_tac `n = LENGTH vs` >>
  `n < LENGTH xs` by
    (qpat_x_assum `_::rest = DROP _ _` mp_tac >>
     Cases_on `n = LENGTH xs` >> fs[Abbr `n`]) >>
  `EL n xs = (ei,az,mz)` by
    (drule HD_DROP >>
     qpat_x_assum `_::rest = DROP _ _` (fn th => rewrite_tac [GSYM th]) >>
     simp[]) >>
  drule calldata_members_cons_split >> strip_tac >> gnvs[] >>
  qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) _ = ((),_)` mp_tac >>
  simp_tac (srw_ss() ++ boolSimps.LET_ss) [comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w) a = (ep,c1)` >>
  rename1 `emit_op ADD [dst; Lit (n2w (V n))] c1 = (dp,addr)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w (V n))]; return (ep,dp) od) a = ((ep,dp),addr)` by
    simp[comp_bind_def, comp_return_def] >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a addr` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends addr b` by (drule cs_extends_abi_decode >> simp[]) >>
  `fn_has_code a addr fn /\ fn_has_code addr b fn` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all calldata_member_address_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [combinTheory.K_THM] >> strip_tac >>
  qmatch_asmsub_rename_tac `eval_operand dp u = SOME (n2w d + n2w (V n))` >>
  `alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
   Own st.cs_next_id final.cs_next_id s` by
    fs[Abbr `Frame`] >>
  `alloca_inv u /\ alloca_frontier_inv ctx fn site u` by
    (drule_all calldata_alloca_invariants_fields >> simp[]) >>
  `cs_extends st addr /\ cs_extends b final` by
    (conj_tac >- metis_tac[cs_extends_trans] >>
     qpat_assum `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ rest _ _ b = _`
       mp_tac >> metis_tac[]) >>
  `a.cs_next_id <= addr.cs_next_id /\ a.cs_next_var <= addr.cs_next_var` by
    (qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) a = ((ep,dp),addr)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `dec_info_needs_offset ei` >>
     simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `ci_mono addr b /\ ci_mono b final` by
    (conj_tac
     >- (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
         disch_then (qspecl_then [`dp`,`ep`,`CALLDATALOAD`,`Lit 0w`,`ei`,`addr`] mp_tac) >> simp[]) >>
     mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`rest`,`az + A n`,`mz + V n`,`b`] mp_tac) >> simp[]) >>
  `st.cs_next_id <= addr.cs_next_id /\ b.cs_next_id <= final.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `Own addr.cs_next_id b.cs_next_id u` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_x_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >>
     BETA_TAC >> rpt strip_tac >> rule_assum_tac BETA_RULE >>
     `st.cs_next_id <= id /\ id < final.cs_next_id` by decide_tac >>
     first_x_assum (qspecl_then [`id`,`q`,`k`] mp_tac) >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  `type_memory_size (ty_at n) <= mz` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `V n + mz <= vo0 + MZ xs /\ vo0 <= V n` by
    (`xs = TAKE n xs ++ (ei,az,mz)::rest` by metis_tac[TAKE_DROP] >>
     qpat_x_assum `xs = TAKE n xs ++ _` mp_tac >>
     simp_tac bool_ss [Abbr `V`, Abbr `MZ`] >>
     disch_then (fn th => once_rewrite_tac [th]) >>
     simp[MAP_APPEND, SUM_APPEND]) >>
  `base_addr <= d + V n /\
   d + V n + type_memory_size (ty_at n) <= base_addr + cap /\
   d + V n + type_memory_size (ty_at n) < dimword(:256)` by decide_tac >>
  `eval_operand dp u = SOME (n2w (d + V n))` by simp[word_add_n2w] >>
  `FLOOKUP u.vs_allocas oid = SOME (base_addr,cap)` by simp[] >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _` drule_all >>
  `Back s u` by simp[Abbr `Back`] >>
  strip_tac
  >- (disj1_tac >>
      qpat_x_assum `Reject u` mp_tac >>
      simp_tac bool_ss [Abbr `Reject`] >> strip_tac >>
      qpat_x_assum `Back s u` mp_tac >>
      simp_tac bool_ss [Abbr `Back`] >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >>
      qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`fuel'`,`z`] >> simp[]) >>
  `Back s v` by
    (qpat_x_assum `Back s u` mp_tac >>
     qpat_x_assum `Back u v` mp_tac >>
     simp_tac bool_ss [Abbr `Back`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `cs_extends st b /\ ci_mono st b` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `A (SUC n) = az + A n /\ V (SUC n) = mz + V n` by
    (simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`, TAKE_SUC, EL_TAKE,
          SUM_APPEND] >> decide_tac) >>
  `Frame st final initial v (d+vo0) (MZ xs) (scratch++sc)` by
    suspend "frame_merge" >>
  `!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
    val_in_memory (ty_at j) (EL j vs) (d+V j) v.vs_memory` by
    suspend "prefix_merge" >>
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   abi_decoder_operand_live b.cs_next_var src /\ abi_decoder_operand_live b.cs_next_var dst /\
   FLOOKUP v.vs_allocas oid = SOME (base_addr,cap)` by
    suspend "entry_merge" >>
  disj2_tac >> qexists_tac `v` >> simp[] >>
  qexistsl_tac [`vs++[x]`,`scratch++sc`] >>
  simp[LENGTH_APPEND, GSYM ADD1, Abbr `n`] >>
  conj_tac
  >- (qpat_x_assum `_::rest = DROP _ _` mp_tac >>
      rewrite_tac [DROP_SUC] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j < LENGTH vs`
  >- simp[EL_APPEND1] >>
  `j = LENGTH vs` by decide_tac >> simp[EL_APPEND2]

QED

Resume calldata_members_owned_repeat[entry_merge]:
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> strip_tac >>
  `a.cs_next_var <= b.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `abi_decoder_operand_live addr.cs_next_var src /\
   abi_decoder_operand_live addr.cs_next_var dst` by metis_tac[abi_decoder_operand_live_mono] >>
  `oid < addr.cs_next_id \/ b.cs_next_id <= oid` by decide_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED

Resume calldata_members_owned_repeat[frame_merge]:
  qpat_x_assum `Frame st final initial s _ _ _` mp_tac >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> ntac 2 strip_tac >>
  `Own st.cs_next_id final.cs_next_id v` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `Own addr.cs_next_id b.cs_next_id v` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
     BETA_TAC >> ntac 2 strip_tac >>
     ho_match_mp_tac (GEN_ALL calldata_owned_interval_replace) >>
     qexistsl_tac [`s`,`b.cs_next_id`,`addr.cs_next_id`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `ci_mono addr b` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >>
     qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < addr.cs_next_id \/ b.cs_next_id <= id` by decide_tac >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live a.cs_next_var op /\
       abi_decoder_operand_live addr.cs_next_var op` by
        (fs[ci_mono_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
      metis_tac[]) >>
  conj_tac >- suspend "footprint_merge" >>
  qpat_x_assum `Wit st.cs_next_id final.cs_next_id s scratch` mp_tac >>
  qpat_x_assum `Wit addr.cs_next_id b.cs_next_id v sc` mp_tac >>
  qpat_x_assum `!id q k. FLOOKUP u.vs_allocas id = _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
  qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
  qpat_x_assum `Abbrev (Wit = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
  BETA_TAC >> simp_tac bool_ss [MEM_APPEND] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Resume calldata_members_owned_repeat[footprint_merge]:
  `abi_decode_footprint_frame ((d+vo0,MZ xs)::scratch) initial u` by
    (qpat_x_assum `abi_decode_footprint_frame _ initial s` mp_tac >>
     simp[abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
  irule calldata_footprint_accumulate >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> decide_tac
QED

Resume calldata_members_owned_repeat[prefix_merge]:
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH xs /\ SUC j <= n` by decide_tac >>
  `type_memory_size (ty_at j) <= (\(ei,az,mz). mz) (EL j xs)` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `j` mp_tac) >> simp[]) >>
  `!i ys. MZ (TAKE i ys) <= MZ ys` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `MZ`] >>
     POP_ASSUM_LIST (K all_tac) >>
     CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV
       (REWR_CONV (GSYM (Q.SPECL [`i`,`ys`] TAKE_DROP))))) >>
     simp[MAP_APPEND, SUM_APPEND, MAP_TAKE]) >>
  `MZ (TAKE (SUC j) xs) <= MZ (TAKE n xs)` by
    (first_x_assum (qspecl_then [`SUC j`,`TAKE n xs`] mp_tac) >>
     simp[TAKE_TAKE, MIN_DEF]) >>
  `V j + type_memory_size (ty_at j) <= V n /\ vo0 <= V j` by
    (qpat_x_assum `MZ (TAKE (SUC j) xs) <= _` mp_tac >>
     simp[Abbr `V`, Abbr `MZ`, TAKE_SUC, EL_TAKE, SUM_APPEND] >> decide_tac) >>
  qpat_x_assum `!j. j < n ==> Pred j _ /\ _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`, Abbr `Wit`] >> strip_tac >>
  irule calldata_member_value_preserved >>
  simp_tac bool_ss [] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `abi_decode_footprint_frame _ u v` (irule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`oid`,`cap`,`base_addr`] >> simp[] >>
  qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise calldata_members_owned_repeat


(* Interval-aware companion; original theorem and proof are retained unchanged. *)
Theorem calldata_members_owned_repeat_intervals:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao0 vo0 st = ((),final) /\
  fn_has_code st final fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d+vo0 /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  (!i. i < LENGTH xs ==> type_memory_size (ty_at i) <= (\(ei,az,mz). mz) (EL i xs)) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (ty_at i) <= base_addr+cap /\
      e+type_memory_size (ty_at i) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ Pred i x /\ val_wf (ty_at i) x /\
        val_in_memory (ty_at i) x e v.vs_memory /\
        (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
          ?fuel'. run_from fuel' ctx fn u = r /\
            (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
        v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
        alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        u.vs_alloca_next <= v.vs_alloca_next /\
        (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          FLOOKUP v.vs_allocas id = SOME (q,k)) /\
        (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
          FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
        (!op. abi_decoder_operand_live mid.cs_next_var op ==>
          eval_operand op v = eval_operand op u) /\
        abi_decode_footprint_frame ((e,type_memory_size (ty_at i))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ LENGTH vs = LENGTH xs /\
    (!i. i < LENGTH xs ==> Pred i (EL i vs) /\ val_wf (ty_at i) (EL i vs) /\
      val_in_memory (ty_at i) (EL i vs)
        (d+(vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) t.vs_memory) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame
      ((d+vo0,SUM (MAP (\(ei,az,mz). mz) xs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \l h s. !id q k.
    l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Wit = \l h s sc. !q k. MEM (q,k) sc ==>
    ?id. l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (Wit = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Back = \u v. !fuel r.
    run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn u = r /\
      (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)` >>
  qpat_assum `Abbrev (Back = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Reject = \u. ?fuel z.
    run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u` >>
  qpat_assum `Abbrev (Reject = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Frame = \a b u v e sz sc.
    v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    Own a.cs_next_id b.cs_next_id v /\ u.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < a.cs_next_id \/ b.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
    (!op. abi_decoder_operand_live a.cs_next_var op ==>
      eval_operand op v = eval_operand op u) /\
    abi_decode_footprint_frame ((e,sz)::sc) u v /\
    Wit a.cs_next_id b.cs_next_id v sc` >>
  qpat_assum `Abbrev (Frame = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `AZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). az) ys)` >>
  qpat_assum `Abbrev (AZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `MZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). mz) ys)` >>
  qpat_assum `Abbrev (MZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `A = \i. ao0 + AZ (TAKE i xs)` >>
  qabbrev_tac `V = \i. vo0 + MZ (TAKE i xs)` >>
  qpat_assum `Abbrev (A = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qpat_assum `Abbrev (V = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Inv = \rest ao vo a s. ?n vs scratch.
    n <= LENGTH xs /\ LENGTH vs = n /\ rest = DROP n xs /\ ao = A n /\ vo = V n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) rest ao vo a = ((),final) /\
    cs_extends st a /\ cs_extends a final /\ ci_mono st a /\ ci_mono a final /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live a.cs_next_var src /\
    abi_decoder_operand_live a.cs_next_var dst /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    Frame st final initial s (d+vo0) (MZ xs) scratch /\
    (!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
      val_in_memory (ty_at j) (EL j vs) (d+V j) s.vs_memory)` >>
  qspecl_then [`ctx`,`fn`,`dst`,`src`,`Inv`] mp_tac calldata_members_fixed_fn_invariant_rule >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> suspend "member_step")) >>
  disch_then (qspecl_then [`xs`,`ao0`,`vo0`,`st`,`final`,`initial`] mp_tac) >>
  (impl_tac >- (simp[] >> suspend "initial_invariant")) >>
  strip_tac
  >- (disj1_tac >> simp[Abbr `Reject`] >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `Inv [] _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  `LENGTH vs = LENGTH xs` by
    (qpat_x_assum `[] = DROP _ _` (mp_tac o SYM) >>
     pure_rewrite_tac [DROP_EQ_NIL] >> decide_tac) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >>
  simp[Abbr `Back`]
QED

Resume calldata_members_owned_repeat_intervals[initial_invariant]:
  simp_tac bool_ss [Abbr `Inv`] >>
  qexistsl_tac [`[]`,`[]`] >>
  simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`,
       Abbr `Frame`, Abbr `Wit`, cs_extends_refl,
       abiDecoderFrameTheory.abi_decode_footprint_frame_refl] >>
  `ci_mono st final` by
    (mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`xs`,`ao0`,`vo0`,`st`] mp_tac) >>
     simp[]) >>
  fs[ci_mono_def, ci_mono_refl, cs_extends_refl]
QED

Resume calldata_members_owned_repeat_intervals[member_step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  rename1 `LENGTH vs <= LENGTH xs` >>
  qabbrev_tac `n = LENGTH vs` >>
  `n < LENGTH xs` by
    (qpat_x_assum `_::rest = DROP _ _` mp_tac >>
     Cases_on `n = LENGTH xs` >> fs[Abbr `n`]) >>
  `EL n xs = (ei,az,mz)` by
    (drule HD_DROP >>
     qpat_x_assum `_::rest = DROP _ _` (fn th => rewrite_tac [GSYM th]) >>
     simp[]) >>
  drule calldata_members_cons_split >> strip_tac >> gnvs[] >>
  qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) _ = ((),_)` mp_tac >>
  simp_tac (srw_ss() ++ boolSimps.LET_ss) [comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w) a = (ep,c1)` >>
  rename1 `emit_op ADD [dst; Lit (n2w (V n))] c1 = (dp,addr)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w (V n))]; return (ep,dp) od) a = ((ep,dp),addr)` by
    simp[comp_bind_def, comp_return_def] >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a addr` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends addr b` by (drule cs_extends_abi_decode >> simp[]) >>
  `fn_has_code a addr fn /\ fn_has_code addr b fn` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all calldata_member_address_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [combinTheory.K_THM] >> strip_tac >>
  qmatch_asmsub_rename_tac `eval_operand dp u = SOME (n2w d + n2w (V n))` >>
  `alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
   Own st.cs_next_id final.cs_next_id s` by
    fs[Abbr `Frame`] >>
  `alloca_inv u /\ alloca_frontier_inv ctx fn site u` by
    (drule_all calldata_alloca_invariants_fields >> simp[]) >>
  `cs_extends st addr /\ cs_extends b final` by
    (conj_tac >- metis_tac[cs_extends_trans] >>
     qpat_assum `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ rest _ _ b = _`
       mp_tac >> metis_tac[]) >>
  `a.cs_next_id <= addr.cs_next_id /\ a.cs_next_var <= addr.cs_next_var` by
    (qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) a = ((ep,dp),addr)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `dec_info_needs_offset ei` >>
     simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `ci_mono addr b /\ ci_mono b final` by
    (conj_tac
     >- (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
         disch_then (qspecl_then [`dp`,`ep`,`CALLDATALOAD`,`Lit 0w`,`ei`,`addr`] mp_tac) >> simp[]) >>
     mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`rest`,`az + A n`,`mz + V n`,`b`] mp_tac) >> simp[]) >>
  `st.cs_next_id <= addr.cs_next_id /\ b.cs_next_id <= final.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `Own addr.cs_next_id b.cs_next_id u` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_x_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >>
     BETA_TAC >> rpt strip_tac >> rule_assum_tac BETA_RULE >>
     `st.cs_next_id <= id /\ id < final.cs_next_id` by decide_tac >>
     first_x_assum (qspecl_then [`id`,`q`,`k`] mp_tac) >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  `type_memory_size (ty_at n) <= mz` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `V n + mz <= vo0 + MZ xs /\ vo0 <= V n` by
    (`xs = TAKE n xs ++ (ei,az,mz)::rest` by metis_tac[TAKE_DROP] >>
     qpat_x_assum `xs = TAKE n xs ++ _` mp_tac >>
     simp_tac bool_ss [Abbr `V`, Abbr `MZ`] >>
     disch_then (fn th => once_rewrite_tac [th]) >>
     simp[MAP_APPEND, SUM_APPEND]) >>
  `base_addr <= d + V n /\
   d + V n + type_memory_size (ty_at n) <= base_addr + cap /\
   d + V n + type_memory_size (ty_at n) < dimword(:256)` by decide_tac >>
  `eval_operand dp u = SOME (n2w (d + V n))` by simp[word_add_n2w] >>
  `FLOOKUP u.vs_allocas oid = SOME (base_addr,cap)` by simp[] >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _` drule_all >>
  `Back s u` by simp[Abbr `Back`] >>
  strip_tac
  >- (disj1_tac >>
      qpat_x_assum `Reject u` mp_tac >>
      simp_tac bool_ss [Abbr `Reject`] >> strip_tac >>
      qpat_x_assum `Back s u` mp_tac >>
      simp_tac bool_ss [Abbr `Back`] >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >>
      qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`fuel'`,`z`] >> simp[]) >>
  `Back s v` by
    (qpat_x_assum `Back s u` mp_tac >>
     qpat_x_assum `Back u v` mp_tac >>
     simp_tac bool_ss [Abbr `Back`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `cs_extends st b /\ ci_mono st b` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `A (SUC n) = az + A n /\ V (SUC n) = mz + V n` by
    (simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`, TAKE_SUC, EL_TAKE,
          SUM_APPEND] >> decide_tac) >>
  `Frame st final initial v (d+vo0) (MZ xs) (scratch++sc)` by
    suspend "frame_merge" >>
  `!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
    val_in_memory (ty_at j) (EL j vs) (d+V j) v.vs_memory` by
    suspend "prefix_merge" >>
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   abi_decoder_operand_live b.cs_next_var src /\ abi_decoder_operand_live b.cs_next_var dst /\
   FLOOKUP v.vs_allocas oid = SOME (base_addr,cap)` by
    suspend "entry_merge" >>
  disj2_tac >> qexists_tac `v` >> simp[] >>
  qexistsl_tac [`vs++[x]`,`scratch++sc`] >>
  simp[LENGTH_APPEND, GSYM ADD1, Abbr `n`] >>
  conj_tac
  >- (qpat_x_assum `_::rest = DROP _ _` mp_tac >>
      rewrite_tac [DROP_SUC] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j < LENGTH vs`
  >- simp[EL_APPEND1] >>
  `j = LENGTH vs` by decide_tac >> simp[EL_APPEND2]
QED

Resume calldata_members_owned_repeat_intervals[entry_merge]:
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> strip_tac >>
  `a.cs_next_var <= b.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `abi_decoder_operand_live addr.cs_next_var src /\
   abi_decoder_operand_live addr.cs_next_var dst` by metis_tac[abi_decoder_operand_live_mono] >>
  `oid < addr.cs_next_id \/ b.cs_next_id <= oid` by decide_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED

Resume calldata_members_owned_repeat_intervals[frame_merge]:
  qpat_x_assum `Frame st final initial s _ _ _` mp_tac >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> ntac 2 strip_tac >>
  `Own st.cs_next_id final.cs_next_id v` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `Own addr.cs_next_id b.cs_next_id v` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
     BETA_TAC >> ntac 2 strip_tac >>
     ho_match_mp_tac (GEN_ALL calldata_owned_interval_replace) >>
     qexistsl_tac [`s`,`b.cs_next_id`,`addr.cs_next_id`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `ci_mono addr b` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >>
     qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < addr.cs_next_id \/ b.cs_next_id <= id` by decide_tac >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live a.cs_next_var op /\
       abi_decoder_operand_live addr.cs_next_var op` by
        (fs[ci_mono_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
      metis_tac[]) >>
  conj_tac >- suspend "footprint_merge" >>
  qpat_x_assum `Wit st.cs_next_id final.cs_next_id s scratch` mp_tac >>
  qpat_x_assum `Wit addr.cs_next_id b.cs_next_id v sc` mp_tac >>
  qpat_x_assum `!id q k. FLOOKUP u.vs_allocas id = _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
  qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
  qpat_x_assum `Abbrev (Wit = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
  BETA_TAC >> simp_tac bool_ss [MEM_APPEND] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Resume calldata_members_owned_repeat_intervals[footprint_merge]:
  `abi_decode_footprint_frame ((d+vo0,MZ xs)::scratch) initial u` by
    (qpat_x_assum `abi_decode_footprint_frame _ initial s` mp_tac >>
     simp[abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
  irule calldata_footprint_accumulate >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> decide_tac
QED

Resume calldata_members_owned_repeat_intervals[prefix_merge]:
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH xs /\ SUC j <= n` by decide_tac >>
  `type_memory_size (ty_at j) <= (\(ei,az,mz). mz) (EL j xs)` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `j` mp_tac) >> simp[]) >>
  `!i ys. MZ (TAKE i ys) <= MZ ys` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `MZ`] >>
     POP_ASSUM_LIST (K all_tac) >>
     CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV
       (REWR_CONV (GSYM (Q.SPECL [`i`,`ys`] TAKE_DROP))))) >>
     simp[MAP_APPEND, SUM_APPEND, MAP_TAKE]) >>
  `MZ (TAKE (SUC j) xs) <= MZ (TAKE n xs)` by
    (first_x_assum (qspecl_then [`SUC j`,`TAKE n xs`] mp_tac) >>
     simp[TAKE_TAKE, MIN_DEF]) >>
  `V j + type_memory_size (ty_at j) <= V n /\ vo0 <= V j` by
    (qpat_x_assum `MZ (TAKE (SUC j) xs) <= _` mp_tac >>
     simp[Abbr `V`, Abbr `MZ`, TAKE_SUC, EL_TAKE, SUM_APPEND] >> decide_tac) >>
  qpat_x_assum `!j. j < n ==> Pred j _ /\ _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`, Abbr `Wit`] >> strip_tac >>
  irule calldata_member_value_preserved >>
  simp_tac bool_ss [] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `abi_decode_footprint_frame _ u v` (irule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`oid`,`cap`,`base_addr`] >> simp[] >>
  qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise calldata_members_owned_repeat_intervals

(* Tail-aware companion: installed suffix code stays in the traversal invariant. *)
Theorem calldata_members_owned_repeat_intervals_tail:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao0 vo0 st = ((),final) /\
  fn_has_code st final fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d+vo0 /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  (!i. i < LENGTH xs ==> type_memory_size (ty_at i) <= (\(ei,az,mz). mz) (EL i xs)) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
      (mz + (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (ty_at i) <= base_addr+cap /\
      e+type_memory_size (ty_at i) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ Pred i x /\ val_wf (ty_at i) x /\
        val_in_memory (ty_at i) x e v.vs_memory /\
        (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
          ?fuel'. run_from fuel' ctx fn u = r /\
            (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
        v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
        alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        u.vs_alloca_next <= v.vs_alloca_next /\
        (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          FLOOKUP v.vs_allocas id = SOME (q,k)) /\
        (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
          FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
        (!op. abi_decoder_operand_live mid.cs_next_var op ==>
          eval_operand op v = eval_operand op u) /\
        abi_decode_footprint_frame ((e,type_memory_size (ty_at i))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ LENGTH vs = LENGTH xs /\
    (!i. i < LENGTH xs ==> Pred i (EL i vs) /\ val_wf (ty_at i) (EL i vs) /\
      val_in_memory (ty_at i) (EL i vs)
        (d+(vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) t.vs_memory) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame
      ((d+vo0,SUM (MAP (\(ei,az,mz). mz) xs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \l h s. !id q k.
    l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Wit = \l h s sc. !q k. MEM (q,k) sc ==>
    ?id. l <= id /\ id < h /\ FLOOKUP s.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (Wit = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Back = \u v. !fuel r.
    run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn u = r /\
      (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)` >>
  qpat_assum `Abbrev (Back = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Reject = \u. ?fuel z.
    run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u` >>
  qpat_assum `Abbrev (Reject = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Frame = \a b u v e sz sc.
    v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    Own a.cs_next_id b.cs_next_id v /\ u.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < a.cs_next_id \/ b.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
    (!op. abi_decoder_operand_live a.cs_next_var op ==>
      eval_operand op v = eval_operand op u) /\
    abi_decode_footprint_frame ((e,sz)::sc) u v /\
    Wit a.cs_next_id b.cs_next_id v sc` >>
  qpat_assum `Abbrev (Frame = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `AZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). az) ys)` >>
  qpat_assum `Abbrev (AZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `MZ = \(ys:(abi_dec_info # num # num) list). SUM (MAP (\(ei,az,mz). mz) ys)` >>
  qpat_assum `Abbrev (MZ = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `A = \i. ao0 + AZ (TAKE i xs)` >>
  qabbrev_tac `V = \i. vo0 + MZ (TAKE i xs)` >>
  qpat_assum `Abbrev (A = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qpat_assum `Abbrev (V = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Inv = \rest ao vo a s. ?n vs scratch.
    n <= LENGTH xs /\ LENGTH vs = n /\ rest = DROP n xs /\ ao = A n /\ vo = V n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) rest ao vo a = ((),final) /\
    fn_has_code a final fn /\
    cs_extends st a /\ cs_extends a final /\ ci_mono st a /\ ci_mono a final /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live a.cs_next_var src /\
    abi_decoder_operand_live a.cs_next_var dst /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    Frame st final initial s (d+vo0) (MZ xs) scratch /\
    (!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
      val_in_memory (ty_at j) (EL j vs) (d+V j) s.vs_memory)` >>
  qspecl_then [`ctx`,`fn`,`dst`,`src`,`Inv`] mp_tac calldata_members_fixed_fn_invariant_rule >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> suspend "member_step")) >>
  disch_then (qspecl_then [`xs`,`ao0`,`vo0`,`st`,`final`,`initial`] mp_tac) >>
  (impl_tac >- (simp[] >> suspend "initial_invariant")) >>
  strip_tac
  >- (disj1_tac >> simp[Abbr `Reject`] >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `Inv [] _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  `LENGTH vs = LENGTH xs` by
    (qpat_x_assum `[] = DROP _ _` (mp_tac o SYM) >>
     pure_rewrite_tac [DROP_EQ_NIL] >> decide_tac) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >>
  simp[Abbr `Back`]
QED

Resume calldata_members_owned_repeat_intervals_tail[initial_invariant]:
  simp_tac bool_ss [Abbr `Inv`] >>
  qexistsl_tac [`[]`,`[]`] >>
  simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`,
       Abbr `Frame`, Abbr `Wit`, cs_extends_refl,
       abiDecoderFrameTheory.abi_decode_footprint_frame_refl] >>
  `ci_mono st final` by
    (mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`xs`,`ao0`,`vo0`,`st`] mp_tac) >>
     simp[]) >>
  fs[ci_mono_def, ci_mono_refl, cs_extends_refl]
QED

Resume calldata_members_owned_repeat_intervals_tail[member_step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  rename1 `LENGTH vs <= LENGTH xs` >>
  qabbrev_tac `n = LENGTH vs` >>
  `n < LENGTH xs` by
    (qpat_x_assum `_::rest = DROP _ _` mp_tac >>
     Cases_on `n = LENGTH xs` >> fs[Abbr `n`]) >>
  `EL n xs = (ei,az,mz)` by
    (drule HD_DROP >>
     qpat_x_assum `_::rest = DROP _ _` (fn th => rewrite_tac [GSYM th]) >>
     simp[]) >>
  `rest = DROP (SUC n) xs` by
    (qpat_assum `_::rest = DROP _ _` mp_tac >>
     rewrite_tac [DROP_SUC] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  drule calldata_members_cons_split >> strip_tac >> gnvs[] >>
  qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) _ = ((),_)` mp_tac >>
  simp_tac (srw_ss() ++ boolSimps.LET_ss) [comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w) a = (ep,c1)` >>
  rename1 `emit_op ADD [dst; Lit (n2w (V n))] c1 = (dp,addr)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) (A n) CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w (V n))]; return (ep,dp) od) a = ((ep,dp),addr)` by
    simp[comp_bind_def, comp_return_def] >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a addr` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends addr b` by (drule cs_extends_abi_decode >> simp[]) >>
  `fn_has_code a addr fn /\ fn_has_code addr b fn` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all calldata_member_address_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [combinTheory.K_THM] >> strip_tac >>
  qmatch_asmsub_rename_tac `eval_operand dp u = SOME (n2w d + n2w (V n))` >>
  `alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
   Own st.cs_next_id final.cs_next_id s` by
    fs[Abbr `Frame`] >>
  `alloca_inv u /\ alloca_frontier_inv ctx fn site u` by
    (drule_all calldata_alloca_invariants_fields >> simp[]) >>
  `cs_extends st addr /\ cs_extends b final` by
    (conj_tac >- metis_tac[cs_extends_trans] >>
     qpat_assum `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ _ _ _ b = _`
       mp_tac >> metis_tac[]) >>
  `fn_has_code b final fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `a.cs_next_id <= addr.cs_next_id /\ a.cs_next_var <= addr.cs_next_var` by
    (qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) a = ((ep,dp),addr)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `dec_info_needs_offset ei` >>
     simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `ci_mono addr b /\ ci_mono b final` by
    (conj_tac
     >- (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
         disch_then (qspecl_then [`dp`,`ep`,`CALLDATALOAD`,`Lit 0w`,`ei`,`addr`] mp_tac) >> simp[]) >>
     mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`DROP (SUC n) xs`,`az + A n`,`mz + V n`,`b`] mp_tac) >> simp[]) >>
  `st.cs_next_id <= addr.cs_next_id /\ b.cs_next_id <= final.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `Own addr.cs_next_id b.cs_next_id u` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_x_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >>
     BETA_TAC >> rpt strip_tac >> rule_assum_tac BETA_RULE >>
     `st.cs_next_id <= id /\ id < final.cs_next_id` by decide_tac >>
     first_x_assum (qspecl_then [`id`,`q`,`k`] mp_tac) >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  `type_memory_size (ty_at n) <= mz` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `V n + mz <= vo0 + MZ xs /\ vo0 <= V n` by
    (`xs = TAKE n xs ++ (ei,az,mz)::DROP (SUC n) xs` by metis_tac[TAKE_DROP] >>
     qpat_x_assum `xs = TAKE n xs ++ _` mp_tac >>
     simp_tac bool_ss [Abbr `V`, Abbr `MZ`] >>
     disch_then (fn th => once_rewrite_tac [th]) >>
     simp[MAP_APPEND, SUM_APPEND]) >>
  `base_addr <= d + V n /\
   d + V n + type_memory_size (ty_at n) <= base_addr + cap /\
   d + V n + type_memory_size (ty_at n) < dimword(:256)` by decide_tac >>
  `eval_operand dp u = SOME (n2w (d + V n))` by simp[word_add_n2w] >>
  `FLOOKUP u.vs_allocas oid = SOME (base_addr,cap)` by simp[] >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _` drule_all >>
  `Back s u` by simp[Abbr `Back`] >>
  strip_tac
  >- (disj1_tac >>
      qpat_x_assum `Reject u` mp_tac >>
      simp_tac bool_ss [Abbr `Reject`] >> strip_tac >>
      qpat_x_assum `Back s u` mp_tac >>
      simp_tac bool_ss [Abbr `Back`] >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >>
      qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`fuel'`,`z`] >> simp[]) >>
  `Back s v` by
    (qpat_x_assum `Back s u` mp_tac >>
     qpat_x_assum `Back u v` mp_tac >>
     simp_tac bool_ss [Abbr `Back`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `cs_extends st b /\ ci_mono st b` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `A (SUC n) = az + A n /\ V (SUC n) = mz + V n` by
    (simp[Abbr `A`, Abbr `V`, Abbr `AZ`, Abbr `MZ`, TAKE_SUC, EL_TAKE,
          SUM_APPEND] >> decide_tac) >>
  `Frame st final initial v (d+vo0) (MZ xs) (scratch++sc)` by
    suspend "frame_merge" >>
  `!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
    val_in_memory (ty_at j) (EL j vs) (d+V j) v.vs_memory` by
    suspend "prefix_merge" >>
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   abi_decoder_operand_live b.cs_next_var src /\ abi_decoder_operand_live b.cs_next_var dst /\
   FLOOKUP v.vs_allocas oid = SOME (base_addr,cap)` by
    suspend "entry_merge" >>
  disj2_tac >> qexists_tac `v` >> simp[] >>
  qexistsl_tac [`vs++[x]`,`scratch++sc`] >>
  simp[LENGTH_APPEND, GSYM ADD1, Abbr `n`] >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j < LENGTH vs`
  >- simp[EL_APPEND1] >>
  `j = LENGTH vs` by decide_tac >> simp[EL_APPEND2]
QED

Resume calldata_members_owned_repeat_intervals_tail[entry_merge]:
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> strip_tac >>
  `a.cs_next_var <= b.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `abi_decoder_operand_live addr.cs_next_var src /\
   abi_decoder_operand_live addr.cs_next_var dst` by metis_tac[abi_decoder_operand_live_mono] >>
  `oid < addr.cs_next_id \/ b.cs_next_id <= oid` by decide_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED

Resume calldata_members_owned_repeat_intervals_tail[frame_merge]:
  qpat_x_assum `Frame st final initial s _ _ _` mp_tac >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`] >> ntac 2 strip_tac >>
  `Own st.cs_next_id final.cs_next_id v` by
    (qpat_x_assum `Own st.cs_next_id final.cs_next_id s` mp_tac >>
     qpat_x_assum `Own addr.cs_next_id b.cs_next_id v` mp_tac >>
     qpat_x_assum `Abbrev (Own = _)` mp_tac >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
     BETA_TAC >> ntac 2 strip_tac >>
     ho_match_mp_tac (GEN_ALL calldata_owned_interval_replace) >>
     qexistsl_tac [`s`,`b.cs_next_id`,`addr.cs_next_id`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `ci_mono addr b` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >>
     qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < addr.cs_next_id \/ b.cs_next_id <= id` by decide_tac >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live a.cs_next_var op /\
       abi_decoder_operand_live addr.cs_next_var op` by
        (fs[ci_mono_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
      metis_tac[]) >>
  conj_tac >- suspend "footprint_merge" >>
  qpat_x_assum `Wit st.cs_next_id final.cs_next_id s scratch` mp_tac >>
  qpat_x_assum `Wit addr.cs_next_id b.cs_next_id v sc` mp_tac >>
  qpat_x_assum `!id q k. FLOOKUP u.vs_allocas id = _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  qpat_x_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
  qpat_x_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
  qpat_x_assum `Abbrev (Wit = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
  BETA_TAC >> simp_tac bool_ss [MEM_APPEND] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Resume calldata_members_owned_repeat_intervals_tail[footprint_merge]:
  `abi_decode_footprint_frame ((d+vo0,MZ xs)::scratch) initial u` by
    (qpat_x_assum `abi_decode_footprint_frame _ initial s` mp_tac >>
     simp[abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
  irule calldata_footprint_accumulate >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> decide_tac
QED

Resume calldata_members_owned_repeat_intervals_tail[prefix_merge]:
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH xs /\ SUC j <= n` by decide_tac >>
  `type_memory_size (ty_at j) <= (\(ei,az,mz). mz) (EL j xs)` by
    (qpat_x_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _`
       (qspec_then `j` mp_tac) >> simp[]) >>
  `!i ys. MZ (TAKE i ys) <= MZ ys` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `MZ`] >>
     POP_ASSUM_LIST (K all_tac) >>
     CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV
       (REWR_CONV (GSYM (Q.SPECL [`i`,`ys`] TAKE_DROP))))) >>
     simp[MAP_APPEND, SUM_APPEND, MAP_TAKE]) >>
  `MZ (TAKE (SUC j) xs) <= MZ (TAKE n xs)` by
    (first_x_assum (qspecl_then [`SUC j`,`TAKE n xs`] mp_tac) >>
     simp[TAKE_TAKE, MIN_DEF]) >>
  `V j + type_memory_size (ty_at j) <= V n /\ vo0 <= V j` by
    (qpat_x_assum `MZ (TAKE (SUC j) xs) <= _` mp_tac >>
     simp[Abbr `V`, Abbr `MZ`, TAKE_SUC, EL_TAKE, SUM_APPEND] >> decide_tac) >>
  qpat_x_assum `!j. j < n ==> Pred j _ /\ _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  qpat_x_assum `Frame addr b u v _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Frame`, Abbr `Wit`] >> strip_tac >>
  irule calldata_member_value_preserved >>
  simp_tac bool_ss [] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `abi_decode_footprint_frame _ u v` (irule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`oid`,`cap`,`base_addr`] >> simp[] >>
  qpat_x_assum `!id. id < addr.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise calldata_members_owned_repeat_intervals_tail
