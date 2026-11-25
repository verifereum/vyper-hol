(* Interpret the actual fetched, successful administrative instructions.
   The observer advances only through the materializer's installed interval. *)
Theory entryCreateCtorCopyGeometry
Ancestors
  entryCreatePathScope createSizePrefixReplay createMarkedPath
  createSizeCutRegion createSizeCutCode createSizeLocationCode context pair
  createSizeTypedCopyCode exprSimPtrTopLevelStorageCopy
  exprSimAbiGasBridge exprSimAbiDecodeSiteCoverage fragGasSeqAbort fragGasOrigin fragExec
  exprLoweringProps exprLowering compileEnv venomInst venomState
  venomExecSemantics venomInstProofs gasEvents relation list rich_list arithmetic

Theorem copied_head_prefix_step[local]:
  (s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  gas_origin_edge F explicit ctx fn s [] (OK t) ==>
  create_expr_prefix a b explicit ctx fn s [] t
Proof
  strip_tac >> simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]
QED

Theorem copied_head_prefix_trans[local]:
  create_expr_prefix a b explicit ctx fn s [] u /\
  create_expr_prefix a b explicit ctx fn u [] t ==>
  create_expr_prefix a b explicit ctx fn s [] t
Proof
  metis_tac[create_expr_prefix_append,APPEND_NIL]
QED

Theorem copied_head_straight_prefix[local]:
  !code s t.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    (!k. k < LENGTH code ==>
      s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx + k <> LENGTH b.cs_current_insts) /\
    run_inst_seq code s = OK t ==>
    create_expr_prefix a b explicit ctx fn s []
      (t with vs_inst_idx := LENGTH code + s.vs_inst_idx)
Proof
  Induct >- simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted,step_preserves_control_flow] >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `create_expr_prefix a b explicit ctx fn s [] v` by
    (irule copied_head_prefix_step >> conj_tac >- metis_tac[] >>
     conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     simp[Abbr `v`,gas_origin_edge_def] >> qexists_tac `0` >>
     simp[gas_events_step_def]) >>
  irule copied_head_prefix_trans >> first_assum (irule_at Any) >>
  first_x_assum (qspecl_then [`v`,`t with vs_inst_idx := v.vs_inst_idx`] mp_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  simp[Abbr `v`,run_inst_seq_inst_idx,ADD_CLAUSES,instIdxIndepTheory.exec_result_map_def] >>
  `!k. k < LENGTH code ==> s.vs_current_bb <> b.cs_current_bb \/
       k + SUC s.vs_inst_idx <> LENGTH b.cs_current_insts` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[ADD_CLAUSES]) >>
  fs[ADD_CLAUSES]
QED

Theorem copied_head_jump_prefix[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  (s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  step_inst_base i s = OK (jump_to l s) ==>
  create_expr_prefix a b explicit ctx fn s [] (jump_to l s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule copied_head_prefix_step >> conj_tac >- metis_tac[] >> simp[] >>
  simp[gas_origin_edge_def] >> qexists_tac `0` >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
   is_terminator i.inst_opcode` by fs[is_terminator_def] >>
  simp[step_inst_non_invoke,gas_events_step_def] >> metis_tac[]
QED

Theorem copied_head_prefix_fetch[local]:
  isPREFIX code (DROP k bb.bb_instructions) /\ j < LENGTH code ==>
  get_instruction bb (k+j) = SOME (EL j code)
Proof
  strip_tac >>
  `j < LENGTH (DROP k bb.bb_instructions)` by
    (drule IS_PREFIX_LENGTH >> decide_tac) >>
  `k+j < LENGTH bb.bb_instructions` by fs[LENGTH_DROP] >>
  simp[get_instruction_def] >>
  drule_all is_prefix_el >> simp[EL_DROP,ADD_COMM]
QED

Theorem copied_head_span_off_exit[local]:
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_id IN frag_ids a b) code ==>
  !k. k < LENGTH code ==>
      s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx+k <> LENGTH b.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  drule_all copied_head_prefix_fetch >> strip_tac >>
  fs[EVERY_MEM] >> metis_tac[EL_MEM]
QED

Theorem copied_head_materialize_cut_code:
  compile_materialize_vv ce ty vv sm = (dst,sb) ==>
  create_cut_code {} sm sb
Proof
  simp[compile_materialize_vv_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `unwrap_value _ _ mid = (src,sc)` >>
  irule create_cut_code_join >>
  qexists_tac `sc` >> reverse conj_tac
  >- metis_tac[create_store_memory_cut_code,SND] >>
  irule create_cut_code_join >> qexists_tac `mid` >>
  conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[compile_alloc_buffer_def,comp_bind_def,comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `create_cut_code {} sm
        (SND (emit_op ALLOCA [Lit (n2w (type_memory_bytes ce ty))] sm))` by
        simp[create_cut_code_emit_op,create_cut_targets_def] >>
      pop_assum mp_tac >> asm_rewrite_tac[SND]) >>
  metis_tac[create_unwrap_cut_code,SND]
QED

(* Only the continuation's first fetch is used, never its execution. *)
Theorem copied_head_materialize_exit_fetch:
  create_cut_code {} sb sc /\ fn_has_code sb sc fn /\
  (sb.cs_current_bb <> sc.cs_current_bb \/
   LENGTH sb.cs_current_insts <> LENGTH sc.cs_current_insts) ==>
  !bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
         i.inst_id NOTIN frag_ids sm sb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `sb.cs_next_id <= i.inst_id` by metis_tac[create_cut_continuation_fetch] >>
  fs[abiEncoderPropsTheory.frag_ids_def] >> decide_tac
QED

(* These introductions use the exact successful run and its installed slice.
   The slice can be from the allocation, the unwrap, or the store, including
   a single block of the unwrap's copy loop. *)
Theorem copied_head_materialize_span_laws:
  compile_materialize_vv ce ty vv sm = (dst,sb) /\
  (!bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sm sb) ==>
  (!s. create_expr_prefix sm sb explicit ctx fn s [] s) /\
  (!s u t. create_expr_prefix sm sb explicit ctx fn s [] u /\
           create_expr_prefix sm sb explicit ctx fn u [] t ==>
           create_expr_prefix sm sb explicit ctx fn s [] t) /\
  (!s code bb t.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. MEM i (frag_code sm sb) /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==>
    create_expr_prefix sm sb explicit ctx fn s []
      (t with vs_inst_idx := LENGTH code + s.vs_inst_idx)) /\
  (!s bb i l.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\ MEM i (frag_code sm sb) /\
    (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
    step_inst_base i s = OK (jump_to l s) ==>
    create_expr_prefix sm sb explicit ctx fn s [] (jump_to l s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. MEM i (frag_code sm sb) ==> i.inst_id IN frag_ids sm sb` by
    metis_tac[copied_head_materialize_cut_code,create_cut_code_def] >>
  simp[] >> conj_tac >- metis_tac[copied_head_prefix_trans] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (Q.SPECL [`code`,`s`,`t`] copied_head_straight_prefix) >>
      simp[] >> reverse conj_tac >- fs[EVERY_MEM] >>
      `EVERY (\i. i.inst_id IN frag_ids sm sb) code` by fs[EVERY_MEM] >>
      `!k. k < LENGTH code ==> s.vs_current_bb <> sb.cs_current_bb \/
          s.vs_inst_idx+k <> LENGTH sb.cs_current_insts` by
        (rpt strip_tac >> metis_tac[copied_head_span_off_exit]) >> fs[]) >>
  rpt gen_tac >> strip_tac >> irule copied_head_jump_prefix >>
  simp[] >> metis_tac[]
QED

(* Compiler-side premises for the three observer producers.  In particular
   the unwrap need not remain in the current block. *)
Theorem copied_head_materialize_cuts:
  compile_alloc_buffer (type_memory_bytes ce ty) sm = (buf,mid) /\
  unwrap_value ce vv mid = (src,sc) /\
  compile_store_memory ce src buf.buf_operand ty ty sc = ((),sb) /\
  fn_has_code sm sb fn ==>
  fn_has_code sm mid fn /\ fn_has_code mid sc fn /\ fn_has_code sc sb fn /\
  (!i. MEM i (frag_code sm sb) <=>
       MEM i (frag_code sm mid) \/ MEM i (frag_code mid sc) \/
       MEM i (frag_code sc sb))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sm mid /\ ci_mono mid sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
              ci_mono_compile_store_memory,SND] >>
  fs[ci_mono_def] >>
  `cs_extends mid sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm mid fn /\ fn_has_code mid sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code mid sc fn /\ fn_has_code sc sb fn` by metis_tac[fn_has_code_split] >>
  simp[] >> gen_tac >>
  `MEM i (frag_code sm sb) <=> MEM i (frag_code sm mid) \/ MEM i (frag_code mid sb)` by
    metis_tac[abi_decode_frag_code_compose] >>
  `MEM i (frag_code mid sb) <=> MEM i (frag_code mid sc) \/ MEM i (frag_code sc sb)` by
    metis_tac[abi_decode_frag_code_compose] >> simp[]
QED

Theorem copied_head_straight_span_code:
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\ fn_has_code a b fn ==>
  ?bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts a b) (DROP (LENGTH a.cs_current_insts) bb.bb_instructions) /\
       (!i. MEM i (emitted_insts a b) ==> MEM i (frag_code a b))
Proof
  fs[cs_extends_def,fn_has_code_def,frag_code_def,emitted_blocks_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  `LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  fs[IS_PREFIX_APPEND] >> gvs[DROP_APPEND]
QED

(* The slot-copy layout is supplied by toplevel_copy_compile_blocks.
   The initial span starts after the old open block prefix; the other
   spans occupy their entire closed blocks.  This includes the jumps. *)
Theorem copied_head_slot_spans_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var dst) n loc LocMemory F a = (u,b) /\
  fn_has_code a b fn /\
  emitted_blocks a b =
    [<|bb_label := loop_body; bb_instructions := body_code|>;
     <|bb_label := hdr; bb_instructions := hdr_code|>;
     <|bb_label := a.cs_current_bb; bb_instructions := a.cs_current_insts ++ init_code|>] ==>
  lookup_block loop_body fn.fn_blocks = SOME <|bb_label := loop_body; bb_instructions := body_code|> /\
  lookup_block hdr fn.fn_blocks = SOME <|bb_label := hdr; bb_instructions := hdr_code|> /\
  (?bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        DROP (LENGTH a.cs_current_insts) bb.bb_instructions = init_code) /\
  b.cs_current_insts = [] /\
  (!i. MEM i init_code \/ MEM i hdr_code \/ MEM i body_code ==> MEM i (frag_code a b))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_layout_lookups >> strip_tac >>
  drule_all toplevel_copy_compile_exit >>
  simp[frag_code_def,DROP_LENGTH_APPEND] >> metis_tac[]
QED
