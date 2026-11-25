(* Translate the slot copy's fetched occurrences to the unwrap fragment. *)
Theory entryCreateSlotWalkScope
Ancestors
  bodyFullUnwrapSlotCursor abiBufferAllocationCode createSizeLocationCode
  createSizeCutCode createSizePrefixReplay createMarkedPath entryCreatePathScope
  exprSimAbiDecodeSiteCoverage emitHelperProps pred_set rich_list arithmetic
  relation slotCopyCursorWindow exprPtrUnwrapEnsureShape exprPtrUnwrapAllocation
  exprSimStorageCopy fragExec createSizeCutRegion copyExecution venomInst
  venomState compileEnv abiEncoderProps list exprLoweringProps pair loweringHalt

Theorem slot_copy_walk_create_prefix:
  slot_copy_walk
    (\l k i. (l,k) <> (b.cs_current_bb,LENGTH b.cs_current_insts) /\
             i.inst_id IN frag_ids a b) E C f s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  qid_spec_tac `t` >> qid_spec_tac `s` >>
  simp[slot_copy_walk_def] >> ho_match_mp_tac RTC_INDUCT >>
  conj_tac >- simp[create_expr_prefix_marked] >>
  rpt strip_tac >>
  rename1 `gas_origin_edge F E C f u [] (OK v)` >>
  `create_expr_prefix a b E C f u [] v` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  irule (SIMP_RULE bool_ss [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL entryCreatePathScopeTheory.create_expr_prefix_append))) >>
  qexists_tac `v` >> simp[]
QED

Theorem ensure_slot_copy_walk_scope:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm a = (op,b) /\
  fn_has_code a b f /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) ==>
  ensure_slot_copy_walk_ok
    (\l k i. (l,k) <> (b.cs_current_bb,LENGTH b.cs_current_insts) /\
             i.inst_id IN frag_ids a b) nb n a b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ensure_slot_memory_split >>
  disch_then (qx_choosel_then [`buf`,`m`] (map_every assume_tac o CONJUNCTS)) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `a.cs_blocks = m.cs_blocks` by fs[same_blocks_def] >>
  `create_cut_code {} a b` by metis_tac[create_ensure_in_memory_cut_code,SND] >>
  `cs_extends a m` by metis_tac[compile_alloc_buffer_extends] >>
  `!i. MEM i (frag_code a b) ==> i.inst_id IN frag_ids a b` by fs[create_cut_code_def] >>
  `!i. MEM i (emitted_insts a m) ==> MEM i (frag_code a m)` by
    simp[exprSimAbiGasBridgeTheory.frag_code_def, emitted_blocks_def] >>
  Cases_on `n = 1`
  >- (qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> disch_tac >>
      drule storage_copy_word_layout >> strip_tac >>
      `cs_extends m b` by metis_tac[same_blocks_def,cs_extends_same_block] >>
      `LENGTH b.cs_current_insts = LENGTH m.cs_current_insts + LENGTH (emitted_insts m b)` by
        (qpat_x_assum `isPREFIX m.cs_current_insts b.cs_current_insts` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         rw[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >> fs[]) >>
      `!i. MEM i (emitted_insts m b) ==> MEM i (frag_code m b)` by
        fs[exprSimAbiGasBridgeTheory.frag_code_def, emitted_blocks_def, same_blocks_def] >>
      drule_all abi_decode_frag_code_compose >> strip_tac >>
      `!i. MEM i (emitted_insts a m) \/ MEM i (emitted_insts m b) ==>
           i.inst_id IN frag_ids a b` by metis_tac[] >>
      rewrite_tac[ensure_slot_copy_walk_ok_def] >> BETA_TAC >> conj_tac
      >- (conj_tac
          >- (simp[] >> decide_tac) >>
          first_x_assum irule >> simp[]) >>
      qpat_assum `n = 1` (fn th => simp_tac bool_ss [th, COND_CLAUSES]) >>
      rpt gen_tac >> disch_tac >>
      `sm = m` by metis_tac[PAIR_EQ] >>
      qpat_x_assum `sm = m` SUBST_ALL_TAC >>
      rpt gen_tac >> disch_tac >> conj_tac
      >- (qpat_x_assum `j < LENGTH (emitted_insts m b)` mp_tac >> simp[] >> decide_tac) >>
      first_x_assum irule >> disj2_tac >> irule EL_MEM >> simp[]) >>
  qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
  `b = slot_copy_final m src buf.buf_operand n (if loc = LocStorage then SLOAD else TLOAD)` by
    metis_tac[compile_slot_to_memory_shape, PAIR_EQ] >>
  `cs_extends m b` by metis_tac[slot_copy_extends] >>
  drule_all abi_decode_frag_code_compose >> strip_tac >>
  `!i. MEM i (frag_code a m) \/ MEM i (frag_code m b) ==>
       i.inst_id IN frag_ids a b` by metis_tac[] >>
  drule_all fn_has_code_split >> strip_tac >>
  `lookup_block m.cs_current_bb f.fn_blocks = SOME
     <|bb_label := m.cs_current_bb;
       bb_instructions := m.cs_current_insts ++ slot_copy_init_insts m|>` by
    metis_tac[slot_copy_lookup] >>
  `get_instruction
     <|bb_label := m.cs_current_bb;
       bb_instructions := m.cs_current_insts ++ slot_copy_init_insts m|>
     (LENGTH a.cs_current_insts) =
     SOME (mk_inst a.cs_next_id ALLOCA [Lit (n2w nb)] [STRING #"%" (toString a.cs_next_var)])` by
    (simp[get_instruction_def] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[EL_APPEND_EQN]) >>
  `!i. (MEM i (slot_copy_init_insts m) \/
        MEM i (slot_copy_cond_insts m n) \/
        MEM i (slot_copy_body_insts m src buf.buf_operand (if loc = LocStorage then SLOAD else TLOAD))) ==>
       MEM i (frag_code m b)` by
    (qpat_assum `b = slot_copy_final _ _ _ _ _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,exprSimAbiGasBridgeTheory.frag_code_def,slot_copy_emitted_blocks,slot_copy_blocks_def,
          slot_copy_final_def,DROP_LENGTH_APPEND] >> metis_tac[]) >>
  rewrite_tac[ensure_slot_copy_walk_ok_def] >> BETA_TAC >> conj_tac
  >- (`(mk_inst a.cs_next_id ALLOCA [Lit (n2w nb)] [STRING #"%" (toString a.cs_next_var)]).inst_id
          IN frag_ids a b` by
        (first_x_assum irule >> disj1_tac >> first_x_assum irule >> simp[]) >>
      simp[] >> strip_tac >> metis_tac[]) >>
  qpat_assum `n <> 1` (fn th => simp_tac bool_ss [th, COND_CLAUSES]) >>
  rpt gen_tac >> disch_tac >>
  `sm = m` by metis_tac[PAIR_EQ] >>
  qpat_x_assum `sm = m` SUBST_ALL_TAC >>
  `LENGTH b.cs_current_insts = 0 /\ b.cs_current_bb = slot_copy_exit m` by
    (qpat_assum `b = slot_copy_final _ _ _ _ _` (fn th => simp[th,slot_copy_final_def])) >>
  `!j. LENGTH m.cs_current_insts + j <> 0` by simp[] >>
  `slot_copy_cond m <> slot_copy_exit m /\ slot_copy_body m <> slot_copy_exit m` by
    simp[slot_copy_labels_distinct] >>
  `emitted_blocks m b =
    [<|bb_label := slot_copy_body m;
       bb_instructions := slot_copy_body_insts m src buf.buf_operand (if loc = LocStorage then SLOAD else TLOAD)|>;
     <|bb_label := slot_copy_cond m; bb_instructions := slot_copy_cond_insts m n|>;
     <|bb_label := m.cs_current_bb; bb_instructions := m.cs_current_insts ++ slot_copy_init_insts m|>]` by
    (qpat_assum `b = slot_copy_final _ _ _ _ _`
      (fn th => simp[th,slot_copy_emitted_blocks,slot_copy_blocks_def])) >>
  qpat_assum `emitted_blocks m b = _`
    (fn th => simp[NoAsms,th]) >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> disch_tac >>
  `!i. (MEM i (slot_copy_init_insts m) \/ MEM i (slot_copy_cond_insts m n) \/
         MEM i (slot_copy_body_insts m src buf.buf_operand (if loc = LocStorage then SLOAD else TLOAD))) ==>
        i.inst_id IN frag_ids a b` by metis_tac[] >>
  qpat_x_assum `b = slot_copy_final _ _ _ _ _` kall_tac >>
  simp[] >> first_x_assum irule >> metis_tac[EL_MEM]
QED
