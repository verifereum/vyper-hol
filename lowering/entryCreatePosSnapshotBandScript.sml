(* The positional snapshot's computed traversal stops at the actual exit.
   Coverage of the numerical band is supplied by the snapshot compiler. *)
Theory entryCreatePosSnapshotBand
Ancestors
  entryCreateFocusSpec entryCreateIntervalLayout createCtorSegmentArrival compileExprAllocaFresh
  exprSimAbiEncodeSiteResources exprSimAbiGasBridge loweringShapeDefs fragExec
  fragFuel venomExecSemantics venomExecProofs venomInstIdsProps venomWf
  externalEntryShape exprLoweringProps abiEncoderProps compileEnv loweringStateRelDefs
  venomFnInstsProofs venomInst relation rich_list list pred_set arithmetic

Theorem snapshot_added_frag_member[local]:
  cs_extends a b /\ MEM i (added_insts a b) ==> MEM i (frag_code a b)
Proof
  strip_tac >>
  `?new. b.cs_blocks = new ++ a.cs_blocks /\ emitted_blocks a b = new` by
    (fs[cs_extends_def] >> metis_tac[emitted_blocks_append]) >>
  Cases_on `new = []`
  >- (gvs[added_insts_def, state_insts_def, all_blocks_def,
          FLAT_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG,
          frag_code_def, emitted_insts_def]) >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    (qspec_then `new:basic_block list` mp_tac APPEND_FRONT_LAST >> simp[] >>
     disch_then (ACCEPT_TAC o REWRITE_RULE [REVERSE_APPEND, REVERSE_DEF, APPEND] o
                 Q.AP_TERM `REVERSE : basic_block list -> basic_block list` o SYM)) >>
  fs[added_insts_def, state_insts_def, all_blocks_def, REVERSE_APPEND,
     IS_PREFIX_APPEND, frag_code_def, NULL_EQ, MAP_APPEND, FLAT_APPEND,
     DROP_APPEND, DROP_LENGTH_TOO_LONG, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  gvs[DROP_LENGTH_APPEND, DECIDE ``x - (y + x) = 0n``,
      DECIDE ``x - (y + (z + x)) = 0n``, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  metis_tac[]
QED

(* The installed occurrence is either in a finished block, or at an
   index strictly inside the final prefix. *)
Theorem snapshot_frag_member_location[local]:
  MEM i (frag_code a b) ==>
  MEM i b.cs_current_insts \/
  ?bb. MEM bb (emitted_blocks a b) /\ MEM i bb.bb_instructions
Proof
  Cases_on `emitted_blocks a b = []` >>
  gvs[frag_code_def, emitted_insts_def, NULL_EQ, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_DROP_IMP, MEM_LAST_NOT_NIL, MEM_FRONT_NOT_NIL]
QED

Theorem snapshot_exit_not_generated[local]:
  fn_has_code a b f /\ fn_inst_ids_distinct f /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\
  MEM i (frag_code a b) /\ ctor_segment_fetch f x = SOME i ==>
  ~create_operand_at b x
Proof
  strip_tac >> strip_tac >>
  `?endbb. lookup_block b.cs_current_bb f.fn_blocks = SOME endbb /\
           get_instruction endbb (LENGTH b.cs_current_insts) = SOME i` by
    fs[ctor_segment_fetch_def, create_operand_at_def, AllCaseEqs()] >>
  `MEM endbb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule snapshot_frag_member_location >> strip_tac
  >- ( `isPREFIX b.cs_current_insts endbb.bb_instructions` by
         (fs[fn_has_code_def] >> metis_tac[]) >>
       `ALL_DISTINCT (MAP (\j. j.inst_id) endbb.bb_instructions)` by
         (qspec_then `\bb:basic_block. MAP (\j. j.inst_id) bb.bb_instructions`
            (irule o BETA_RULE) all_distinct_flat_map_member >>
          qexists_tac `f.fn_blocks` >> fs[fn_inst_ids_distinct_def]) >>
       gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN, AllCaseEqs(),
           ALL_DISTINCT_APPEND, MEM_MAP] >>
       Cases_on `l` >> gvs[] >> metis_tac[]) >>
  `bb.bb_label <> b.cs_current_bb` by (fs[MEM_MAP] >> metis_tac[]) >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `bb <> endbb` by metis_tac[lookup_block_label] >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i endbb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs(), EL_MEM] >>
  `i.inst_id IN set (MAP (\j. j.inst_id) bb.bb_instructions) /\
   i.inst_id IN set (MAP (\j. j.inst_id) endbb.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  fs[fn_inst_ids_distinct_def] >>
  qspecl_then [`f.fn_blocks`, `\blk:basic_block. MAP (\j. j.inst_id) blk.bb_instructions`]
    (mp_tac o BETA_RULE) all_distinct_flat_map_unique >> metis_tac[]
QED

Theorem snapshot_segment_halted[local]:
  ctor_segment_next f x i = SOME y ==> y.vs_halted = x.vs_halted
Proof
  rw[ctor_segment_next_def, ctor_segment_entry_def, AllCaseEqs()] >>
  gvs[] >> metis_tac[step_inst_base_OK_preserves_halted, eval_phis_preserves_halted]
QED

Theorem pos_materialized_snapshot_live_band_interval:
  compile_snapshot_vv ce T input a = (saved,b) /\ ~is_word_type (vv_type input) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\
  create_layout a b /\
  EVERY (\i. ~MEM i.inst_opcode [GAS; CREATE; CREATE2; INVOKE]) (frag_code a b) /\
  create_operand_at a s /\ ~s.vs_halted /\
  RTC (\x y. ?i. ctor_segment_fetch f x = SOME i /\
                 a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next f x i = SOME y) s u ==>
  RTC (\x y. ~x.vs_halted /\ ~y.vs_halted /\ ~create_operand_at b x /\
             ?i. ctor_segment_fetch f x = SOME i /\ i.inst_id IN frag_ids a b /\
                 i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                 ctor_segment_next f x i = SOME y) s u
Proof
  strip_tac >>
  `cs_extends a b` by metis_tac[compile_snapshot_vv_labels, pairTheory.SND] >>
  `!x i. ctor_segment_fetch f x = SOME i /\ i.inst_id IN frag_ids a b ==>
        MEM i (frag_code a b) /\ ~create_operand_at b x` by
    (rpt gen_tac >> strip_tac >>
     `?j. MEM j (added_insts a b) /\ j.inst_id = i.inst_id` by
       metis_tac[compile_snapshot_vv_added_id] >>
     `MEM j (frag_code a b)` by metis_tac[snapshot_added_frag_member] >>
     `MEM j (fn_insts f)` by metis_tac[abi_encode_frag_code_members] >>
     `MEM i (fn_insts f)` by
       (fs[ctor_segment_fetch_def, AllCaseEqs()] >>
        metis_tac[lookup_block_get_instruction_fn_insts]) >>
     `i = j` by metis_tac[fn_inst_ids_distinct_inj] >>
     qpat_x_assum `i = j` SUBST_ALL_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule snapshot_exit_not_generated >> simp[] >>
     qexistsl_tac [`a`,`f`,`j`] >> fs[create_layout_def]) >>
  qpat_x_assum `create_operand_at a s` kall_tac >>
  qpat_x_assum `~s.vs_halted` mp_tac >>
  qpat_x_assum `RTC _ s u` mp_tac >>
  map_every qid_spec_tac [`u`,`s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[PULL_EXISTS] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >> BETA_TAC >>
  rename1 `ctor_segment_next f x i = SOME y` >>
  `i.inst_id IN frag_ids a b` by simp[frag_ids_def] >>
  `MEM i (frag_code a b) /\ ~create_operand_at b x` by metis_tac[] >>
  `~y.vs_halted` by metis_tac[snapshot_segment_halted] >>
  `i.inst_opcode <> GAS` by (fs[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `y` >> simp[] >> metis_tac[]
QED

Theorem pos_materialized_snapshot_live_band:
  compile_snapshot_vv ce T input a = (saved,b) /\ ~is_word_type (vv_type input) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) /\
  EVERY (\i. ~MEM i.inst_opcode [GAS; CREATE; CREATE2; INVOKE]) (frag_code a b) /\
  create_operand_at a s /\ ~s.vs_halted /\
  RTC (\x y. ?i. ctor_segment_fetch f x = SOME i /\
                 a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next f x i = SOME y) s u ==>
  RTC (\x y. ~x.vs_halted /\ ~y.vs_halted /\ ~create_operand_at b x /\
             ?i. ctor_segment_fetch f x = SOME i /\ i.inst_id IN frag_ids a b /\
                 i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                 ctor_segment_next f x i = SOME y) s u
Proof
  strip_tac >>
  `cs_extends a b` by metis_tac[compile_snapshot_vv_labels, pairTheory.SND] >>
  `create_layout a b` by (irule create_layout_of_all_blocks >> simp[]) >>
  metis_tac[pos_materialized_snapshot_live_band_interval]
QED
