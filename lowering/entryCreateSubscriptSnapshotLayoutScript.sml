(* The numeric snapshot band owns only installed occurrences before its cut. *)
Theory entryCreateSubscriptSnapshotLayout
Ancestors
  entryCreateIntervalLayout entryCreateFocusSpec createCtorSegmentArrival
  exprSimAbiDecodeCoverageActions
  exprSimAbiGasBridge exprLowering exprLoweringProps
  venomFnInstsProofs venomExecProofs venomExecSemantics venomWf fragExec compileEnv
  list rich_list emitHelper abiEncoderProps context exprSimAbiEncodeSiteResources venomInst

fun coverage_steps defs =
  rpt (FIRST [CHANGED_TAC (simp (defs @ [abi_decode_id_coverage_prims,
                abi_decode_id_coverage_return, abi_decode_id_coverage_alloc_buffer])),
              irule abi_decode_id_coverage_bind,
              irule abi_decode_id_coverage_ignore_bind,
              conj_tac, gen_tac, IF_CASES_TAC]);

Theorem snapshot_coverage_location[local,simp]:
  abi_decode_id_coverage (compile_imm_load_word ctor imm op) /\
  abi_decode_id_coverage (compile_imm_store_word imm op v) /\
  abi_decode_id_coverage (compile_lit_byte_offset op n)
Proof
  Cases_on `imm` >> Cases_on `ctor` >> Cases_on `op` >>
  coverage_steps [compile_imm_load_word_def, compile_imm_store_word_def,
                  compile_lit_byte_offset_def]
QED

Theorem snapshot_coverage_ptr[local,simp]:
  abi_decode_id_coverage (compile_ptr_load ctor imm loc op) /\
  abi_decode_id_coverage (compile_ptr_store ctor imm loc op v)
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  coverage_steps [compile_ptr_load_def, compile_ptr_store_def]
QED

Theorem snapshot_coverage_loop[local,simp]:
  abi_decode_id_coverage (compile_word_copy_loop_base src dst count_op ll sl ctor imm)
Proof
  coverage_steps [compile_word_copy_loop_base_def, LET_DEF]
QED

Theorem snapshot_coverage_immutables[local,simp]:
  !n off. abi_decode_id_coverage (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> coverage_steps [compile_imm_copy_to_memory_def]
QED

Theorem snapshot_coverage_ensure[local,simp]:
  abi_decode_id_coverage (compile_ensure_in_memory op loc bytes n ctor imm)
Proof
  Cases_on `loc` >> coverage_steps
    [compile_ensure_in_memory_def, LET_DEF, compile_storage_to_memory_def,
     compile_transient_to_memory_def, compile_word_copy_loop_def,
     compile_word_copy_loop_op_def]
QED

Theorem snapshot_coverage_unwrap[local,simp]:
  abi_decode_id_coverage (unwrap_value ce vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, abi_decode_id_coverage_return] >>
  Cases_on `p.ptr_location` >> coverage_steps []
QED

Theorem snapshot_coverage_copy[local,simp]:
  abi_decode_id_coverage (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, abi_decode_id_coverage_prims,
                      abi_decode_id_coverage_return]
QED

Theorem array_snapshot_coverage[local]:
  vv_type vv = ArrayT et bd ==>
  abi_decode_id_coverage (compile_snapshot_vv ce T vv)
Proof
  strip_tac >> coverage_steps
    [compile_snapshot_vv_def, compile_materialize_vv_def, is_word_type_def,
     is_bytestring_type_def, LET_DEF, compile_store_memory_def]
QED

Theorem snapshot_fragment_location[local]:
  MEM i (frag_code sm sc) ==>
  MEM i sc.cs_current_insts \/
  ?block. MEM block (emitted_blocks sm sc) /\ MEM i block.bb_instructions
Proof
  Cases_on `emitted_blocks sm sc`
  >- (simp[frag_code_def, emitted_insts_def] >>
      disch_then (irule o MATCH_MP MEM_DROP_IMP)) >>
  simp[frag_code_def, emitted_insts_def, MEM_FLAT, MEM_MAP] >>
  strip_tac
  >- (disj2_tac >> qexists_tac `LAST (h::t)` >>
      simp[GSYM (cj 2 MEM), MEM_LAST_NOT_NIL] >>
      drule MEM_DROP_IMP >> simp[]) >>
  metis_tac[MEM_FRONT, cj 2 MEM]
QED

Theorem snapshot_exit_excludes_fragment[local]:
  fn_has_code sm sc fn /\ create_layout sm sc /\ fn_inst_ids_distinct fn /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
  ~MEM i (frag_code sm sc)
Proof
  strip_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) bb.bb_instructions)` by
    metis_tac[fn_inst_ids_block_distinct] >>
  `isPREFIX sc.cs_current_insts bb.bb_instructions` by
    fs[fn_has_code_def] >>
  `i = EL (LENGTH sc.cs_current_insts) bb.bb_instructions /\
   LENGTH sc.cs_current_insts < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `MEM i bb.bb_instructions` by metis_tac[EL_MEM] >>
  drule snapshot_fragment_location >> strip_tac
  >- (fs[IS_PREFIX_APPEND] >> Cases_on `l` >>
      gvs[EL_APPEND_EQN, MAP_APPEND, ALL_DISTINCT_APPEND] >>
      fs[MEM_MAP] >> metis_tac[]) >>
  rename1 `MEM b (emitted_blocks sm sc)` >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[fn_has_code_def] >>
  `b = bb` by metis_tac[inst_in_unique_block, venomExecProofsTheory.lookup_block_MEM] >>
  `bb.bb_label = sc.cs_current_bb` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  fs[create_layout_def, MEM_MAP] >> metis_tac[]
QED

(* The exact coverage of the allocation, unwrap and store is what turns
   a numeric band into physical code.  The suffix need not fetch at all. *)
Theorem subscript_snapshot_band_fetch:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd /\
  fn_has_code sm sc fn /\ create_layout sm sc /\ fn_inst_ids_distinct fn /\
  ctor_segment_fetch fn a = SOME i /\ sm.cs_next_id <= i.inst_id /\
  i.inst_id < sc.cs_next_id ==>
  i.inst_id IN frag_ids sm sc /\ ~create_operand_at sc a
Proof
  strip_tac >> conj_tac >- simp[frag_ids_def] >>
  strip_tac >>
  fs[create_operand_at_def, ctor_segment_fetch_def, AllCaseEqs()] >>
  `cs_extends sm sc /\ ?j. MEM j (frag_code sm sc) /\ j.inst_id = i.inst_id` by
    metis_tac[array_snapshot_coverage, abi_decode_id_coverage_def] >>
  `MEM i (fn_insts fn)` by
    (irule lookup_block_fn_insts >> gvs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[EL_MEM]) >>
  `MEM j (fn_insts fn)` by metis_tac[abi_encode_frag_code_members] >>
  `j = i` by metis_tac[fn_insts_id_unique] >>
  metis_tac[snapshot_exit_excludes_fragment]
QED

(* The copied Subscript decomposition gives the two outer extension facts.
   Restrict the original caller's installed layout to the actual snapshot. *)
Theorem subscript_snapshot_band_fetch_from_layout:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd /\
  cs_extends sa sm /\ cs_extends sc sb /\
  fn_has_code sa sb fn /\ create_layout sa sb /\ fn_inst_ids_distinct fn /\
  ctor_segment_fetch fn a = SOME i /\ sm.cs_next_id <= i.inst_id /\
  i.inst_id < sc.cs_next_id ==>
  i.inst_id IN frag_ids sm sc /\ ~create_operand_at sc a
Proof
  strip_tac >>
  `cs_extends sm sc` by metis_tac[array_snapshot_coverage, abi_decode_id_coverage_def] >>
  `fn_has_code sm sc fn` by metis_tac[fn_has_code_mid] >>
  `create_layout sm sc` by metis_tac[create_layout_subinterval] >>
  metis_tac[subscript_snapshot_band_fetch]
QED
