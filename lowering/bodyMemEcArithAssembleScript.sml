Theory bodyMemEcArithAssemble
Ancestors
  bodyMemEcArithPayload bodyMemEcArithOperands exprSimAlloc
  fragGasSeqMem allocaHistoryFragment exprSimProps exprSimPrecompiles
  exprLoweringProps emitHelperProps compileEnv context venomState venomInst
  loweringHalt fragExecMem loweringPosts vyperValue
  bodyMemEcArithCode bodyMemEcArithPrefix instMemFrontier

(* Restatement of private exprSimECArith.ec_point_scratch_disjoint;
   original: alan-ref/base/exprSimECArithScript.sml.txt, lines 705-722. *)
Theorem ec_point_scratch_disjoint:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sb es v pop s /\
  eval_operand pop s = SOME w /\
  (!aid b sz. aid < sb.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch scratch_size b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint scratch scratch_size b sz) ==>
  regions_disjoint scratch scratch_size (w2n w) 64
Proof
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  strip_tac >> gvs[]
  >- (first_x_assum drule >> simp[] >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  first_x_assum drule >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

(* Restatement of private exprSimECArith.ec_point_fresh_scratch_disjoint;
   original reference lines 766-783. *)
Theorem ec_point_fresh_scratch_disjoint:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v pop s /\
  eval_operand pop s = SOME w /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch len b sz) /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     regions_disjoint scratch len b sz) ==>
  regions_disjoint scratch len (w2n w) 64
Proof
  strip_tac >> irule ec_point_scratch_disjoint >>
  qexistsl_tac [`cenv`, `cx`, `es`, `pop`, `s`, `lo`, `sa`, `v`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule exprSimPropsTheory.local_region_frame_fwd >>
      qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem ec_prefix_mem_lift:
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!i. MEM i code ==> MEM i.inst_opcode [ALLOCA; ADD; MLOAD; MSTORE]) /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
  alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[NoAsms, listTheory.EVERY_MEM, listTheory.FILTER_EQ_NIL] >>
     rpt strip_tac >>
     qpat_x_assum `!i. MEM i code ==> _` drule >>
     disch_tac >> Cases_on `i.inst_opcode` >> fs[is_terminator_def]) >>
  conj_tac
  >- (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all alloca_history_run_inst_seq >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem ecmul_prefix_safe:
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;scalar] ==> not_fresh_at sf x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 96 sf = (ib,sa) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    run_inst_seq_mem_ok (emitted_insts sf sm) s
Proof
  strip_tac >> drule_all ecmul_points_prefix >> strip_tac >>
  `96 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `context$compile_alloc_buffer 96 sf = _`
    (mp_then Any mp_tac literal_alloc_buffer_run) >>
  disch_then (qspecl_then [`func`, `cenv`, `cx`, `es`, `s`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  `s1.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand p s1 = SOME point /\ eval_operand scalar s1 = SOME wscalar` by
    (conj_tac >> Cases_on `p` >> Cases_on `scalar` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [p;ib.buf_operand;scalar] ==> not_fresh_at sa x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `regions_disjoint (w2n w) 96 (w2n point) 64` by
    (irule ec_point_fresh_scratch_disjoint >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `s1` >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next <= s1.vs_alloca_next` by
    (drule_all ec_alloc_buffer_frontier >> simp[]) >>
  `w2n w + 96 <= s1.vs_alloca_next` by
    (irule alloca_region_below_frontier >>
     conj_tac >- gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     qexistsl_tac [`sf.cs_next_id`, `w2n w`, `96`] >> simp[]) >>
  `w2n point + 64 <= s1.vs_alloca_next` by decide_tac >>
  drule_all ecmul_input_stores_mem >> strip_tac >>
  drule_all ecmul_input_stores_run >> strip_tac >>
  qexistsl_tac [`ib`, `ob`, `sa`, `sp`, `sm`] >> simp[] >>
  irule run_inst_seq_mem_ok_append >>
  conj_tac
  >- (rpt strip_tac >> irule ec_alloc_buffer_mem_ok >>
      goal_assum (drule_at Any)) >>
  irule run_inst_seq_mem_ok_append >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  irule ec_alloc_buffer_mem_ok >> goal_assum (drule_at Any)
QED

Theorem ecadd_prefix_safe:
  compile_ecadd_points p q sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 q s /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  (!x. MEM (Var x) [p;q] ==> not_fresh_at sf x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next /\
  w2n point2 + 64 <= s.vs_alloca_next ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    run_inst_seq_mem_ok (emitted_insts sf sm) s
Proof
  strip_tac >> drule_all ecadd_points_prefix >> strip_tac >>
  `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `context$compile_alloc_buffer 128 sf = _`
    (mp_then Any mp_tac literal_alloc_buffer_run) >>
  disch_then (qspecl_then [`func`, `cenv`, `cx`, `es`, `s`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  `s1.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand p s1 = SOME point /\ eval_operand q s1 = SOME point2` by
    (conj_tac >> Cases_on `p` >> Cases_on `q` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [p;q;ib.buf_operand] ==> not_fresh_at sa x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `regions_disjoint (w2n w) 128 (w2n point) 64` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ v2 q s` kall_tac >>
     irule ec_point_fresh_scratch_disjoint >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `s1` >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `regions_disjoint (w2n w) 128 (w2n point2) 64` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ v p s` kall_tac >>
     irule ec_point_fresh_scratch_disjoint >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `s1` >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next <= s1.vs_alloca_next` by
    (drule_all ec_alloc_buffer_frontier >> simp[]) >>
  `w2n w + 128 <= s1.vs_alloca_next` by
    (irule alloca_region_below_frontier >>
     conj_tac >- gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     qexistsl_tac [`sf.cs_next_id`, `w2n w`, `128`] >> simp[]) >>
  `w2n point + 64 <= s1.vs_alloca_next /\
   w2n point2 + 64 <= s1.vs_alloca_next` by decide_tac >>
  drule_all ecadd_input_stores_mem >> strip_tac >>
  drule_all ecadd_input_stores_run >> strip_tac >>
  qexistsl_tac [`ib`, `ob`, `sa`, `sp`, `sm`] >> simp[] >>
  irule run_inst_seq_mem_ok_append >> conj_tac
  >- (rpt strip_tac >> irule ec_alloc_buffer_mem_ok >>
      goal_assum (drule_at Any)) >>
  irule run_inst_seq_mem_ok_append >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  irule ec_alloc_buffer_mem_ok >> goal_assum (drule_at Any)
QED
