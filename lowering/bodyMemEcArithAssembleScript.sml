Theory bodyMemEcArithAssemble
Ancestors
  bodyMemEcArithPayload bodyMemEcArithOperands exprSimAlloc
  fragGasSeqMem allocaHistoryFragment exprSimProps exprSimPrecompiles
  exprLoweringProps emitHelperProps compileEnv context venomState venomInst
  loweringHalt fragExecMem loweringPosts vyperValue

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
