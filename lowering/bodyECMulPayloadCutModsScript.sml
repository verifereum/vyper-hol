(* ECMul's two point loads and scalar store on the allocated input row. *)
Theory bodyECMulPayloadCutMods
Ancestors
  bodyPtrPrecompileBuiltinsPrefixes bodyMemEcArithPayload bodyMemEcArithTransfers
  instSeqPtrLo fragGasSeqPtr revertReasonPrefixFramePtr exprSimHash memSafeRun
  arithmeticProps loweringStateRelDefs exprLoweringProps compileEnv
  venomState venomInst ptrDiscipline words list rich_list valueEncodingProps
  exprSimAbiEncodeMemoryLength typedMemoryCopy
Libs dep_rewrite

val _ = Parse.hide "cp";

Theorem ecmul_payload_code[local]:
  (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 0w]; emit_void MSTORE [y;v] od) ca = ((),c1) /\
  (do x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 32w]; emit_void MSTORE [y;v] od) c1 = ((),c2) /\
  (do y <- emit_op ADD [b; Lit 64w]; emit_void MSTORE [y;scalar] od) c2 = ((),cp) ==>
  (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 0w]; emit_void MSTORE [y;v];
      x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 32w]; emit_void MSTORE [y;v];
      y <- emit_op ADD [b; Lit 64w]; emit_void MSTORE [y;scalar] od) ca = ((),cp) /\
  emitted_insts ca cp = emitted_insts ca c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 cp /\
  cp.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cp /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; MSTORE]) (emitted_insts ca cp)
Proof
  strip_tac >> conj_tac
  >- (`(do
          (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
              y <- emit_op ADD [b; Lit 0w]; emit_void MSTORE [y;v] od);
          (do x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
              y <- emit_op ADD [b; Lit 32w]; emit_void MSTORE [y;v] od);
          (do y <- emit_op ADD [b; Lit 64w]; emit_void MSTORE [y;scalar] od) od)
          ca = ((),cp)` suffices_by simp[comp_ignore_bind_def, comp_bind_assoc] >>
      simp[comp_ignore_bind_def, comp_bind_def]) >>
  qpat_assum `_ ca = ((),c1)` (strip_assume_tac o MATCH_MP ec_point_word_transfer_shape) >>
  qpat_assum `_ c1 = ((),c2)` (strip_assume_tac o MATCH_MP ec_point_word_transfer_shape) >>
  qpat_assum `_ c2 = ((),cp)` (strip_assume_tac o MATCH_MP ec_scalar_store_shape) >>
  `emitted_insts c1 cp = emitted_insts c1 c2 ++ emitted_insts c2 cp` by
    (irule emitted_insts_prefix_split >> simp[]) >>
  `emitted_insts ca cp = emitted_insts ca c1 ++ emitted_insts c1 cp` by
    (irule emitted_insts_prefix_split >> simp[listTheory.APPEND_ASSOC]) >>
  simp[listTheory.APPEND_ASSOC, mk_inst_def]
QED

Theorem ecmul_payload_origin[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; MSTORE]) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK r /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  inst_seq_ptr (<|d_stor := K (K {}); d_trans := K (K {});
                  d_imm := K {}; d_ret := K {}|>) 0 ctx func PG G tn code s Gf tnf ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (r with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tnf)) /\
  tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     first_assum (irule_at Any) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (qpat_assum `EVERY (\i. MEM i.inst_opcode _) code`
       (assume_tac o REWRITE_RULE [EVERY_MEM, BETA_THM]) >>
     simp[EVERY_MEM, FILTER_EQ_NIL] >> conj_tac >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i code ==> _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
     gvs[is_terminator_def]) >>
  `ctx_has_dalloca ctx ==> !pre i post u. code = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode _) code`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[listTheory.MEM_APPEND] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (qx_gen_tac `D` >>
      qpat_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
        (qspec_then `D` assume_tac) >>
      qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> DELEGATECALL /\
              i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
              i.inst_opcode <> SSTORE /\ i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) code` by
    (qpat_assum `EVERY (\i. MEM i.inst_opcode _) code`
       (assume_tac o REWRITE_RULE [EVERY_MEM, BETA_THM]) >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i code ==> _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >> gvs[]) >>
  drule_all inst_seq_ptr_nonmemory_taint_frame >> simp[]
QED

Theorem ecmul_payload_words[local]:
  mem = (mstore (b+64) w (mstore (b+32) v (mstore b u s))).vs_memory ==>
  mem_word_at b mem = u /\ mem_word_at (b+32) mem = v /\
  mem_word_at (b+64) mem = w /\ typed_copy_frame b 96 s.vs_memory mem
Proof
  strip_tac >> gvs[] >>
  conj_tac >- simp[mstore_mem_word_at_disjoint, mstore_mem_word_at_same] >>
  conj_tac >- simp[mstore_mem_word_at_disjoint, mstore_mem_word_at_same] >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt strip_tac >> dep_rewrite.DEP_REWRITE_TAC
        [Q.INST [`b` |-> `b`, `sz` |-> `96`] (SPEC_ALL mstore_region_frame)] >>
      simp[GSYM arithmeticTheory.ADD_ASSOC, regions_disjoint_def] >> decide_tac) >>
  ntac 2 (irule arithmeticTheory.LESS_EQ_TRANS >>
          irule_at (Pos last) abi_encode_mstore_memory_length) >>
  irule abi_encode_mstore_memory_length
QED

Theorem ecmul_payload_cut_mods:
  (do x <- emit_op ADD [Var root; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [Var src; Lit 0w]; emit_void MSTORE [y;v] od) ca = ((),c1) /\
  (do x <- emit_op ADD [Var root; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [Var src; Lit 32w]; emit_void MSTORE [y;v] od) c1 = ((),c2) /\
  (do y <- emit_op ADD [Var src; Lit 64w]; emit_void MSTORE [y;scalar] od) c2 = ((),cp) /\
  lookup_var root s = SOME wp /\ lookup_var src s = SOME wi /\
  ptr_covers G tn root s 64 /\ ptr_covers G tn src s 96 /\
  not_fresh_at ca root /\ not_fresh_at ca src /\
  eval_operand scalar s = SOME w /\ op_taint tn scalar = {} /\
  (!l. scalar <> Label l) /\ (!z. scalar = Var z ==> not_fresh_at ca z) /\
  w2n wp+64 < dimword (:256) /\ w2n wi+96 < dimword (:256) /\
  w2n wp+64 <= s.vs_alloca_next /\ w2n wi+96 <= s.vs_alloca_next /\
  (!i. w2n wp <= i /\ i < w2n wp+64 ==> i NOTIN tn.t_mem) /\
  regions_disjoint (w2n wi) 96 (w2n wp) 64 /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  isPREFIX (emitted_insts ca cp) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?r t G' tn'.
    run_inst_seq (emitted_insts ca cp) s = OK r /\
    t = r with vs_inst_idx := LENGTH cp.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (r with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    t.vs_memory = (mstore (w2n wi+64) w
      (mstore (w2n wi+32) (mem_word_at (w2n wp+32) s.vs_memory)
        (mstore (w2n wi) (mem_word_at (w2n wp) s.vs_memory) s))).vs_memory /\
    mem_word_at (w2n wi) t.vs_memory = mem_word_at (w2n wp) s.vs_memory /\
    mem_word_at (w2n wi+32) t.vs_memory = mem_word_at (w2n wp+32) s.vs_memory /\
    mem_word_at (w2n wi+64) t.vs_memory = w /\
    typed_copy_state_frame ca (w2n wi) 96 s t /\
    (!z. not_fresh_at ca z ==> lookup_var z t = lookup_var z s /\
                             FLOOKUP G' z = FLOOKUP G z /\
                             op_taint tn' (Var z) = op_taint tn (Var z)) /\
    lookup_var src t = SOME wi /\ ptr_covers G' tn' src t 96 /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n wi <= i /\ i < w2n wi+96} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all_then strip_assume_tac ecmul_payload_code >>
  `eval_operand (Var root) s = SOME wp /\ eval_operand (Var src) s = SOME wi` by
    simp[eval_operand_def] >>
  `!z. MEM (Var z) [Var root;Var src;scalar] ==> not_fresh_at ca z` by
    (simp[] >> metis_tac[]) >>
  drule_all_then (qx_choose_then `r` strip_assume_tac) ecmul_input_stores_run >>
  drule_all_then assume_tac ecmul_input_stores_mem >>
  qpat_assum `r.vs_memory = _` (mp_tac o MATCH_MP ecmul_payload_words) >> strip_tac >>
  drule_all ecmul_input_staging_checked >>
  disch_then (qspecl_then [`func`, `PG`, `<|d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {}|>`]
      (qx_choosel_then [`raw`,`Gf`,`tnf`] strip_assume_tac)) >>
  `raw = r` by
    (qpat_x_assum `run_inst_seq _ s = OK raw` mp_tac >>
     qpat_assum `emitted_insts ca cp = _` (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_x_assum `raw = r` SUBST_ALL_TAC >>
  `inst_seq_ptr (<|d_stor := K (K {}); d_trans := K (K {});
                   d_imm := K {}; d_ret := K {}|>) 0 ctx func PG G tn
     (emitted_insts ca cp) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> simp[venom_state_component_equality]) >>
  drule_all ecmul_payload_origin >> disch_then (qspec_then `explicit` strip_assume_tac) >>
  `LENGTH cp.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts ca cp)` by simp[] >>
  qexistsl_tac [`r`, `r with vs_inst_idx := LENGTH cp.cs_current_insts`, `Gf`, `tnf`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `LENGTH cp.cs_current_insts = _`
        (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `typed_copy_state_frame ca (w2n wi) 96 s
      (r with vs_inst_idx := LENGTH cp.cs_current_insts)` by
    (qpat_x_assum `r.vs_memory = _` kall_tac >>
     qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[Once venom_state_component_equality] >> strip_tac >>
     fs[typed_copy_state_frame_def, lookup_var_def,
        Once venom_state_component_equality]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qpat_x_assum `r.vs_memory = _` kall_tac >> fs[lookup_var_def]
QED
