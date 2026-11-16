Theory bodyFullAbiDecodeLoopDestination
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeMemberPrefix decoderArraySetupPtr
  calldataDynOwned bodyPtrBopScalarOutcome stateFrame freshWrites
  abiDecodePtrBytesTail instSeqPtrLo fragGasSeqPtr fragExecMem abiDecodePtrHead
  loweringShapeRules fragGasOriginPtrLoop
  allocaFootprint emitHelperProps exprLoweringProps abiDecoderIndexedAddress
  codegenRel ptrDiscipline decoderNavigationPtr decoderGhostFramePtr fragExec
  abiDecoderReentry loweringStateRelDefs compileEnv emitHelper
  venomInst venomExecSemantics venomState words list rich_list finite_map arithmetic

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

Theorem abi_decode_loop_destination_joint:
  abi_decode_indexed_address (Var dst) idx msz sa = (child_dst,sb) /\
  lookup_var dst s = SOME (n2w d) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live sa.cs_next_var (Var dst) /\
  abi_decoder_operand_live sa.cs_next_var idx /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\ j<n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gu tnu child.
    child_dst = Var child /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gu tnu /\
    eval_operand child_dst u = SOME (n2w (d+32+j*msz)) /\
    ptr_covers Gu tnu child u msz /\
    FLOOKUP Gu child = SOME (output_base,output_cap) /\
    op_taint tnu child_dst = {} /\
    abi_decoder_operand_live sb.cs_next_var child_dst /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    tnu.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var dst) s = SOME (n2w d)` by simp[eval_operand_def] >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  `(!x. idx = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa dst` by
    (conj_tac >- (rpt strip_tac >> gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
     gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `32+j*msz+msz <= 32+n*msz` by
    (`(j+1)*msz <= n*msz` by simp[LE_MULT_RCANCEL] >>
     pop_assum mp_tac >> pure_rewrite_tac [RIGHT_ADD_DISTRIB,MULT_CLAUSES] >> decide_tac) >>
  `output_base+output_cap < dimword(:256)` by fs[] >>
  `d+32+j*msz < dimword(:256) /\ msz < dimword(:256)` by
    (`msz <= n*msz` by (simp[LE_MULT_RCANCEL] >> decide_tac) >> decide_tac) >>
  `?data_op c1 offset_op c2.
    emit_op ADD [Var dst; Lit 32w] sa = (data_op,c1) /\
    emit_op MUL [idx; Lit (n2w msz)] c1 = (offset_op,c2) /\
    emit_op ADD [data_op;offset_op] c2 = (child_dst,sb)` by
    (qpat_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_indexed_address_def, comp_bind_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
     metis_tac[]) >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 sb` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def] >>
     metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `fn_has_code sa c1 fn /\ fn_has_code c1 c2 fn /\ fn_has_code c2 sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `?q. data_op = Var q` by
    (qpat_assum `emit_op ADD _ sa = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
     metis_tac[]) >>
  qpat_x_assum `data_op = _` SUBST_ALL_TAC >>
  `op_taint tn (Var dst) = {}` by
    fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\
   op_taint tn (Lit 32w) = {} /\ 32+(j*msz+msz) <= 32+n*msz /\
   w2n (n2w d : 256 word)+(32+n*msz) < dimword(:256)` by
    (simp[eval_operand_def, op_taint_def, w2n_n2w] >> decide_tac) >>
  drule_all (abiDecodePtrBytesTailTheory.abi_decode_ptr_output_address |>
    Q.INST [`cap` |-> `32+n*msz`, `q` |-> `32`, `k` |-> `j*msz+msz`,
      `D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`fn`, `PG`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_covers G1 tn1 q u1 (j*msz+msz)` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  `FLOOKUP G1 q = SOME (output_base,output_cap)` by
    (simp[Abbr `G1`, ptrDisciplineTheory.step_prov_def,
      ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
      ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
      mk_inst_def, FLOOKUP_UPDATE]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts /\
   s1.vs_memory = s.vs_memory /\ s1.vs_allocas = s.vs_allocas /\
   s1.vs_alloca_next = s.vs_alloca_next /\ s1.vs_labels = s.vs_labels /\
   allocas_from lo s1` by
    (qpat_assum `emit_op ADD _ sa = _` (mp_tac o MATCH_MP emit_op_facts) >>
     strip_tac >>
     simp[Abbr `s1`, Abbr `u1`, update_var_def, allocas_from_def]) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa c1) s G1 tn1` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >>
     drule_all (abiDecodePtrBytesTailTheory.abi_decode_ptr_output_address |>
       Q.INST [`cap` |-> `32+n*msz`, `q` |-> `32`, `k` |-> `j*msz+msz`,
         `D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
     simp[LET_THM, Abbr `G1`, Abbr `tn1`, Abbr `u1`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK s1,G1,tn1)` by
    (gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> GAS) (emitted_insts sa c1) /\
      run_inst_seq_mem_ok (emitted_insts sa c1) s` by
       (qpat_assum `emit_op ADD _ sa = _`
          (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
        simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
          instMemFrontierTheory.below_frontier_no_ranges] >>
        BasicProvers.TOP_CASE_TAC >> simp[]) >>
     qpat_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     `c1.cs_current_bb = sa.cs_current_bb` by
       (qpat_assum `emit_op ADD _ sa = _` (mp_tac o MATCH_MP emit_op_facts) >>
        strip_tac >> asm_rewrite_tac[]) >>
     drule_all emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     simp[Abbr `s1`, Abbr `u1`]) >>
  `eval_operand idx s1 = SOME (n2w j) /\
   op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    (Cases_on `idx` >>
     fs[eval_operand_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  `?z. offset_op = Var z /\
    emitted_insts c1 c2 = [mk_inst c1.cs_next_id MUL
      [idx;Lit (n2w msz)] [z]]` by
    (qpat_assum `emit_op MUL _ _ = _`
      (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> metis_tac[]) >>
  qpat_x_assum `offset_op = _` SUBST_ALL_TAC >>
  qabbrev_tac `u2 = update_var z (n2w j * n2w msz) s1` >>
  `run_inst_seq (emitted_insts c1 c2) s1 = OK u2` by
    simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, Abbr `u2`] >>
  `eval_operand (Lit (n2w msz)) s1 = SOME (n2w msz) /\
   op_taint tn1 (Lit (n2w msz)) = {} /\
   op_prov G1 (Lit (n2w msz)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (emit_scalar_binop_endpoint_ptr_origin_core |>
    Q.SPEC `MUL` |> SRULE []) >>
  disch_then (qspecl_then [`ARB`, `cx`, `ctx`, `PG`, `ARB`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qabbrev_tac `s2 = u2 with vs_inst_idx := LENGTH c2.cs_current_insts` >>
  `~s2.vs_halted /\ s2.vs_current_bb = c2.cs_current_bb /\
   s2.vs_inst_idx = LENGTH c2.cs_current_insts /\
   s2.vs_memory = s.vs_memory /\ s2.vs_allocas = s.vs_allocas /\
   s2.vs_alloca_next = s.vs_alloca_next /\ s2.vs_labels = s.vs_labels /\
   allocas_from lo s2` by
    (qpat_assum `emit_op MUL _ _ = _` (mp_tac o MATCH_MP emit_op_facts) >>
     strip_tac >> simp[Abbr `s2`, Abbr `u2`, update_var_def, allocas_from_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s1,G1,tn1) [] (OK s2,G2,tn2)` by
    (gen_tac >> simp[Abbr `s2`]) >>
  `not_fresh_at c1 q` by
    (qpat_assum `emit_op ADD _ sa = _` (mp_tac o MATCH_MP emit_op_facts) >>
     strip_tac >> gvs[]) >>
  `lookup_var q s2 = SOME (n2w (d+32)) /\
   FLOOKUP G2 q = SOME (output_base,output_cap) /\
   op_taint tn2 (Var q) = {}` by
    (qpat_assum `!q. not_fresh_at c1 q ==> _` (qspec_then `q` mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then strip_assume_tac >>
     `op_taint tn1 (Var q) = {}` by
       (gvs[bodyPtrDefsTheory.ptr_covers_def]) >>
     fs[Abbr `s2`, lookup_var_def, GSYM word_add_n2w]) >>
  `ptr_covers G2 tn2 q s2 (j*msz+msz)` by
    (irule ptr_covers_frame >> qexistsl_tac [`G1`, `u1`, `tn1`] >>
     fs[Abbr `s2`, Abbr `s1`, lookup_var_def] >>
     gvs[bodyPtrDefsTheory.ptr_covers_def, word_add_n2w]) >>
  `eval_operand (Var z) s2 = SOME (n2w (j*msz)) /\
   op_taint tn2 (Var z) = {} /\
   w2n (n2w (d+32):256 word)+(j*msz+msz) < dimword(:256)` by
    (simp[Abbr `s2`, Abbr `u2`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, word_mul_n2w, w2n_n2w] >> decide_tac) >>
  `?child. child_dst = Var child` by metis_tac[emit_op_facts] >>
  qpat_x_assum `child_dst = Var child` SUBST_ALL_TAC >>
  `j*msz+msz <= j*msz+msz` by simp[] >>
  drule_all (abiDecodePtrBytesTailTheory.abi_decode_ptr_output_address |>
    Q.INST [`cap` |-> `j*msz+msz`, `q` |-> `j*msz`, `k` |-> `msz`,
      `D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`fn`, `PG`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_covers G3 tn3 child u3 msz` >>
  qabbrev_tac `s3 = u3 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `FLOOKUP G3 child = SOME (output_base,output_cap)` by
    simp[Abbr `G3`, ptrDisciplineTheory.step_prov_def,
      ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
      ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
      mk_inst_def, FLOOKUP_UPDATE] >>
  `~s3.vs_halted /\ s3.vs_current_bb = sb.cs_current_bb /\
   s3.vs_inst_idx = LENGTH sb.cs_current_insts /\
   s3.vs_memory = s.vs_memory /\ s3.vs_allocas = s.vs_allocas /\
   s3.vs_alloca_next = s.vs_alloca_next /\ s3.vs_labels = s.vs_labels /\
   allocas_from lo s3` by
    (qpat_assum `emit_op ADD _ c2 = _` (mp_tac o MATCH_MP emit_op_facts) >>
     strip_tac >> simp[Abbr `s3`, Abbr `u3`, update_var_def, allocas_from_def]) >>
  `lo <= s2.vs_alloca_next` by simp[] >>
  `!D. inst_seq_ptr D lo ctx fn PG G2 tn2 (emitted_insts c2 sb) s2 G3 tn3` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >>
     drule_all (abiDecodePtrBytesTailTheory.abi_decode_ptr_output_address |>
       Q.INST [`cap` |-> `j*msz+msz`, `q` |-> `j*msz`, `k` |-> `msz`,
         `D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
     simp[LET_THM, Abbr `G3`, Abbr `tn3`, Abbr `u3`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s2,G2,tn2) [] (OK s3,G3,tn3)` by
    (gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> GAS) (emitted_insts c2 sb) /\
      run_inst_seq_mem_ok (emitted_insts c2 sb) s2` by
       (qpat_assum `emit_op ADD _ c2 = _`
          (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
        simp[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
          instMemFrontierTheory.below_frontier_no_ranges] >>
        BasicProvers.TOP_CASE_TAC >> simp[]) >>
     qpat_assum `!D. inst_seq_ptr D lo _ _ _ G2 _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     `sb.cs_current_bb = c2.cs_current_bb` by
       (qpat_assum `emit_op ADD _ c2 = _` (mp_tac o MATCH_MP emit_op_facts) >>
        strip_tac >> asm_rewrite_tac[]) >>
     drule_all emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     simp[Abbr `s3`, Abbr `u3`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK s3,G3,tn3)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G2`, `s2`, `tn2`] >> simp[]) >>
  `(!i. MEM i (emitted_insts sa sb) ==> MEM i.inst_opcode [ADD;MUL]) /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = 3 + LENGTH sa.cs_current_insts` by
    (qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_indexed_address_def, emit_op_def, emit_inst_def,
       comp_bind_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `MEM i _` mp_tac >>
     pure_rewrite_tac [emitted_insts_def, compile_state_accfupds,
       compile_state_accessors, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND,
       combinTheory.K_THM, MEM, mk_inst_def, instruction_accessors] >>
     rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s3 = lookup_var x s /\
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at c1 x /\ not_fresh_at c2 x` by
       (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[] >>
        qpat_assum `emit_op ADD _ sa = _` (mp_tac o MATCH_MP emit_op_facts) >>
        qpat_assum `emit_op MUL _ c1 = _` (mp_tac o MATCH_MP emit_op_facts) >>
        rpt strip_tac >> decide_tac) >>
     fs[Abbr `s2`, lookup_var_def] >> metis_tac[]) >>
  `state_frame s3 = state_frame (s with vs_inst_idx := s3.vs_inst_idx)` by
    simp[Abbr `s3`, Abbr `u3`, Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`,
      update_var_def, state_frame_def] >>
  `alloca_history fn s3` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     fs[inst_extends_def, IS_PREFIX_APPEND, EVERY_MEM, MEM] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >> strip_tac >> simp[]) >>
  `(^owned_decoder_state) sb s3 G3 tn3` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >> simp[]) >>
  `ptr_covers G3 tn3 child s3 msz` by
    (simp[bodyPtrDefsTheory.ptr_covers_def, Abbr `s3`, lookup_var_def] >>
     metis_tac[]) >>
  `eval_operand (Var child) s3 = SOME (n2w (d+32+j*msz))` by
    (metis_tac[eval_operand_def, Abbr `s3`, lookup_var_def, word_add_n2w, ADD_ASSOC]) >>
  `op_taint tn3 (Var child) = {}` by
    (qpat_assum `ptr_covers G3 tn3 child s3 msz` mp_tac >>
     pure_rewrite_tac[bodyPtrDefsTheory.ptr_covers_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`s3`, `G3`, `tn3`] >>
  fs[] >> rpt conj_tac >> metis_tac[]
QED
