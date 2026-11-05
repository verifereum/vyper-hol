Theory bodyIntCallMappingFrame
Ancestors
  exprSimHash bodyIntCallSemanticFrame exprLowering exprLoweringProps
  valueEncodingProps valueEncodingProofs vyperStorage venomExecSemantics
  byte words emitHelper emitHelperProps compileEnv venomInst venomState context list
  abiDecodeStaticProps valueEncoding fragExec rich_list

(* The scratch layout is base-slot first, then the already encoded key. *)
Theorem mapping_scratch_bytes:
  mem_bytes_at a 64 (mstore (a + 32) key (mstore a slot s)).vs_memory =
    word_to_bytes_be slot ++ word_to_bytes_be key
Proof
  rewrite_tac[GSYM (EVAL ``32 + 32:num``)] >>
  rewrite_tac[mem_bytes_at_split_padded] >>
  simp[mstore_mem_bytes_at_disjoint, mem_bytes_at_mstore_same,
       word_to_bytes_be_def]
QED

Theorem mapping_scratch_hash:
  word_of_bytes T (0w:bytes32)
    (Keccak_256_w64
      (mem_bytes_at a 64 (mstore (a + 32) key (mstore a slot s)).vs_memory)) =
  hashmap_slot slot key
Proof
  simp[mapping_scratch_bytes, hashmap_slot_def, word_of_bytes_be_def]
QED

Theorem mapping_hash_tail_run:
  !ptr base key sa s1 kp s2 s3 out sb s addr slot kw.
  emit_void MSTORE [ptr; base] sa = ((),s1) /\
  emit_op ADD [ptr; Lit 32w] s1 = (kp,s2) /\
  emit_void MSTORE [kp; key] s2 = ((),s3) /\
  emit_op SHA3 [ptr; Lit 64w] s3 = (out,sb) /\
  eval_operand ptr s = SOME addr /\ eval_operand base s = SOME slot /\
  eval_operand key s = SOME kw /\ w2n addr + 64 < dimword (:256) /\
  (!x. ptr = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (hashmap_slot slot kw) /\
    t.vs_memory = (mstore (w2n addr + 32) kw (mstore (w2n addr) slot s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_write2_def] >>
  rename1 `eval_operand pop s = SOME addr` >>
  `eval_operand pop (mstore (w2n addr) slot s) = SOME addr` by
    metis_tac[eval_operand_mstore] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ mid` >>
  `eval_operand key mid = SOME kw` by
    (Cases_on `key` >>
     gvs[Abbr `mid`, eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  `eval_operand pop mid = SOME addr` by
    (Cases_on `pop` >>
     gvs[Abbr `mid`, eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
       eval_operand_def, Abbr `mid`, lookup_var_update_var] >>
  `w2n (addr + 32w) = w2n addr + 32` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ stored` >>
  `eval_operand pop stored = SOME addr` by
    (simp[Abbr `stored`] >> metis_tac[eval_operand_mstore]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       GSYM mem_bytes_at_def] >>
  `stored.vs_memory =
    (mstore (w2n addr + 32) kw (mstore (w2n addr) slot s)).vs_memory` by
    (simp_tac (srw_ss()) [Abbr `stored`] >>
     asm_simp_tac (srw_ss()) [mstore_def, update_var_def, LET_THM]) >>
  simp[run_inst_seq_def, mapping_scratch_hash, lookup_var_update_var] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >-
    simp_tac (srw_ss()) [Abbr `stored`, mstore_def, update_var_def, LET_THM] >>
  rpt strip_tac >>
  qpat_x_assum `not_fresh_at sa x` mp_tac >>
  simp[not_fresh_at_def] >> strip_tac >>
  first_assum (qspec_then `sa.cs_next_var` mp_tac) >>
  first_x_assum (qspec_then `sa.cs_next_var + 1` mp_tac) >>
  simp[] >> rpt strip_tac >>
  simp_tac (srw_ss()) [Abbr `stored`, lookup_var_def, update_var_def,
                      mstore_def, LET_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem mapping_tail_code:
  !ptr base key sa s1 kp s2 s3 out sb.
  emit_void MSTORE [ptr; base] sa = ((),s1) /\
  emit_op ADD [ptr; Lit 32w] s1 = (kp,s2) /\
  emit_void MSTORE [kp; key] s2 = ((),s3) /\
  emit_op SHA3 [ptr; Lit 64w] s3 = (out,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sa.cs_next_var <= sb.cs_next_var
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem mapping_alloc_code:
  compile_alloc_buffer 64 sa = (buf,sm) ==>
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at sm x)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
      not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem mapping_scratch_region_frame:
  regions_disjoint a 64 b len ==>
  mem_bytes_at b len (mstore (a + 32) kw (mstore a slot s)).vs_memory =
  mem_bytes_at b len s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b len (mstore (a + 32) kw (mstore a slot s)).vs_memory =
   mem_bytes_at b len (mstore a slot s).vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`a`, `64`] >> simp[]) >>
  simp[] >> irule mstore_region_frame >> qexistsl_tac [`a`, `64`] >> simp[]
QED

Theorem mapping_scratch_state_rel:
  !ctx func cenv cx es s a slot kw inst.
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (a,64) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint a 64 b len) ==>
  stmt_state_rel ctx func cenv cx es (mstore (a + 32) kw (mstore a slot s))
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore a slot s)` by
    (irule exprSimAllocTheory.literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`a`, `inst`, `64`] >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def]) >>
  irule exprSimAllocTheory.literal_mstore_state_rel >> simp[] >>
  qexistsl_tac [`a`, `inst`, `64`] >> simp[mstore_def] >>
  rpt strip_tac >>
  gvs[local_region_def, lookup_var_def, regions_disjoint_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem mapping_tail_state_rel:
  !ctx func cenv cx es sa s t a slot kw inst.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (a,64) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint a 64 b len) /\
  t.vs_memory = (mstore (a + 32) kw (mstore a slot s)).vs_memory /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore (a + 32) kw (mstore a slot s))` by
    (irule mapping_scratch_state_rel >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `inst` >> simp[]) >>
  `t = (mstore (a + 32) kw (mstore a slot s)) with vs_vars := t.vs_vars` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     qpat_x_assum `t.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [venom_state_component_equality, mstore_def, LET_THM] >>
     metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  irule stmt_state_rel_fresh_vars >> simp[] >> qexists_tac `sa` >> simp[] >>
  simp_tac (srw_ss()) [mstore_def, LET_THM] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
  simp[lookup_var_def]
QED

Theorem compile_mapping_subscript_run:
  !base key sa out sb s slot kw ctx func cenv cx es.
  compile_mapping_subscript base key sa = (out,sb) /\
  eval_operand base s = SOME slot /\ eval_operand key s = SOME kw /\
  (!x. base = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t (addr:bytes32) allocated.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (hashmap_slot slot kw) /\
    t.vs_memory =
      (mstore (w2n addr + 32) kw (mstore (w2n addr) slot s)).vs_memory /\
    (t with <|vs_vars := allocated.vs_vars; vs_memory := allocated.vs_memory|>) = allocated /\
    stmt_state_rel ctx func cenv cx es allocated /\
    stmt_state_rel ctx func cenv cx es t /\
    allocated.vs_memory = s.vs_memory /\
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n addr) 64 b len) /\
    (!name b len. local_region cenv es.scopes allocated name b len ==>
       regions_disjoint (w2n addr) 64 b len) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    local_ptrs_reserved cenv sb /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_mapping_subscript_def, LET_THM, comp_bind_def,
     comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer 64 sa = (buf,sm)` >>
  rename1 `eval_operand bop s = SOME slot` >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all exprSimAllocTheory.hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand bop allocated = SOME slot /\
   eval_operand key allocated = SOME kw` by
    (conj_tac >> Cases_on `bop` >> Cases_on `key` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  drule mapping_alloc_code >> strip_tac >>
  `!x. key = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule_all mapping_hash_tail_run >> strip_tac >>
  drule_all mapping_tail_code >> strip_tac >>
  suspend "compose"
QED

Resume compile_mapping_subscript_run[compose]:
  rename1 `run_inst_seq (emitted_insts sm sb) allocated = OK final` >>
  `run_inst_seq (emitted_insts sa sb) s = OK final /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `contract_storage allocated = contract_storage s /\
   contract_transient allocated = contract_transient s` by
    (drule_all exprSimAllocTheory.alloc_buffer_storage >> simp[]) >>
  `contract_storage final = contract_storage allocated /\
   contract_transient final = contract_transient allocated /\
   final.vs_allocas = allocated.vs_allocas` by
    (qpat_x_assum `final with <|vs_vars := _; vs_memory := _|> = allocated` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_state_component_equality, contract_storage_def,
          contract_transient_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es final` by
    (drule_at (Pat `_.vs_memory = _`) mapping_tail_state_rel >>
     disch_then irule >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
          [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
     qexists_tac `sm` >> simp[] >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume compile_mapping_subscript_run[finish]:
  `!aid b len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     mem_bytes_at b len final.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `final.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `allocated.vs_memory = _` (fn th =>
       pure_once_rewrite_tac[GSYM th]) >>
     irule mapping_scratch_region_frame >>
     qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len final.vs_memory = mem_bytes_at b len s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl_tac [`sa`, `es.scopes`, `allocated`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `final.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `allocated.vs_memory = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule mapping_scratch_region_frame >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` drule >> simp[]) >>
  qexistsl_tac [`final`, `addr`, `allocated`] >> simp[] >>
  conj_tac >-
    (simp_tac (srw_ss()) [mstore_def, LET_THM] >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `final with <|vs_vars := _; vs_memory := _|> = allocated` mp_tac >>
     qpat_x_assum `allocated.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `final.vs_memory = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_mapping_subscript_run

Theorem compile_mapping_subscript_code:
  !base key sa out sb.
  compile_mapping_subscript base key sa = (out,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (emitted_insts sa sb)
Proof
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def, same_blocks_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem compile_mapping_subscript_alloc_code:
  !base key sa out sb func.
  compile_mapping_subscript base key sa = (out,sb) /\ fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >> drule compile_mapping_subscript_code >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND]
QED

Theorem compile_mapping_subscript_frame_frag:
  !base key sa out sb s0 slot kw ctx func cenv cx es R.
  compile_mapping_subscript base key sa = (out,sb) /\ fn_has_code sa sb func /\
  eval_operand base s0 = SOME slot /\ eval_operand key s0 = SOME kw /\
  (!x. base = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. eval_operand out t = SOME (hashmap_slot slot kw) /\
      stmt_state_rel ctx func cenv cx es t /\
      contract_storage t = contract_storage s0 /\
      contract_transient t = contract_transient s0 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
         mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) /\
      (!name b len. local_region cenv es.scopes s0 name b len ==>
         mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory)) R
Proof
  rpt strip_tac >>
  drule compile_mapping_subscript_code >> strip_tac >>
  drule_all compile_mapping_subscript_alloc_code >> strip_tac >>
  irule hash_run_frag >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all compile_mapping_subscript_run >> strip_tac >>
  qexists_tac `t` >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      contract_storage_def, contract_transient_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Encoding boundary: dynamic bytes and strings are hashed before their
   encoded word is stored; address and fixed bytes use different padding. *)
Theorem mapping_scratch_hash_int:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (i2w i) (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key kt (IntV i))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_flag:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (n2w n) (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key kt (FlagV n))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_bool:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (if b then 1w else 0w)
      (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key kt (BoolV b))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_address:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (word_of_bytes_be (PAD_LEFT 0w 32 bs))
      (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key (BaseT AddressT) (BytesV bs))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_fixed_bytes:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (word_of_bytes_be (PAD_RIGHT 0w 32 bs))
      (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key (BaseT (BytesT (Fixed n))) (BytesV bs))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_dynamic_bytes:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32) (word_of_bytes_be (Keccak_256_w64 bs))
      (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key (BaseT (BytesT (Dynamic n))) (BytesV bs))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem mapping_scratch_hash_string:
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (mem_bytes_at a 64 (mstore (a + 32)
      (word_of_bytes_be (Keccak_256_w64 (MAP n2w_o_ORD str)))
      (mstore a slot s)).vs_memory)) =
  hashmap_slot slot (encode_hashmap_key (BaseT (StringT n)) (StringV str))
Proof
  simp[mapping_scratch_hash, encode_hashmap_key_def]
QED

Theorem compile_subscript_mapping_shape:
  !cfn cenv ret_ty ty base_e idx_e sa out sb kt vt.
  place_type cenv base_e = MapPT kt vt /\
  compile_subscript cfn cenv ret_ty ty base_e idx_e sa = (out,sb) ==>
  ?base_vv s1 key_op s2 hashed_key s3 slot.
    cfn cenv ty base_e sa = (base_vv,s1) /\
    lower_value cfn cenv (expr_type idx_e) idx_e s1 = (key_op,s2) /\
    (if is_bytestring_type kt then compile_keccak256_key key_op F
     else comp_return key_op) s2 = (hashed_key,s3) /\
    compile_mapping_subscript (vv_operand base_vv) hashed_key s3 = (slot,sb) /\
    out = LocatedValue ret_ty
      (mk_ptr slot (case vv_location base_vv of SOME l => l | NONE => LocMemory))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_subscript _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  Cases_on `cfn cenv ty base_e sa` >> simp[] >>
  rename1 `cfn cenv ty base_e sa = (base_vv,s1)` >>
  Cases_on `lower_value cfn cenv (expr_type idx_e) idx_e s1` >> simp[] >>
  rename1 `lower_value cfn cenv (expr_type idx_e) idx_e s1 = (key_op,s2)` >>
  Cases_on `(if is_bytestring_type kt then compile_keccak256_key key_op F
             else comp_return key_op) s2` >> simp[] >>
  rename1 `(if is_bytestring_type kt then _ else _) s2 = (hashed_key,s3)` >>
  Cases_on `compile_mapping_subscript (vv_operand base_vv) hashed_key s3` >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_keccak256_key_bytes_run:
  !key sa out sb s p bytes.
  compile_keccak256_key key F sa = (out,sb) /\
  eval_operand key s = SOME p /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w (LENGTH bytes) /\
  LENGTH bytes < dimword (:256) /\
  mem_bytes_at (w2n (p + 32w)) (LENGTH bytes) s.vs_memory = bytes ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bytes)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[compile_keccak256_key_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ mid` >>
  `eval_operand key mid = SOME p` by
    (Cases_on `key` >>
     gvs[Abbr `mid`, eval_operand_def, lookup_var_update_var, not_fresh_at_def]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_read1_def, bind_outputs_def] >>
  `mload (w2n p) mid = n2w (LENGTH bytes)` by
    (simp[Abbr `mid`, mload_def, update_var_def] >>
     gvs[mload_def]) >>
  simp[] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       lookup_var_update_var, Abbr `mid`, GSYM mem_bytes_at_def] >>
  simp[run_inst_seq_def, lookup_var_update_var] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `not_fresh_at sa x` mp_tac >> simp[not_fresh_at_def] >>
  strip_tac >>
  first_assum (qspec_then `sa.cs_next_var` mp_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` mp_tac) >>
  first_x_assum (qspec_then `sa.cs_next_var + 2` mp_tac) >>
  simp[] >> rpt strip_tac >> simp[lookup_var_update_var] >> metis_tac[]
QED

Theorem compile_keccak256_key_bytes_code:
  !key sa out sb.
  compile_keccak256_key key F sa = (out,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_keccak256_key_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def, same_blocks_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem compile_keccak256_key_bytes_frame_frag:
  !key sa out sb s0 p bytes ctx func cenv cx es R.
  compile_keccak256_key key F sa = (out,sb) /\
  eval_operand key s0 = SOME p /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s0 = n2w (LENGTH bytes) /\
  LENGTH bytes < dimword (:256) /\
  mem_bytes_at (w2n (p + 32w)) (LENGTH bytes) s0.vs_memory = bytes /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. eval_operand out t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bytes)) /\
      stmt_state_rel ctx func cenv cx es t /\
      t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas /\
      contract_storage t = contract_storage s0 /\
      contract_transient t = contract_transient s0 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0)) R
Proof
  rpt strip_tac >> drule compile_keccak256_key_bytes_code >> strip_tac >>
  irule hash_run_frag >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all compile_keccak256_key_bytes_run >> strip_tac >>
  `t = s0 with vs_vars := t.vs_vars` by
    (qpat_x_assum `t with vs_vars := s0.vs_vars = s0`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     irule stmt_state_rel_fresh_vars >> simp[] >> qexists_tac `sa` >>
     gvs[lookup_var_def]) >>
  qexists_tac `t` >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
       contract_storage_def, contract_transient_def] >>
  qpat_assum `t = _` (fn th => pure_once_rewrite_tac[th]) >>
  simp[] >> gvs[lookup_var_def]
QED
