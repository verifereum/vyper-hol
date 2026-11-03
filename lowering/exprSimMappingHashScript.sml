(* Shared slot/key hashing boundary for mapping access. *)
Theory exprSimMappingHash
Ancestors
  exprSimHash vyperStorage valueEncodingProps valueEncodingProofs byte
  exprLoweringProps venomExecSemantics venomInst venomState emitHelperProps
  words finite_map builtinHashing valueEncoding exprLowering context
  emitHelper ASCIInumbers compileEnv list rich_list exprSimCalldataSlice

Theorem mapping_hash_staged_bytes:
  mem_bytes_at a 64
    (mstore (a + 32) key (mstore a slot s)).vs_memory =
  word_to_bytes_be slot ++ word_to_bytes_be key
Proof
  qspecl_then [`a`, `32`, `32`] (fn th => rewrite_tac[SIMP_RULE (srw_ss()) [] th])
    mem_bytes_at_split_padded >>
  simp[mstore_mem_bytes_at_disjoint, mem_bytes_at_mstore_same,
       word_to_bytes_be_def]
QED

Theorem mapping_hash_store_run:
  eval_operand ptr_op s = SOME (n2w a) /\
  eval_operand slot_op s = SOME slot /\
  eval_operand key_op s = SOME key /\
  a + 32 < dimword (:256) /\
  ptr_op <> Var kp /\ key_op <> Var kp ==>
  ?t. run_inst_seq
    [mk_inst i MSTORE [ptr_op; slot_op] [];
     mk_inst (i + 1) ADD [ptr_op; Lit 32w] [kp];
     mk_inst (i + 2) MSTORE [Var kp; key_op] [];
     mk_inst (i + 3) SHA3 [ptr_op; Lit 64w] [out]] s = OK t /\
    lookup_var out t = SOME (hashmap_slot slot key) /\
    t.vs_memory = (mstore (a + 32) key (mstore a slot s)).vs_memory /\
    (t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory |>) = s /\
    (!x. x <> kp /\ x <> out ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `a < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst i MSTORE [ptr_op; slot_op] []) s =
     OK (mstore a slot s)` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def] >>
  `eval_operand ptr_op (mstore a slot s) = SOME (n2w a) /\
   eval_operand key_op (mstore a slot s) = SOME key` by
    (gvs[mstore_def, eval_operand_def, lookup_var_def]) >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ staged` >>
  `step_inst_base (mk_inst (i + 1) ADD [ptr_op; Lit 32w] [kp]) staged =
   OK (update_var kp (n2w (a + 32)) staged)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, bind_outputs_def, word_add_n2w, Abbr `staged`,
         mstore_def, lookup_var_def] >>
  `eval_operand ptr_op (update_var kp (n2w (a + 32)) staged) = SOME (n2w a) /\
   eval_operand key_op (update_var kp (n2w (a + 32)) staged) = SOME key` by
    (Cases_on `ptr_op` >> Cases_on `key_op` >>
     gvs[eval_operand_def, lookup_var_update_var, Abbr `staged`,
         mstore_def, lookup_var_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_write2_def, eval_operand_def, lookup_var_update_var] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ hashed` >>
  `eval_operand ptr_op hashed = SOME (n2w a)` by
    gvs[Abbr `hashed`, mstore_def, eval_operand_def, lookup_var_def] >>
  `hashed.vs_memory = (mstore (a + 32) key (mstore a slot s)).vs_memory` by
    simp_tac (srw_ss()) [Abbr `hashed`, Abbr `staged`, mstore_def, update_var_def, LET_THM] >>
  `mem_bytes_at a 64 hashed.vs_memory =
   word_to_bytes_be slot ++ word_to_bytes_be key` by
    (pure_asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [Abbr `staged`, mapping_hash_staged_bytes]) >>
  simp[run_inst_seq_def, step_inst_base_def, eval_operand_def,
       GSYM mem_bytes_at_def, hashmap_slot_def, word_of_bytes_be_def] >>
  `64 MOD dimword (:256) = 64` by simp[dimword_def] >>
  `mem_bytes_at a 64 (mstore (a + 32) key staged).vs_memory =
   word_to_bytes_be slot ++ word_to_bytes_be key` by
    simp_tac (srw_ss()) [Abbr `staged`, mapping_hash_staged_bytes] >>
  simp[lookup_var_update_var] >>
  simp_tac (srw_ss()) [Abbr `hashed`, Abbr `staged`, update_var_def,
    mstore_def, LET_THM, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem compile_mapping_subscript_decompose:
  compile_mapping_subscript slot_op key_op sa = (op,sb) ==>
  ?buf sm.
    compile_alloc_buffer 64 sa = (buf,sm) /\
    sm.cs_next_var = sa.cs_next_var + 1 /\
    sm.cs_next_id = sa.cs_next_id + 1 /\
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id MSTORE [buf.buf_operand; slot_op] [];
       mk_inst (sm.cs_next_id + 1) ADD [buf.buf_operand; Lit 32w]
         [STRING #"%" (toString sm.cs_next_var)];
       mk_inst (sm.cs_next_id + 2) MSTORE
         [Var (STRING #"%" (toString sm.cs_next_var)); key_op] [];
       mk_inst (sm.cs_next_id + 3) SHA3 [buf.buf_operand; Lit 64w]
         [STRING #"%" (toString (sm.cs_next_var + 1))]] /\
    op = Var (STRING #"%" (toString (sm.cs_next_var + 1))) /\
    sb.cs_next_var = sm.cs_next_var + 2 /\
    sb.cs_next_id = sm.cs_next_id + 4
Proof
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       GSYM APPEND_ASSOC, DROP_APPEND2]
QED

Theorem mapping_hash_stores_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (a,64) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint a 64 b len) ==>
  stmt_state_rel ctx func cenv cx es (mstore (a + 32) key (mstore a slot s))
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore a slot s)` by
    (irule exprSimLiteralBufferTheory.literal_mstore_state_rel >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`, `inst`, `64`] >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def]) >>
  irule exprSimLiteralBufferTheory.literal_mstore_state_rel >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`a`, `inst`, `64`] >> simp[mstore_def] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s name lb lsz` by
    gvs[local_region_def, mstore_def, lookup_var_def] >>
  first_x_assum drule >> simp[regions_disjoint_def]
QED

Theorem compile_mapping_subscript_run:
  compile_mapping_subscript slot_op key_op sa = (op,sb) /\
  (!x. slot_op = Var x ==> not_fresh_at sa x) /\
  (!x. key_op = Var x ==> not_fresh_at sa x) /\
  eval_operand slot_op s = SOME slot /\ eval_operand key_op s = SOME key /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t (addr:bytes32).
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (hashmap_slot slot key) /\
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_memory =
      (mstore (w2n addr + 32) key (mstore (w2n addr) slot s)).vs_memory /\
    w2n addr + 64 < dimword (:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addr,64) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >> drule compile_mapping_subscript_decompose >> strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all exprSimLiteralBufferTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK allocated` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand slot_op allocated = SOME slot /\
   eval_operand key_op allocated = SOME key` by
    (Cases_on `slot_op` >> Cases_on `key_op` >> gvs[eval_operand_def] >>
     metis_tac[]) >>
  `buf.buf_operand <> Var (STRING #"%" (toString sm.cs_next_var)) /\
   key_op <> Var (STRING #"%" (toString sm.cs_next_var))` by
    (gvs[toString_inj] >> strip_tac >>
     qpat_x_assum `!x. key_op = Var x ==> _` drule >> simp[not_fresh_at_def] >>
     disch_then (qspec_then `sa.cs_next_var + 1` mp_tac) >> simp[]) >>
  `eval_operand buf.buf_operand allocated = SOME (n2w (w2n w))` by simp[] >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  qpat_assum `eval_operand slot_op allocated = SOME slot`
    (mp_then (Pos (el 2)) mp_tac mapping_hash_store_run) >>
  disch_then (fn th => qpat_assum `eval_operand key_op allocated = SOME key`
    (mp_then (Pos (el 2)) mp_tac th)) >>
  disch_then drule_all >>
  disch_then (qspecl_then
    [`STRING #"%" (toString (sm.cs_next_var + 1))`, `sm.cs_next_id`] mp_tac) >>
  strip_tac >> suspend "compose"
QED

Resume compile_mapping_subscript_run[compose]:
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x allocated` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `not_fresh_at sa x` mp_tac >>
     rewrite_tac[not_fresh_at_def] >> strip_tac >>
     gvs[] >> conj_tac >> first_x_assum irule >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (qspecl_then [`sa`, `sm`, `sb`] mp_tac (cj 1 run_inst_seq_chain) >>
     disch_then drule_all >> disch_then SUBST1_TAC >>
     gvs[]) >>
  `t.vs_allocas = allocated.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qmatch_asmsub_abbrev_tac `t.vs_memory = staged.vs_memory` >>
     `stmt_state_rel ctx func cenv cx es staged` by
       (simp_tac (srw_ss()) [Abbr `staged`] >>
        irule mapping_hash_stores_state_rel >>
        conj_tac >- (first_assum ACCEPT_TAC) >>
        conj_tac >- (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
          [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
        (first_assum ACCEPT_TAC)) >>
     `t = allocated with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>` by
       (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
         (mp_tac o Q.AP_TERM `\z. z with <|vs_vars := t.vs_vars;
           vs_memory := t.vs_memory|>`) >> simp_tac (srw_ss()) []) >>
     `staged = allocated with vs_memory := staged.vs_memory` by
       (simp_tac (srw_ss()) [Abbr `staged`, mstore_def, LET_THM]) >>
     `staged.vs_vars = allocated.vs_vars` by
       (qpat_assum `staged = _` (mp_tac o Q.AP_TERM `\z. z.vs_vars`) >>
        simp_tac (srw_ss()) []) >>
     `t with vs_vars := staged.vs_vars = staged` by
       (qpat_assum `t = allocated with <|vs_vars := _; vs_memory := _|>` SUBST1_TAC >>
        simp_tac (srw_ss()) [] >>
        qpat_assum `t.vs_memory = staged.vs_memory` (fn th => rewrite_tac[th]) >>
        qpat_assum `staged.vs_vars = allocated.vs_vars` (fn th => rewrite_tac[th]) >>
        qpat_assum `staged = allocated with vs_memory := _`
          (fn th => once_rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
     irule hash_readonly_state_rel >> qexistsl_tac [`staged`, `sa`] >>
     conj_tac >- (rpt strip_tac >>
       `lookup_var x staged = lookup_var x allocated` by
         (qpat_assum `staged.vs_vars = allocated.vs_vars`
            (fn th => simp_tac (srw_ss()) [lookup_var_def, th])) >>
       qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >>
       qpat_assum `lookup_var x staged = _` (fn th => rewrite_tac[th])) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `t.vs_memory = (mstore (w2n w + 32) key (mstore (w2n w) slot s)).vs_memory` by
    (qpat_x_assum `t.vs_memory = _` mp_tac >>
     qpat_x_assum `allocated.vs_memory = s.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `!off value. (mstore off value allocated).vs_memory =
        (mstore off value s).vs_memory` by
       (rpt gen_tac >> drule mstore_equal_memory >> simp[]) >>
     qpat_x_assum `allocated.vs_memory = _` kall_tac >>
     `(mstore (w2n w) slot allocated).vs_memory =
      (mstore (w2n w) slot s).vs_memory` by simp[] >>
     qpat_x_assum `!off value. _` kall_tac >>
     drule mstore_equal_memory >> simp[]) >>
  `!b len. regions_disjoint (w2n w) 64 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> qpat_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     `mem_bytes_at b len
        (mstore (w2n w + 32) key (mstore (w2n w) slot s)).vs_memory =
      mem_bytes_at b len (mstore (w2n w) slot s).vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`w2n w`, `64`] >> simp[]) >>
     asm_rewrite_tac[] >> irule mstore_region_frame >>
     qexistsl_tac [`w2n w`, `64`] >> simp[]) >>
  `!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl_tac [`sa`, `es.scopes`, `allocated`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp_tac (srw_ss()) [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `allocated.vs_memory = s.vs_memory` (fn th => rewrite_tac[th])) >>
     rpt strip_tac >>
     `regions_disjoint (w2n w) 64 b sz` by
       (qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` drule >> simp[]) >>
     `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
       (qpat_x_assum `!b len. regions_disjoint _ _ _ _ ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `mem_bytes_at b sz t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `allocated.vs_memory = s.vs_memory` (fn th => rewrite_tac[th])) >>
  qexistsl_tac [`t`, `w`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `op = _` (fn th => rewrite_tac[th]) >>
    simp_tac (srw_ss()) [eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x allocated = _` drule >>
    simp_tac (srw_ss()) [] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED


Finalise compile_mapping_subscript_run
