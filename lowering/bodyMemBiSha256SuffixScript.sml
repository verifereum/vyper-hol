(* Memory checking for the common SHA256 precompile continuation. *)
Theory bodyMemBiSha256Suffix
Ancestors
  bodyMemBiSha256Bounds emitHelper fragExecMem instMemFrontier memSafeRun
  exprLoweringProps compileEnv loweringStateRelDefs emitHelperProps venomExecSemantics venomInst venomState venomMemProps
  venomMemDefs venomInstProps venomInstProofs words list bufferAllocationExecution exprSimHash

Theorem sha256_call_preserves_operand:
  step_inst_base (mk_inst i STATICCALL ops [sv]) s = OK t /\
  (!x. ret_op = Var x ==> x <> sv) ==>
  eval_operand ret_op t = eval_operand ret_op s
Proof
  strip_tac >> Cases_on `ret_op` >> simp[eval_operand_def] >>
  `step_inst 0 ARB (mk_inst i STATICCALL ops [sv]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `t.vs_labels = s.vs_labels` by
    (drule step_preserves_labels >> simp[mk_inst_def, is_terminator_def]) >>
  drule step_preserves_non_output_vars >>
  simp[mk_inst_def, is_terminator_def] >> metis_tac[]
QED

Theorem sha256_assert_load_mem_ok:
  eval_operand ret_op s = SOME r /\ w2n r + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst ia ASSERT [cond] []; mk_inst il MLOAD [ret_op] [out]] s
Proof
  strip_tac >>
  `inst_mem_below_frontier (mk_inst ia ASSERT [cond] []) s` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `inst_dload_in_section (mk_inst ia ASSERT [cond] []) s` by simp[mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_def] >>
  Cases_on `step_inst_base (mk_inst ia ASSERT [cond] []) s` >> simp[] >>
  rename1 `_ = OK t` >>
  `step_inst 0 ARB (mk_inst ia ASSERT [cond] []) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `t = s` by (drule step_assert_identity >> simp[mk_inst_def]) >>
  gvs[run_inst_seq_mem_ok_last, below_frontier_MLOAD, mk_inst_def]
QED

Theorem sha256_tail_mem_ok:
  eval_operand ptr_op s = SOME p /\
  eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gv) /\
  (!x. ret_op = Var x ==> x <> sv) /\
  (w2n n = 0 \/ w2n p + w2n n <= s.vs_alloca_next) /\
  w2n r + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst i0 GAS [] [gv];
     mk_inst i1 STATICCALL [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv];
     mk_inst i2 ASSERT [Var sv] [];
     mk_inst i3 MLOAD [ret_op] [out]] s
Proof
  strip_tac >>
  `inst_mem_below_frontier (mk_inst i0 GAS [] [gv]) s` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `inst_dload_in_section (mk_inst i0 GAS [] [gv]) s` by simp[mk_inst_def] >>
  `step_inst_base (mk_inst i0 GAS [] [gv]) s =
     OK (update_var gv (HD (s.vs_gas_readings ++ [0w]))
       (s with vs_gas_readings := DROP 1 s.vs_gas_readings))` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_gas_def] >>
     Cases_on `s.vs_gas_readings` >> simp[update_var_def, venom_state_component_equality]) >>
  simp[Once run_inst_seq_mem_ok_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ sg` >>
  `eval_operand ptr_op sg = SOME p /\
   eval_operand len_op sg = SOME n /\
   eval_operand ret_op sg = SOME r /\
   sg.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `ptr_op` >> Cases_on `len_op` >> Cases_on `ret_op` >>
     gvs[Abbr `sg`, eval_operand_def, lookup_var_update_var, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `inst_mem_below_frontier
     (mk_inst i1 STATICCALL [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv]) sg` by
    (fs[below_frontier_STATICCALL, eval_operand_def, dimword_def]) >>
  `inst_dload_in_section
     (mk_inst i1 STATICCALL [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv]) sg` by
    simp[mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_def] >>
  Cases_on `step_inst_base
    (mk_inst i1 STATICCALL [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv]) sg` >>
  simp[] >> rename1 `_ = OK sc` >>
  `eval_operand ret_op sc = SOME r` by
    metis_tac[sha256_call_preserves_operand] >>
  `sc.vs_alloca_next = sg.vs_alloca_next` by
    (irule venomMemPropsTheory.step_inst_base_preserves_alloca_next >>
     qexists_tac `mk_inst i1 STATICCALL
       [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv]` >>
     simp[mk_inst_def]) >>
  irule sha256_assert_load_mem_ok >> simp[] >> metis_tac[]
QED

Theorem emit_sha256_tail_mem_ok:
  emit_op GAS [] sa = (gas_op, sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] sg =
    (success_op, sc) /\
  emit_void ASSERT [success_op] sc = ((), sh) /\
  emit_op MLOAD [ret_op] sh = (op, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> not_fresh_at sa x) /\
  (w2n n = 0 \/ w2n p + w2n n <= s.vs_alloca_next) /\
  w2n r + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  irule sha256_tail_mem_ok >>
  simp[] >> fs[not_fresh_at_def] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem sha256_alloc32_mem:
  compile_alloc_buffer 32 ca = (buf,cb) /\ alloca_next_valid s /\
  (!base cap. FLOOKUP s.vs_allocas ca.cs_next_id = SOME (base,cap) ==> cap = 32) ==>
  ?t r. run_inst_seq (emitted_insts ca cb) s = OK t /\
    run_inst_seq_mem_ok (emitted_insts ca cb) s /\
    eval_operand buf.buf_operand t = SOME r /\
    w2n r + 32 <= t.vs_alloca_next /\ alloca_next_valid t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    (!a. (!x. a = Var x ==> not_fresh_at ca x) ==>
      eval_operand a t = eval_operand a s) /\
    (!aid. aid <> ca.cs_next_id ==> FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at cb x)
Proof
  strip_tac >> drule compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  qexists_tac `update_var out (n2w (buffer_allocation_base s ca.cs_next_id))
    (buffer_allocation_fields s ca.cs_next_id 32)` >>
  qexists_tac `n2w (buffer_allocation_base s ca.cs_next_id)` >>
  `emitted_insts ca cb =
    [mk_inst ca.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString ca.cs_next_var)]] /\
   out = STRING #"%" (toString ca.cs_next_var) /\
   cb.cs_next_var = ca.cs_next_var + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `w2n (32w:bytes32) = 32` by simp_tac (srw_ss()) [wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  (* Only substitution with the assumptions is needed here; fs[] over this
     context took 3.5 s. *)
  full_simp_tac bool_ss [] >>
  qabbrev_tac `nm = STRING #"%" (toString ca.cs_next_var)` >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, run_inst_seq_mem_ok_last,
       mk_inst_def, below_frontier_no_ranges] >>
  simp[Abbr`nm`] >>
  `w2n (n2w (buffer_allocation_base s ca.cs_next_id):bytes32) <=
    buffer_allocation_base s ca.cs_next_id` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  Cases_on `FLOOKUP s.vs_allocas ca.cs_next_id`
  >- (gvs[buffer_allocation_base_def, buffer_allocation_fields_def,
          alloca_next_valid_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
      conj_tac
      >- (rpt strip_tac >> Cases_on `ca.cs_next_id = aid` >> gvs[] >>
          first_x_assum drule >> decide_tac) >>
      rpt strip_tac >> Cases_on `a` >>
      gvs[eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >> metis_tac[]) >>
  rename1 `_ = SOME allocation` >> PairCases_on `allocation` >>
  `allocation1 = 32` by metis_tac[] >>
  qpat_x_assum `!base cap. _` kall_tac >>
  gvs[buffer_allocation_base_def, buffer_allocation_fields_def,
      alloca_next_valid_def, not_fresh_at_def] >>
  conj_tac
  >- (first_x_assum drule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> Cases_on `a` >>
  gvs[eval_operand_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >> metis_tac[]
QED


Theorem sha256_alloc32_compile:
  compile_alloc_buffer 32 ca = (buf,cb) ==>
  cb.cs_next_id = ca.cs_next_id + 1 /\
  cb.cs_next_var = ca.cs_next_var + 1 /\
  cb.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cb
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem sha256_mstore_mem:
  !ptr_op value ca cb s p v.
  emit_void MSTORE [ptr_op;value] ca = ((),cb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand value s = SOME v /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq (emitted_insts ca cb) s = OK (mstore (w2n p) v s) /\
  run_inst_seq_mem_ok (emitted_insts ca cb) s /\
  (mstore (w2n p) v s).vs_allocas = s.vs_allocas /\
  (mstore (w2n p) v s).vs_alloca_next = s.vs_alloca_next /\
  (!a. eval_operand a (mstore (w2n p) v s) = eval_operand a s) /\
  (alloca_next_valid (mstore (w2n p) v s) <=> alloca_next_valid s)
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst ca.cs_next_id MSTORE [ptr_op;value] []) s =
    OK (mstore (w2n p) v s)` by (irule step_MSTORE >> simp[]) >>
  simp[run_inst_seq_def, run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       mstore_def, alloca_next_valid_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem compile_sha256_bytesm_mem_ok:
  compile_sha256_bytesm val_op m sa = (op,sb) /\
  eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  alloca_next_valid s /\ m <= 32 /\
  (!aid base cap. (aid = sa.cs_next_id \/ aid = sa.cs_next_id + 2) /\
    FLOOKUP s.vs_allocas aid = SOME (base,cap) ==> cap = 32) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[builtinHashingTheory.compile_sha256_bytesm_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer 32 sa = (ib,c1)` >>
  rename1 `emit_void MSTORE _ c1 = (u,c2)` >> Cases_on `u` >>
  rename1 `compile_alloc_buffer 32 c2 = (ob,c3)` >>
  rename1 `emit_void ASSERT _ _ = (u,c6)` >> Cases_on `u` >>
  `!base cap. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (base,cap) ==> cap = 32` by metis_tac[] >>
  drule_all sha256_alloc32_mem >> strip_tac >>
  qpat_x_assum `!base cap. _` kall_tac >>
  qpat_x_assum `!aid base cap. _` (mk_asm "sizes") >>
  qpat_assum `compile_alloc_buffer 32 sa = _`
    (mp_then Any strip_assume_tac sha256_alloc32_compile) >>
  `eval_operand val_op t = SOME v` by metis_tac[] >>
  drule_all sha256_mstore_mem >> strip_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  `!base cap. FLOOKUP (mstore (w2n r) v t).vs_allocas c2.cs_next_id = SOME (base,cap) ==> cap = 32` by
    (simp[] >> rpt strip_tac >>
     `c2.cs_next_id <> sa.cs_next_id` by decide_tac >>
     asm "sizes" (qspec_then `sa.cs_next_id + 2` mp_tac) >> metis_tac[]) >>
  qpat_assum `compile_alloc_buffer 32 c2 = _`
    (mp_then Any mp_tac sha256_alloc32_mem) >>
  disch_then (qspec_then `mstore (w2n r) v t` mp_tac) >>
  impl_tac >- (conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `!base cap. _` kall_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) _ = OK t3` >>
  `!x. ib.buf_operand = Var x ==> not_fresh_at c2 x` by fs[not_fresh_at_def] >>
  `eval_operand ib.buf_operand t3 = SOME r` by metis_tac[] >>
  qpat_assum `compile_alloc_buffer 32 c2 = _`
    (mp_then Any strip_assume_tac sha256_alloc32_compile) >>
  `!x. ib.buf_operand = Var x ==> not_fresh_at c3 x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `run_inst_seq_mem_ok (emitted_insts c3 sb) t3` by
    (irule emit_sha256_tail_mem_ok >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op STATICCALL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GAS _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void ASSERT _ _ = _`)) >>
     simp[eval_operand_def] >> conj_tac >- metis_tac[] >>
     `m MOD dimword (:256) <= m` by simp[arithmeticTheory.MOD_LESS_EQ] >>
     fs[] >> decide_tac) >>
  `sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb` by
    (qpat_x_assum `emit_op GAS [] c3 = _` mp_tac >>
     qpat_x_assum `emit_op STATICCALL _ _ = _` mp_tac >>
     qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
      (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `c3.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `c2.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `c1.cs_current_insts = _` SUBST1_TAC >>
     rpt (pop_assum kall_tac) >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND] >>
     `!a b:num. a - (a + b) = 0` by decide_tac >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `t1` >> strip_tac >>
  `t1 = t` by
    (qpat_x_assum `run_inst_seq _ s = OK t1` mp_tac >>
     qpat_assum `run_inst_seq _ s = OK t` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `t2` >> strip_tac >>
  `t2 = mstore (w2n r) v t` by
    (qpat_x_assum `run_inst_seq _ t = OK t2` mp_tac >>
     qpat_assum `run_inst_seq _ t = OK (mstore _ _ _)`
       (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `t2 = _` SUBST_ALL_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `t4` >> strip_tac >>
  `t4 = t3` by
    (qpat_x_assum `run_inst_seq (emitted_insts c2 c3) _ = OK t4` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts c2 c3) _ = OK t3`
       (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `t4 = t3` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED

Theorem sha256_data_prefix_mem_ok:
  emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op,sm) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  b < dimword (:256) /\ b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_def,
       below_frontier_MLOAD, w2n_n2w] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges] >>
  simp[mk_inst_def] >> CASE_TAC >> simp[]
QED

(* Execution of the read prefix reuses the task-permitted overlay fact
   exprSimHash.hash_data_prefix_run; this dependency carries its oracle tag. *)
Theorem compile_sha256_bytes_mem_ok:
  compile_sha256_bytes ptr_op sa = (op,sb) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  mem_word_at b s.vs_memory = n2w len /\
  b < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (len = 0 \/ w2n (n2w (b + 32):bytes32) + len <= s.vs_alloca_next) /\
  alloca_next_valid s /\
  (!base cap. FLOOKUP s.vs_allocas (sa.cs_next_id + 2) = SOME (base,cap) ==> cap = 32) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[builtinHashingTheory.compile_sha256_bytes_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `emit_op MLOAD [ptr_op] sa = (len_op,sl)` >>
  rename1 `emit_op ADD [ptr_op; Lit 32w] sl = (data_op,sm)` >>
  rename1 `compile_alloc_buffer 32 sm = (buf,sn)` >>
  rename1 `emit_void ASSERT _ _ = (u,sh)` >> Cases_on `u` >>
  qpat_x_assum `!base cap. _` (mk_asm "size") >>
  drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK prefix` >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule sha256_data_prefix_mem_ok >> metis_tac[]) >>
  `prefix.vs_allocas = s.vs_allocas /\
   prefix.vs_alloca_next = s.vs_alloca_next /\
   prefix.vs_memory = s.vs_memory` by
    (qpat_x_assum `(prefix with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `alloca_next_valid prefix` by (fs[alloca_next_valid_def] >> metis_tac[]) >>
  `!base cap. FLOOKUP prefix.vs_allocas sm.cs_next_id = SOME (base,cap) ==> cap = 32` by
    (asm "size" assume_tac >> metis_tac[]) >>
  qpat_assum `compile_alloc_buffer 32 sm = _`
    (mp_then Any mp_tac sha256_alloc32_mem) >>
  disch_then (qspec_then `prefix` mp_tac) >>
  impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `!base cap. _` kall_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) prefix = OK allocated` >>
  qpat_assum `compile_alloc_buffer 32 sm = _`
    (mp_then Any strip_assume_tac sha256_alloc32_compile) >>
  `eval_operand len_op allocated = SOME (n2w len) /\
   eval_operand data_op allocated = SOME (n2w (b + 32))` by metis_tac[] >>
  `!x. data_op = Var x \/ len_op = Var x ==> not_fresh_at sn x` by
    (qpat_assum `!x. len_op = Var x \/ data_op = Var x ==> _` mp_tac >>
     qpat_assum `sn.cs_next_var = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `run_inst_seq_mem_ok (emitted_insts sn sb) allocated` by
    (irule emit_sha256_tail_mem_ok >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op STATICCALL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GAS _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void ASSERT _ _ = _`)) >>
     simp[] >> conj_tac >- metis_tac[] >>
     `w2n (n2w len:bytes32) <= len` by simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
     Cases_on `len = 0` >- simp[] >> fs[] >> decide_tac) >>
  `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (qpat_x_assum `emit_op GAS [] sn = _` mp_tac >>
     qpat_x_assum `emit_op STATICCALL _ _ = _` mp_tac >>
     qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ sh = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++
      (emitted_insts sm sn ++ emitted_insts sn sb)` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `sn.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `sm.cs_current_insts = _` SUBST1_TAC >>
     rpt (pop_assum kall_tac) >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND] >>
     `!a b:num. a - (a + b) = 0` by decide_tac >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `t1` >> strip_tac >>
  `t1 = prefix` by
    (qpat_x_assum `run_inst_seq _ s = OK t1` mp_tac >>
     qpat_assum `run_inst_seq _ s = OK prefix` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `t1 = prefix` SUBST_ALL_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `t2` >> strip_tac >>
  `t2 = allocated` by
    (qpat_x_assum `run_inst_seq _ prefix = OK t2` mp_tac >>
     qpat_assum `run_inst_seq _ prefix = OK allocated` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `t2 = allocated` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED
