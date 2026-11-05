(* Memory checking for the common SHA256 precompile continuation. *)
Theory bodyMemBiSha256Suffix
Ancestors
  bodyMemBiSha256Bounds emitHelper fragExecMem instMemFrontier memSafeRun
  exprLoweringProps compileEnv emitHelperProps venomExecSemantics venomInst venomState venomMemProps
  venomMemDefs venomInstProps venomInstProofs words list bufferAllocationExecution

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
  fs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, run_inst_seq_mem_ok_last,
       mk_inst_def, below_frontier_no_ranges] >>
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

