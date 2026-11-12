(* The post-INVOKE store suffix preserves an already owned return buffer.
   This does not assert allocation ownership for the INVOKE prefix. *)
Theory tupleAssignImmutableDeployIntStackOwned
Ancestors
  intCallResult entrySinkExtraction placeMemoryPrimitiveForward
  exprSimCopy abiDecodeStaticProps emitHelperProps exprLowering emitHelper
  context list rich_list compileEnv fragExec venomState exprLoweringProps
  stmtReasonMemory

Theorem stack_store_no_gas[local]:
  !ops buf off sa sb.
    store_multi_results buf ops off sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct
  >- simp[store_multi_results_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (u,post)` >> Cases_on `u` >>
  first_x_assum drule >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `post.cs_current_insts = sa.cs_current_insts ++
    (emitted_insts sa mid ++ emitted_insts mid post)` by simp[APPEND_ASSOC] >>
  `emitted_insts sa post = emitted_insts sa mid ++ emitted_insts mid post` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> metis_tac[]) >>
  simp[EVERY_APPEND, venomInstTheory.mk_inst_def]
QED

Theorem tuple_immutable_stack_return_owned_path:
  store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
  local_ptrs_reserved cenv sa /\
  (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
  (!x. MEM (Var x) results ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) v /\
  EVERY (\etv. ?t'. is_word_type t' /\
    evaluate_type (get_tenv cx) t' = SOME etv) tvs /\
  intret_vals_match (TupleTV tvs) v ws /\ ws <> [] /\
  stmt_state_rel ctx func cenv cx es s0 /\
  eval_operand rbuf.buf_operand s0 = SOME w /\
  MAP (\op. eval_operand op s0) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
     w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint (w2n w) (32 * LENGTH results) off (type_memory_size itv)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  FLOOKUP s0.vs_allocas aid = SOME (w2n w,sz) /\ aid < sa.cs_next_id /\
  type_memory_bytes cenv (TupleT stys) <= sz /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
     w2n w + sz <= lb \/ lb + lsz <= w2n w) ==>
  ?t. stmt_state_rel ctx func cenv cx es t /\
    vv_holds cenv cx (TupleT stys) (Value v)
      (LocatedValue (TupleT stys) (base_ptr rbuf)) es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    t.vs_allocas = s0.vs_allocas /\
    (!a len. a + len <= w2n w \/ w2n w + 32 * LENGTH results <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s0.vs_memory) /\
    eval_operand rbuf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\ aid < sb.cs_next_id /\
    type_memory_bytes cenv (TupleT stys) <= sz /\
    (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
       w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_path F ctx func s0 0 (OK t)
Proof
  strip_tac >>
  drule store_multi_results_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`,
    `TupleT stys`, `TupleTV tvs`, `v`] mp_tac) >>
  disch_then (qspecl_then [`s0`, `w`, `ws`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[arithmeticTheory.ADD_COMM])) >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  `dec_straight sa sb` by
    fs[dec_straight_def, same_blocks_def, inst_extends_def] >>
  drule_at (Pos (el 2)) frag_exec_straight_run >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s0 = OK u` >>
  `gas_marked_path F ctx func s0 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >>
     simp[] >> qexistsl [`emitted_insts sa sb`, `sa`] >>
     simp[] >> metis_tac[stack_store_no_gas, same_blocks_def]) >>
  `u.vs_labels = s0.vs_labels` by metis_tac[run_inst_seq_data_section] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0` by
    fs[lookup_var_def] >>
  `eval_operand rbuf.buf_operand u = SOME w` by
    (Cases_on `rbuf.buf_operand` >> gvs[eval_operand_def]) >>
  `!n lb lsz. local_region cenv es.scopes
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) n lb lsz ==>
      w2n w + sz <= lb \/ lb + lsz <= w2n w` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s0 n lb lsz` by
       (mp_tac (Q.SPECL [`cenv`, `sa`, `s0`,
          `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
          copy_buffer_local_region_frame) >>
        disch_then (qspecl_then [`es.scopes`, `n`, `lb`, `lsz`] mp_tac) >>
        fs[lookup_var_def] >>
        qpat_x_assum `local_region _ _ _ n lb lsz` mp_tac >> simp[]) >>
     metis_tac[]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[same_blocks_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!n lb lsz. local_region _ _ (u with vs_inst_idx := _) n lb lsz ==> _`
    mp_tac >> simp[]
QED
