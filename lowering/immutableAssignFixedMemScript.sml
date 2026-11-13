(* Equal-layout immutable assignment uses the fixed word-copy endpoint. *)
Theory immutableAssignFixedMem
Ancestors
  immutableFixedCopyTransportMem immutableConstructorRelation immutableDeployAssignBytes
  exprLoweringProps stmtLowering context compileEnv loweringSlice valueEncodingProps venomState loweringStateRelDefs

Theorem immutable_assign_fixed_mem_endpoint:
  compile_assign_value ce dst LocCode src F sl dty dty di
    (type_memory_bytes ce dty) sm = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  ce.ce_imm_alloca = SOME region /\ fn_has_code sm sb func /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME (n2w off) /\
  eval_operand src s = SOME (n2w a) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  immutable_value_admissible dtv v /\ val_in_memory dtv v a s.vs_memory /\
  0 < type_memory_size dtv /\ type_memory_size dtv MOD 32 = 0 /\
  a + type_memory_size dtv <= s.vs_alloca_next /\
  off + type_memory_size dtv <= s.vs_alloca_next /\
  a + type_memory_size dtv < dimword (:256) /\
  off + type_memory_size dtv < dimword (:256) /\
  regions_disjoint off (type_memory_size dtv) a (type_memory_size dtv) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    val_in_memory dtv v off t.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) t.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?n. type_memory_size dtv = 32 * n /\ 0 < n` by
    (qexists_tac `type_memory_size dtv DIV 32` >>
     mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
     simp[] >> disch_then (qspec_then `type_memory_size dtv` mp_tac) >>
     simp[] >> decide_tac) >>
  `compile_imm_store_words (SOME region) src dst n 0 sm = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     Cases_on `n = 1` >-
       (gvs[] >> CONV_TAC (DEPTH_CONV numLib.num_CONV) >>
        simp[compile_imm_store_words_def, compile_lit_byte_offset_def,
             comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
     `~(32*n <= 32) /\ (32*n+31) DIV 32 = n` by simp[] >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `!x. region = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `a + 0 + 32*n <= s.vs_alloca_next /\
   off + 0 + 32*n <= s.vs_alloca_next /\
   a + 0 + 32*n < dimword (:256) /\
   off + 0 + 32*n < dimword (:256) /\
   (off+0+32*n <= a+0 \/ a+0+32*n <= off+0)` by
    gvs[regions_disjoint_def] >>
  drule immutable_fixed_copy_operand_mem_endpoint >>
  disch_then (qspecl_then [`s`, `func`, `ctx`, `off`, `a`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_wf dtv v` by metis_tac[immutable_admissible_val_wf] >>
  `val_in_memory dtv v off (mcopy off a (32*n) s).vs_memory` by
    (irule mcopy_establishes_val_in_memory >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[] >>
  `immutable_value_bytes_rel dtv v
    (mem_bytes_at a (32*n) s.vs_memory)` by
    metis_tac[immutable_memory_bytes] >>
  fs[lookup_var_def, same_blocks_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  metis_tac[]
QED
