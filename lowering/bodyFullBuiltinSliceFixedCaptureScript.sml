(* A fixed-byte Slice captures its word in a fresh 32-byte allocation. *)
Theory bodyFullBuiltinSliceFixedCapture
Ancestors
  bodyFullAllocaFresh bodyFullBuiltinBytestringCopy wordLoadStorePtr
  fragGasOriginPtr fragExec loweringHalt emitHelperProps exprLoweringProps valueEncodingProps
  ptrDiscipline bodyPtrDefs allocaHistory freshWrites
  venomExecSemantics venomState venomInst compileEnv loweringStateRelDefs
  emitHelper context words list finite_map

Theorem slice_fixed_capture_full_run:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;src] sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  eval_operand src s = SOME w /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root p u t G' tn'.
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,G',tn')) /\
    t = mstore (w2n p) w u with vs_inst_idx := LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var root t = SOME p /\ ptr_covers G' tn' root t 32 /\
    mem_word_at (w2n p) t.vs_memory = w /\
    mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn'.t_mem) /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,32) /\
    w2n p+32 < dimword (:256) /\ w2n p+32 <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    u with <|vs_vars := s.vs_vars;vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next;vs_inst_idx := s.vs_inst_idx|> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func cenv cx es u) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n p) 32 b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n p) 32 b len) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!j. j < s.vs_alloca_next /\ j IN tn'.t_mem ==> j IN tn.t_mem)
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,fresh_id_def,emit_def] >> strip_tac >>
     gvs[cs_extends_def,rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  mp_tac (Q.INST [`n` |-> `32`,`sb` |-> `sm`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> alpha] alloc_buffer_origin_ptr_path)) >>
  (impl_tac >- simp[dimword_def]) >>
  disch_then (qx_choose_then `root` (qx_choose_then `p`
    (qx_choose_then `u` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))) >>
  `u.vs_labels = s.vs_labels /\ ~u.vs_halted` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME w /\ op_taint tn1 src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def,op_taint_def] >>
     metis_tac[]) >>
  qpat_assum `buf.buf_operand = Var root` SUBST_ALL_TAC >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [Var root;src] []` >>
  qabbrev_tac `t = mstore (w2n p) w u with vs_inst_idx := SUC u.vs_inst_idx` >>
  qabbrev_tac `tn2 = step_taint i u (mstore (w2n p) w u) tn1` >>
  `step_prov PG G1 i (mstore (w2n p) w u) = G1 /\
   tn2.t_var = tn1.t_var /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    simp[Abbr `i`,Abbr `tn2`,ifexp_materialize_mstore_ghost] >>
  `tn2.t_mem = tn1.t_mem DIFF {j | w2n p <= j /\ j < w2n p+32}` by
    (mp_tac (Q.INST [`addr` |-> `Var root`,`value` |-> `src`,
       `s` |-> `u`,`a` |-> `p`,`tn` |-> `tn1`,
       `id` |-> `sm.cs_next_id`] ifexp_materialize_mstore_taint) >>
     simp[eval_operand_def,Abbr `i`,Abbr `tn2`]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G1,tn1) []
      (OK t,G1,tn2)` by
    (mp_tac (Q.INST [`sa` |-> `sm`,`s` |-> `u`,`G` |-> `G1`,
       `tn` |-> `tn1`,`b` |-> `p`,`cnt` |-> `src`,`n` |-> `w`]
       bytestring_length_store_origin_edge) >>
     (impl_tac >- simp[]) >> simp[Abbr `i`,Abbr `tn2`,Abbr `t`]) >>
  `~t.vs_halted` by simp[Abbr `t`,mstore_def,write_memory_with_expansion_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,G1,tn2)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) []
        (OK t,G1,tn2)` by
       metis_tac[gas_origin_ptr_path_rules,APPEND_NIL] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC u.vs_inst_idx /\
   sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  `alloca_history func t` by
    (`alloca_history func (u with vs_inst_idx := SUC u.vs_inst_idx)` by
       (drule_all fn_has_code_same_block >> strip_tac >>
        `get_instruction bb u.vs_inst_idx = SOME i` by
          (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
        irule history_nonalloca_advance >> conj_tac
        >- (qexistsl_tac [`bb`,`i`] >> simp[Abbr `i`,mk_inst_def]) >>
        first_assum ACCEPT_TAC) >>
     irule alloca_history_frame >>
     qexists_tac `u with vs_inst_idx := SUC u.vs_inst_idx` >>
     simp[Abbr `t`,mstore_def,write_memory_with_expansion_def]) >>
  `t.vs_vars = u.vs_vars /\ t.vs_allocas = u.vs_allocas /\
   t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_current_bb = u.vs_current_bb` by
    simp[Abbr `t`,mstore_def,write_memory_with_expansion_def] >>
  `lookup_var root t = SOME p /\ ptr_covers G1 tn2 root t 32` by
    gvs[ptr_covers_def,op_taint_def,lookup_var_def] >>
  `mem_word_at (w2n p) t.vs_memory = w /\
   mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T` by
    simp[Abbr `t`,mstore_mem_word_at_same,mem_bytes_at_mstore_same] >>
  `!j. w2n p <= j /\ j < w2n p+32 ==> j NOTIN tn2.t_mem` by simp[] >>
  `allocas_from lo t` by
    (simp[allocas_from_def] >> qpat_assum `allocas_from lo u`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `not_fresh_at sb root` by fs[not_fresh_at_def] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` assume_tac) >>
     gvs[lookup_var_def,op_taint_def]) >>
  qexistsl_tac [`root`,`p`,`u`,`t`,`G1`,`tn2`] >>
  asm_simp_tac bool_ss [] >>
  simp[Abbr `t`,mstore_def,write_memory_with_expansion_def] >>
  rpt strip_tac >> simp[]
  >- (qpat_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==> _`
        irule >> qexists_tac `aid` >> simp[])
  >- (qpat_assum `!name b len. local_region cenv es.scopes u name b len ==> _`
        irule >> qexists_tac `name` >> simp[])
  >> gvs[] >> decide_tac
QED
