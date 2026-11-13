(* Counted bytestring writes into the constructor immutable region. *)
Theory immutableAssignBytesMem
Ancestors
  immutableLoopStoreMem immutableCopyExecution immutableConstructorRelation immutableDeployAssignBytes
  valueCopyBytes valueCopy exprSimBufferStore stmtLowering context compileEnv
  loweringSlice valueEncodingProps venomState loweringStateRelDefs

Theorem bytestring_counted_footprint[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  immutable_value_admissible tv v /\ val_in_memory tv v p s.vs_memory /\
  mload p s = n2w len /\ len < dimword (:256) /\
  type_memory_size tv < dimword (:256) ==>
  val_footprint tv v <= 32 * (1 + word_size len)
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[immutable_admissible_val_wf] >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >>
  gvs[immutableEncodingTheory.immutable_value_admissible_def,
      valueEncodingDefsTheory.val_wf_def,
      valueEncodingDefsTheory.val_in_memory_def,
      loweringPostsTheory.val_footprint_def,
      mem_word_at_eq_mload] >>
  simp[arithmeticTheory.LEFT_ADD_DISTRIB] >>
  metis_tac[valueTypingMemoryPropsTheory.word_size_capacity]
QED

Theorem immutable_assign_bytes_mem_endpoint:
  compile_assign_value ce dst LocCode src F sl dty sty di memsz sm = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  ce.ce_imm_alloca = SOME region /\ fn_has_code sm sb func /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME b /\
  eval_operand src s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  immutable_value_admissible dtv v /\
  val_in_memory dtv v (w2n a) s.vs_memory /\
  32 * (1 + word_size len) <= type_memory_size dtv /\
  w2n a + 32 * (1 + word_size len) < dimword (:256) /\
  w2n b + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n b) (type_memory_size dtv)
    (w2n a) (32 * (1 + word_size len)) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  (!j. j < 1 + word_size len ==>
    w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
    w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) =
      immutable_transfers T T a b (1 + word_size len) 0 s /\
    val_in_memory dtv v (w2n b) t.vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at (w2n b) (type_memory_size dtv) t.vs_memory) /\
    (!q k. q+k <= w2n b \/ w2n b+type_memory_size dtv <= q ==>
      mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_store_immutable_bytestring (SOME region) src dst sm = ((),sb)` by
    (fs[compile_assign_value_def, is_bytestring_word_type,
        comp_bind_def, comp_return_def]) >>
  drule_all compile_store_immutable_bytestring_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "contents"
QED

Resume immutable_assign_bytes_mem_endpoint[contents]:
  `val_wf dtv v` by metis_tac[immutable_admissible_val_wf] >>
  `t.vs_memory = (mcopy (w2n b) (w2n a) (32*(1+word_size len)) s).vs_memory` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = _`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_memory``) >>
     simp[] >> disch_then kall_tac >>
     qspecl_then [`1+word_size len`, `w2n a`, `w2n b`, `0`, `s`]
       mp_tac (Q.INST [`store` |-> `T`, `ctor` |-> `T`]
         immutable_memory_transfers_snapshot) >>
     simp[regions_disjoint_def] >>
     impl_tac >- (gvs[regions_disjoint_def] >> decide_tac) >>
     simp[]) >>
  `len < dimword (:256) /\ type_memory_size dtv < dimword (:256)` by decide_tac >>
  `val_footprint dtv v <= 32*(1+word_size len)` by
    (irule bytestring_counted_footprint >> metis_tac[]) >>
  `val_in_memory dtv v (w2n b) t.vs_memory` by
    (simp[] >> irule mcopy_val_in_memory >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >-
    (irule immutable_memory_bytes >>
     simp[] >> irule mcopy_val_in_memory >> simp[]) >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac
QED

Finalise immutable_assign_bytes_mem_endpoint
