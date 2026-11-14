(* Counted bytestring writes into the constructor immutable region. *)
Theory immutableAssignBytesPathMem
Ancestors
  immutableBytestringPathMem immutableCopyExecution immutableConstructorRelation immutableDeployAssignBytes
  valueCopyBytes valueCopy exprSimBufferStore stmtLowering context compileEnv
  loweringSlice valueEncodingProps venomState loweringStateRelDefs
  immutableBytestringFootprint immutableAssignStore vyperTyping fragGasMode

Theorem immutable_assign_bytes_mem_path_endpoint:
  compile_assign_value ce dst LocCode src F sl dty sty memsz sm = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  ce.ce_imm_alloca = imm /\ fn_has_code sm sb func /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand dst s = SOME b /\
  eval_operand src s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  immutable_value_admissible dtv v /\
  val_in_memory dtv v (w2n a) s.vs_memory /\
  32 * (1 + word_size len) <= type_memory_size dtv /\
  w2n a + 32 * (1 + word_size len) < dimword (:256) /\
  w2n b + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n b) (type_memory_size dtv)
    (w2n a) (val_footprint dtv v) /\
  (!x. src = Var x \/ dst = Var x \/ (?region. imm = SOME region /\ region = Var x) ==> not_fresh_at sm x) /\
  (!j. j < 1 + word_size len ==>
    w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
    w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    mem_cont_sim ctx func s t /\
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
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_store_immutable_bytestring imm src dst sm = ((),sb)` by
    (fs[compile_assign_value_def, is_bytestring_word_type,
        comp_bind_def, comp_return_def]) >>
  drule_all compile_store_immutable_bytestring_mem_path_option >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "contents"
QED

Resume immutable_assign_bytes_mem_path_endpoint[contents]:
  `value_has_type dtv v` by
    (qspecl_then [`get_tenv cx`, `dty`, `dtv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >> gvs[] >> Cases_on `v` >>
     gvs[immutableEncodingTheory.immutable_value_admissible_def,
         value_has_type_def]) >>
  `val_footprint dtv v <= 32 * (1 + word_size len)` by
    (mp_tac (INST [``a:num`` |-> ``w2n (a:bytes32)``]
       (Q.INST [`sty` |-> `dty`, `stv` |-> `dtv`,
         `tenv` |-> `get_tenv cx`] immutable_bytestring_runtime_extent)) >>
     simp[] >> disch_then (qx_choose_then `n` strip_assume_tac) >>
     `n < dimword (:256) /\ len < dimword (:256)` by decide_tac >>
     `n = len` by fs[wordsTheory.n2w_11] >>
     qpat_assum `val_footprint dtv v = n + 32` mp_tac >>
     qpat_assum `n + 32 <= _` mp_tac >>
     qpat_assum `n = len` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[]) >>
  suspend "transfer"
QED

Resume immutable_assign_bytes_mem_path_endpoint[transfer]:
  `?n. mload (w2n a) s = n2w n /\ n + 63 < dimword (:256) /\
    val_footprint dtv v <= 32 * (1 + word_size n) /\
    32 * (1 + word_size n) <= type_memory_size dtv /\
    32 * (1 + word_size n) <= type_memory_size dtv /\
    val_in_memory dtv v (w2n b)
      (immutable_transfers T T (n2w (w2n a)) (n2w (w2n b))
        (1 + word_size n) 0 s).vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at (w2n b) (type_memory_size dtv)
        (immutable_transfers T T (n2w (w2n a)) (n2w (w2n b))
          (1 + word_size n) 0 s).vs_memory) /\
    (!p k. p+k <= w2n b \/ w2n b+type_memory_size dtv <= p ==>
      mem_bytes_at p k
        (immutable_transfers T T (n2w (w2n a)) (n2w (w2n b))
          (1 + word_size n) 0 s).vs_memory = mem_bytes_at p k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH
      (immutable_transfers T T (n2w (w2n a)) (n2w (w2n b))
        (1 + word_size n) 0 s).vs_memory` by
    (mp_tac (INST [``a:num`` |-> ``w2n (a:bytes32)``,
         ``b:num`` |-> ``w2n (b:bytes32)``]
       (Q.INST [`tenv` |-> `get_tenv cx`, `sty` |-> `dty`,
         `stv` |-> `dtv`] immutable_bytestring_runtime_transfer)) >>
     impl_tac >- (simp[] >> fs[regions_disjoint_def] >> decide_tac) >>
     simp[]) >>
  `n < dimword (:256) /\ len < dimword (:256)` by decide_tac >>
  `n = len` by fs[wordsTheory.n2w_11] >>
  qpat_assum `(t with <|vs_vars := _; vs_current_bb := _;
    vs_prev_bb := _; vs_inst_idx := _|>) = _`
    (mp_tac o AP_TERM ``\z:venom_state. z.vs_memory``) >>
  simp[] >> strip_tac >> suspend "frame"
QED

Resume immutable_assign_bytes_mem_path_endpoint[frame]:
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (mp_tac (Q.SPECL [`1 + word_size len`, `0`, `s`]
      (Q.INST [`source_word` |-> `a`, `target_word` |-> `b`]
        immutable_transfers_record_restore)) >>
     qpat_x_assum `(t with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = _` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality] >>
     rpt strip_tac >> gvs[]) >>
  `val_in_memory dtv v (w2n b) t.vs_memory /\
   immutable_value_bytes_rel dtv v
     (mem_bytes_at (w2n b) (type_memory_size dtv) t.vs_memory) /\
   (!q k. q+k <= w2n b \/ w2n b+type_memory_size dtv <= q ==>
     mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `n = len` mp_tac >>
     qpat_assum `t.vs_memory = _` mp_tac >>
     qpat_assum `val_in_memory _ _ _ (immutable_transfers _ _ _ _ _ _ _).vs_memory` mp_tac >>
     qpat_assum `immutable_value_bytes_rel _ _
       (mem_bytes_at _ _ (immutable_transfers _ _ _ _ _ _ _).vs_memory)` mp_tac >>
     qpat_assum `!p k. _ ==> mem_bytes_at p k
       (immutable_transfers _ _ _ _ _ _ _).vs_memory = _` mp_tac >>
     qpat_assum `LENGTH s.vs_memory <=
       LENGTH (immutable_transfers _ _ _ _ _ _ _).vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[arithmeticTheory.ADD_COMM]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (PURE_REWRITE_TAC [gas_marked_path_def, COND_CLAUSES] >>
     first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume immutable_assign_bytes_mem_path_endpoint[finish]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`gas_marked_path T ctx func s 0 (OK t)`,
     `mem_cont_sim ctx func s t`, `t.vs_allocas = s.vs_allocas`,
     `t.vs_alloca_next = s.vs_alloca_next`,
     `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s`,
     `(t with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = _`,
     `~t.vs_halted`, `t.vs_current_bb = sb.cs_current_bb`,
     `t.vs_inst_idx = LENGTH sb.cs_current_insts`,
     `val_in_memory dtv v (w2n b) t.vs_memory`,
     `immutable_value_bytes_rel dtv v (mem_bytes_at _ _ t.vs_memory)`,
     `!q k. _ ==> mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory`,
     `LENGTH s.vs_memory <= LENGTH t.vs_memory`,
     `(t with <|vs_vars := _; vs_memory := _; vs_immutables := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = s`,
     `s.vs_current_bb = sm.cs_current_bb`,
     `s.vs_inst_idx = LENGTH sm.cs_current_insts`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> qexists_tac `t` >>
  fs[venomStateTheory.venom_state_component_equality, arithmeticTheory.ADD_COMM] >>
  first_assum ACCEPT_TAC
QED

Finalise immutable_assign_bytes_mem_path_endpoint
