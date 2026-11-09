(* Counted sparse array-loop boundaries. *)
Theory storeSlotsCountedElements
Ancestors
  storeSlotsCountedControl storeSlotsCountedBase placeStoreSlots
  context compileEnv fragExec fragGasMode venomState venomInst emitHelperProps
  valueEncoding valueEncodingProps words arithmetic list rich_list finite_map
  storeSlotsMemoryPaths fragExecMem instMemFrontier venomExecSemantics
  emitHelper exprLoweringProps memSafeRun

Theorem store_slots_loop_init_mem[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    store_slots_prefix sa etv el tr sw dw s 0 [] u /\
    u.vs_alloca_next = s.vs_alloca_next /\
    lookup_var cv u = SOME 0w /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME ibb /\
   DROP s.vs_inst_idx ibb.bb_instructions =
     [mk_inst id1 ASSIGN [Lit 0w] [cv]; mk_inst id2 JMP [Label hdr] []]` by simp[] >>
  drule_all store_slots_array_init_mem >> strip_tac >>
  qexists_tac `jump_to hdr ((update_var cv 0w s) with
    vs_inst_idx := s.vs_inst_idx + 1)` >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- simp[jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule store_slots_prefix_init_control >>
  simp[store_slots_prefix_empty] >> metis_tac[]
QED

Theorem store_slots_loop_exit_mem[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw N ks u.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  store_slots_prefix sa etv el tr sw dw s N ks u /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
  lookup_var cv u = SOME (n2w N) /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  ?t. gas_marked_path T ctx func u 0 (OK t) /\
    store_slots_prefix sa etv el tr sw dw s N ks t /\
    t.vs_alloca_next = u.vs_alloca_next /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `~u.vs_halted /\ eval_operand cnt u = SOME (n2w N)` by
    (fs[store_slots_prefix_def] >> Cases_on `cnt` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb /\
   eval_operand (Var cv) u = SOME (n2w N)` by simp[eval_operand_def] >>
  `N <= N` by simp[] >>
  drule_all store_slots_array_condition_mem >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit ((update_var dv (bool_to_word T)
    (update_var lv (bool_to_word F) u)) with vs_inst_idx := 2)` >>
  conj_tac >- simp[] >>
  reverse conj_tac >- simp[jump_to_def, update_var_def] >>
  irule store_slots_prefix_control >> simp[] >> metis_tac[]
QED

Theorem store_slots_addresses_mem_ok[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[comp_bind_def, comp_return_def, emit_op_def, fresh_var_def,
       emit_inst_def, fresh_id_def, emit_def, comp_ignore_bind_def] >>
  strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem store_slots_addresses_forward_mem[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_addresses_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule store_slots_addresses_mem_ok >> simp[]) >>
  `LENGTH (FILTER (\j. j.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `EVERY (\j. j.inst_opcode <> GAS) _` mp_tac >>
     simp[LENGTH_NIL, FILTER_EQ_NIL]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule store_slots_emitted_seq_path_mem >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, same_blocks_def] >>
  qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >> simp[]
QED

Theorem store_slots_element_forward_mem[local]:
  (!src slot tr sa sb func s sw dw writes.
    compile_store_slots cenv src slot elem tr sa = ((),sb) /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    w2n sw + type_memory_size tv <= s.vs_alloca_next /\
    w2n dw + type_slot_size tv <= dimword (:256) /\
    encode_value tv v = SOME writes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
    ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
          (mload (w2n sw + 32*j) s) q) s ks /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_alloca_next = s.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  compile_store_slots cenv sp dp elem tr sc = ((),sd) /\
  (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
  eval_operand sp a = SOME (sw + n2w (i * type_memory_size tv)) /\
  eval_operand dp a = SOME (dw + n2w (i * type_slot_size tv)) /\
  val_in_memory tv v (w2n sw + i * type_memory_size tv) s.vs_memory /\
  encode_value tv v = SOME writes /\ a.vs_memory = s.vs_memory /\
  i < N /\
  w2n sw + N * type_memory_size tv < dimword (:256) /\
  w2n sw + N * type_memory_size tv <= a.vs_alloca_next /\
  w2n dw + N * type_slot_size tv <= dimword (:256) /\
  fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
  ~a.vs_halted /\ a.vs_current_bb = sc.cs_current_bb /\
  a.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~a.vs_call_ctx.cc_static /\
  store_copy_normalize s a =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks ==>
  ?t js. gas_marked_path T ctx func a 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q)
        s (ks ++ MAP (\j. i * type_slot_size tv + j) js) /\
    (!j. MEM j js <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x a) /\
    t.vs_allocas = a.vs_allocas /\ t.vs_memory = a.vs_memory /\
    t.vs_labels = a.vs_labels /\ t.vs_call_ctx = a.vs_call_ctx /\
    t.vs_alloca_next = a.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_element_bounds >> strip_tac >>
  `i * type_memory_size tv + type_memory_size tv <= N * type_memory_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n sw + i * type_memory_size tv + type_memory_size tv <= a.vs_alloca_next` by
    decide_tac >>
  `sw + n2w (i * type_memory_size tv) =
   n2w (w2n sw + i * type_memory_size tv)` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  gvs[] >>
  first_x_assum (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`t`,`ks'`] >> simp[] >>
  `w2n sw + i * type_memory_size tv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`js` |-> `ks'`, `sw` |-> `sw:bytes32`]
    (INST_TYPE [``:'a`` |-> ``:256``] store_slots_compose_fold)) >>
  simp[]
QED

Theorem store_slots_loop_round_mem[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw N i ks u.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  type_memory_bytes cenv elem = type_memory_size etv /\
  (!r. r < N ==>
    (!src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot elem tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory etv (el r) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size etv < dimword (:256) /\
      w2n sw + type_memory_size etv <= s.vs_alloca_next /\
      w2n dw + type_slot_size etv <= dimword (:256) /\
      encode_value etv (el r) = SOME writes /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
      ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
        store_copy_normalize s t =
          FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
            (mload (w2n sw + 32*j) s) q) s ks /\
        (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
        t.vs_alloca_next = s.vs_alloca_next /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
    IS_SOME (encode_value etv (el r)) /\
    val_in_memory etv (el r) (w2n sw + r * type_memory_size etv) s.vs_memory) /\
  (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
  w2n sw + N * type_memory_size etv < dimword (:256) /\
  w2n sw + N * type_memory_size etv <= s.vs_alloca_next /\
  w2n dw + N * type_slot_size etv <= dimword (:256) /\
  fn_inst_ids_distinct func /\ ~s.vs_call_ctx.cc_static /\
  i < N /\ store_slots_prefix sa etv el tr sw dw s i ks u /\
  u.vs_alloca_next = s.vs_alloca_next /\
  lookup_var cv u = SOME (n2w i) /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  ?v ks'. gas_marked_path T ctx func u 0 (OK v) /\
    store_slots_prefix sa etv el tr sw dw s (SUC i) ks' v /\
    v.vs_alloca_next = s.vs_alloca_next /\
    lookup_var cv v = SOME (n2w (SUC i)) /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `~u.vs_halted /\ eval_operand cnt u = SOME (n2w N) /\
   eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    (fs[store_slots_prefix_def] >>
     conj_tac >- (Cases_on `cnt` >> fs[eval_operand_def] >> metis_tac[]) >>
     conj_tac >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `slot` >> fs[eval_operand_def] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb /\
   eval_operand (Var cv) u = SOME (n2w i) /\ i <= N` by
    (simp[eval_operand_def] >> decide_tac) >>
  drule_all store_slots_array_condition_mem >> simp[] >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func u 0 (OK hu)` >>
  `store_slots_prefix sa etv el tr sw dw s i ks hu` by
    (simp[Abbr `hu`] >> irule store_slots_prefix_control >> simp[] >> metis_tac[]) >>
  suspend "body"
QED

Resume store_slots_loop_round_mem[body]:
  `lookup_var cv hu = SOME (n2w i) /\ ~hu.vs_halted /\
   hu.vs_current_bb = bs.cs_current_bb /\
   hu.vs_inst_idx = LENGTH bs.cs_current_insts` by
    (simp[Abbr `hu`, jump_to_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `eval_operand src hu = SOME sw /\ eval_operand slot hu = SOME dw` by
    (fs[store_slots_prefix_def] >>
     conj_tac >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `slot` >> fs[eval_operand_def] >> metis_tac[]) >>
  `(!x. src = Var x ==> not_fresh_at bs x) /\
   (!x. slot = Var x ==> not_fresh_at bs x)` by
    (fs[ci_mono_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  drule_all store_slots_addresses_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path T ctx func hu 0 (OK a)` >>
  `a.vs_memory = hu.vs_memory /\ a.vs_call_ctx = hu.vs_call_ctx /\
   a.vs_allocas = hu.vs_allocas /\ a.vs_labels = hu.vs_labels /\
   a.vs_alloca_next = hu.vs_alloca_next /\
   store_copy_normalize s a = store_copy_normalize s hu` by
    (qpat_x_assum `a with <|vs_vars := _; vs_inst_idx := _|> = hu` mp_tac >>
     simp[venom_state_component_equality, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     metis_tac[]) >>
  `store_slots_prefix sa etv el tr sw dw s i ks a` by
    (irule store_slots_prefix_transfer >> simp[] >> qexists_tac `hu` >>
     simp[] >> fs[ci_mono_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `a.vs_memory = s.vs_memory /\ ~a.vs_call_ctx.cc_static /\
   store_copy_normalize s a =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks` by fs[store_slots_prefix_def] >>
  `type_memory_size etv DIV 32 = type_slot_size etv` by
    simp[type_memory_size_slots] >>
  `eval_operand dp a = SOME (dw + n2w (i * type_slot_size etv))` by fs[] >>
  qpat_x_assum `!r. r < N ==> _` (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `IS_SOME (encode_value etv (el i))` mp_tac >>
  rewrite_tac[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `writes` assume_tac) >>
  suspend "element"
QED

Resume store_slots_loop_round_mem[element]:
  `?t js. gas_marked_path T ctx func a 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q)
        s (ks ++ MAP (\j. i * type_slot_size etv + j) js) /\
    (!j. MEM j js <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x a) /\
    t.vs_allocas = a.vs_allocas /\ t.vs_memory = a.vs_memory /\
    t.vs_labels = a.vs_labels /\ t.vs_call_ctx = a.vs_call_ctx /\
    t.vs_alloca_next = a.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (irule store_slots_element_forward_mem >>
     simp[] >>
     conj_tac
     >- (qexists_tac `N` >> simp[Abbr `hu`, jump_to_def, update_var_def]) >>
     qexistsl_tac [`cenv`, `dp`, `elem`, `sp`, `el i`] >>
     simp[] >> conj_tac >- metis_tac[] >>
     qpat_x_assum `!src' slot' tr' sa' sb' func' s' sw' dw' writes'. _` mp_tac >>
     simp[]) >>
  suspend "backedge"
QED

Resume store_slots_loop_round_mem[backedge]:
  `store_slots_prefix sa etv el tr sw dw s (SUC i)
     (ks ++ MAP (\j. i * type_slot_size etv + j) js) t` by
    (pure_rewrite_tac[store_slots_prefix_def] >>
     conj_tac >- simp[] >>
     conj_tac >- (irule store_slots_prefix_members_step >>
       fs[store_slots_prefix_def] >> metis_tac[]) >>
     fs[store_slots_prefix_def, ci_mono_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `lookup_var cv t = SOME (n2w i)` by metis_tac[] >>
  `SUC i < dimword (:256)` by decide_tac >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME tbb /\
   DROP t.vs_inst_idx tbb.bb_instructions =
     [mk_inst tid1 ADD [Var cv; Lit 1w] [iv];
      mk_inst tid2 ASSIGN [Var iv] [cv]; mk_inst tid3 JMP [Label hdr] []]` by simp[] >>
  drule_all store_slots_array_backedge_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func t 0 (OK v)` >>
  qexistsl_tac [`v`, `ks ++ MAP (\j. i * type_slot_size etv + j) js`] >>
  reverse conj_tac
  >- (conj_tac
      >- (qunabbrev_tac `v` >> irule store_slots_prefix_control >>
          simp[] >> metis_tac[]) >>
      simp[Abbr `v`, Abbr `hu`, jump_to_def, lookup_var_def, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `hu` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `a` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `t` >> conj_tac >> first_assum ACCEPT_TAC
QED
Finalise store_slots_loop_round_mem
