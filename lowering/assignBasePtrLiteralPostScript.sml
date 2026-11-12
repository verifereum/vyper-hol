(* Fixed-endpoint semantic boundaries for the one-byte literal.
   Every execution equation is an input: no second run is chosen. *)
Theory assignBasePtrLiteralPost
Ancestors assignBasePtrLiteralSource exprSimAlloc exprSimLiteralBuffer
  exprLoweringProps emitHelperProps venomState venomInst venomExecSemantics
  valueEncodingProps venomMemProps immutableMemoryFrame finite_map words list
  stmtSimDeclPath loweringSlice localPtrsProps venomMemDefs compileEnv loweringStateRelDefs
  valueEncodingProofs valueEncoding valueEncodingDefs byte

Theorem assign_base_ptr_one_byte_init_endpoint:
  !s t p q a i j k.
    p <> q /\ lookup_var p s = SOME a /\
    run_inst_seq
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s = OK t ==>
    t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
          (update_var q (a + 32w) (mstore (w2n a) 1w s))
Proof
  rpt strip_tac >>
  qabbrev_tac `u = mstore (w2n a) 1w s` >>
  qabbrev_tac `v = update_var q (a + 32w) u` >>
  `step_inst_base (mk_inst i MSTORE [Var p; Lit 1w] []) s = OK u` by
    (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `lookup_var p u = SOME a` by
    simp[Abbr `u`, mstore_def, lookup_var_def] >>
  `step_inst_base (mk_inst j ADD [Var p; Lit 32w] [q]) u = OK v` by
    (simp[Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []) v =
      OK (mstore (w2n (a + 32w)) (n2w (2 ** 248)) v)` by
    (irule step_MSTORE >> simp[eval_operand_def, Abbr `v`, lookup_var_update_var]) >>
  gvs[run_inst_seq_def] >> simp[Abbr `v`, Abbr `u`]
QED

Theorem assign_base_ptr_one_byte_init_memory:
  !s t q a.
    w2n a + 64 < dimword (:256) /\
    t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
          (update_var q (a + 32w) (mstore (w2n a) 1w s)) ==>
    mem_word_at (w2n a) t.vs_memory = 1w /\
    mem_word_at (w2n a + 32) t.vs_memory = n2w (2 ** 248) /\
    (!b len. b + len <= w2n a \/ w2n a + 64 <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (a + 32w) = w2n a + 32` by
    (irule EQ_TRANS >> qexists_tac `w2n a + w2n (32w:bytes32)` >>
     conj_tac >- (irule w2n_add_2 >> fs[dimword_def] >> decide_tac) >> simp[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> conj_tac >-
    simp[mstore_mem_word_at_disjoint, update_var_def, mstore_mem_word_at_same] >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  rpt strip_tac >>
  `mem_bytes_at b len
     (mstore (w2n a + 32) (n2w (2 ** 248))
       (update_var q (a + 32w) (mstore (w2n a) 1w s))).vs_memory =
   mem_bytes_at b len (update_var q (a + 32w) (mstore (w2n a) 1w s)).vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  gvs[update_var_def] >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED


Theorem assign_base_ptr_init_frame[local]:
  !s q off1 off2 w1 w2 v.
    (mstore off2 w2 (update_var q v (mstore off1 w1 s))).vs_allocas = s.vs_allocas /\
    (mstore off2 w2 (update_var q v (mstore off1 w1 s))
       with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. x <> q ==>
      lookup_var x (mstore off2 w2 (update_var q v (mstore off1 w1 s))) = lookup_var x s) /\
    lookup_var q (mstore off2 w2 (update_var q v (mstore off1 w1 s))) = SOME v
Proof
  rpt gen_tac >> conj_tac
  >- simp[mstore_def, update_var_def] >>
  conj_tac
  >- (pure_rewrite_tac[mstore_def, LET_THM, update_var_def] >> simp_tac (srw_ss()) []) >>
  conj_tac
  >- (rpt strip_tac >> simp[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem assign_base_ptr_one_byte_init_frame:
  !s t q a.
    t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
          (update_var q (a + 32w) (mstore (w2n a) 1w s)) ==>
    t.vs_allocas = s.vs_allocas /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. x <> q ==> lookup_var x t = lookup_var x s) /\
    lookup_var q t = SOME (a + 32w)
Proof
  rpt gen_tac >> disch_then SUBST1_TAC >>
  MATCH_ACCEPT_TAC assign_base_ptr_init_frame
QED

Theorem assign_base_ptr_one_byte_run_split:
  !sa buf sb s t.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?u.
      step_inst_base
        (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
          [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
      run_inst_seq
        [mk_inst (sa.cs_next_id + 1) MSTORE
           [Var (STRING #"%" (toString sa.cs_next_var)); Lit 1w] [];
         mk_inst (sa.cs_next_id + 2) ADD
           [Var (STRING #"%" (toString sa.cs_next_var)); Lit 32w]
           [STRING #"%" (toString (sa.cs_next_var + 1))];
         mk_inst (sa.cs_next_id + 3) MSTORE
           [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
            Lit (n2w (2 ** 248))] []] u = OK t
Proof
  rpt strip_tac >> drule assign_base_ptr_one_byte_code >> strip_tac >>
  Cases_on `step_inst_base
    (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) s` >>
  fs[Once run_inst_seq_def] >> metis_tac[run_inst_seq_def]
QED

Theorem assign_base_ptr_alloca_endpoint:
  !func cenv cx es s inst p n t ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\ exec_alloca inst s n = OK t ==>
    stmt_state_rel ctx func cenv cx es t /\
    ?w. lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,w2n n) /\
      w2n w + w2n n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b sz. aid <> inst.inst_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n w) (w2n n) b sz) /\
      (!name b sz. local_region cenv es.scopes t name b sz ==>
        regions_disjoint (w2n w) (w2n n) b sz)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  drule_all exec_alloca_frames >> strip_tac >>
  drule exec_alloca_memory >> strip_tac >>
  `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `w2n w + w2n n < dimword (:256)` by
    (`t.vs_alloca_next < dimword (:256)` by
       metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  fs[dimword_def] >> conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
      fs[alloca_inv_def, allocas_non_overlapping_def, regions_disjoint_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
      disch_then (qspecl_then [`b`, `sz`, `w2n w`, `w2n n`] mp_tac) >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem assign_base_ptr_one_byte_alloc_endpoint:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?u a.
      stmt_state_rel ctx func cenv cx es u /\
      lookup_var (STRING #"%" (toString sa.cs_next_var)) u = SOME a /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n a,64) /\
      w2n a + 64 < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      (!x. x <> STRING #"%" (toString sa.cs_next_var) ==>
        lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b sz. aid <> sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n a) 64 b sz) /\
      (!name b sz. local_region cenv es.scopes u name b sz ==>
        regions_disjoint (w2n a) 64 b sz) /\
      t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
        (update_var (STRING #"%" (toString (sa.cs_next_var + 1))) (a + 32w)
          (mstore (w2n a) 1w u))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_run_split >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `exec_alloca inst s (64w:bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Abbr `inst`, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (64w:bytes32)] /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  drule_all assign_base_ptr_alloca_endpoint >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <>
   STRING #"%" (toString (sa.cs_next_var + 1))` by
    simp[ASCIInumbersTheory.toString_11] >>
  drule_all assign_base_ptr_one_byte_init_endpoint >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> fs[Abbr `inst`, mk_inst_def, dimword_def] >>
  metis_tac[]
QED

Theorem assign_base_ptr_init_memory_length[local]:
  !s q off1 off2 w1 w2 v.
    LENGTH s.vs_memory <=
      LENGTH (mstore off2 w2 (update_var q v (mstore off1 w1 s))).vs_memory
Proof
  rpt gen_tac >> simp[immutable_mstore_capacity, update_var_def,
    arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem assign_base_ptr_one_byte_init_old_vars:
  !sa u t a.
    t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
      (update_var (STRING #"%" (toString (sa.cs_next_var + 1))) (a + 32w)
        (mstore (w2n a) 1w u)) ==>
    !x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u
Proof
  rpt gen_tac >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >>
  rpt strip_tac >> first_x_assum irule >>
  fs[not_fresh_at_def] >> strip_tac >>
  first_x_assum (qspec_then `sa.cs_next_var + 1` mp_tac) >> simp[]
QED

Theorem assign_base_ptr_one_byte_init_state_rel:
  !ctx func cenv cx es sa u t a.
    stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
    ~cenv.ce_is_ctor /\ w2n a + 64 < dimword (:256) /\
    (!name b sz. local_region cenv es.scopes u name b sz ==>
      regions_disjoint (w2n a) 64 b sz) /\
    t = mstore (w2n (a + 32w)) (n2w (2 ** 248))
      (update_var (STRING #"%" (toString (sa.cs_next_var + 1))) (a + 32w)
        (mstore (w2n a) 1w u)) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt gen_tac >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_memory >> strip_tac >>
  drule assign_base_ptr_one_byte_init_old_vars >> strip_tac >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory` by
    (qpat_x_assum `t = _` SUBST1_TAC >>
     MATCH_ACCEPT_TAC assign_base_ptr_init_memory_length) >>
  qpat_x_assum `t = _` kall_tac >>
  irule literal_state_memory_frame >> qexists_tac `u` >> simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ _ = _` irule >>
     qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >-
    (rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  drule_all local_ptrs_reserved_imm_base >> simp[]
QED

Theorem assign_base_ptr_one_byte_run_state_rel:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~cenv.ce_is_ctor /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt strip_tac >> drule_all assign_base_ptr_one_byte_alloc_endpoint >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_state_rel >> simp[]
QED

Theorem assign_base_ptr_one_byte_value:
  !b m n.
    mem_word_at b m = 1w /\
    mem_word_at (b + 32) m = n2w (2 ** 248) ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV [1w]) b m
Proof
  rpt gen_tac >> strip_tac >>
  `TAKE 1 (word_to_bytes (n2w (2 ** 248):bytes32) T) = [1w:word8]` by
    (simp[byteTheory.word_to_bytes_def, dimindex_256] >> EVAL_TAC >>
     simp[dimindex_256] >> CONV_TAC wordsLib.WORD_EVAL_CONV) >>
  `TAKE 1 (mem_bytes_at (b + 32) 32 m) = [1w:word8]` by
    (rewrite_tac[mem_bytes_at_word] >> asm_rewrite_tac[]) >>
  qspecl_then [`b + 32`, `1`, `31`, `m`] mp_tac mem_bytes_at_split_padded >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_CLAUSES] >> strip_tac >>
  `mem_bytes_at (b + 32) 1 m = [1w:word8]` by
    (qpat_x_assum `TAKE 1 (mem_bytes_at _ _ _) = _` mp_tac >>
     asm_rewrite_tac[] >> simp[TAKE_APPEND1, LENGTH_mem_bytes_at_proof] >>
     metis_tac[TAKE_LENGTH_ID, LENGTH_mem_bytes_at_proof]) >>
  simp[val_in_memory_def]
QED

Theorem assign_base_ptr_one_byte_run_frame:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_alloc_endpoint >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >>
  drule assign_base_ptr_one_byte_init_old_vars >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_memory >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >> fs[not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `t = _` kall_tac >>
  qpat_assum `u.vs_memory = s.vs_memory`
    (fn th => pure_rewrite_tac[GSYM th]) >> conj_asm1_tac
  >- metis_tac[] >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ _ = _` irule >>
      `aid <> sa.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid b sz. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `local_region cenv es.scopes u name b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem assign_base_ptr_one_byte_run_value:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    expr_val_rel cx (BaseT (BytesT (Dynamic 64))) (BytesV [1w]) buf.buf_operand t /\
    expr_val_at cenv cx (BaseT (BytesT (Dynamic 64))) sa sb es
      (BytesV [1w]) buf.buf_operand t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_alloc_endpoint >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >>
  drule assign_base_ptr_one_byte_init_old_vars >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_memory >> strip_tac >>
  drule assign_base_ptr_one_byte_code >> strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic 64))) (BytesV [1w])
     (w2n a) t.vs_memory` by
    (irule assign_base_ptr_one_byte_value >> simp[]) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
     simp[assign_base_ptr_one_byte_initialization, contextTheory.compile_alloc_buffer_def,
          emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[]) >>
  `STRING #"%" (toString sa.cs_next_var) <>
   STRING #"%" (toString (sa.cs_next_var + 1))` by
    simp[ASCIInumbersTheory.toString_11] >>
  qpat_x_assum `t = _` kall_tac >>
  `eval_operand buf.buf_operand t = SOME a` by
    simp[eval_operand_def] >> conj_tac
  >- (simp[loweringPostsTheory.expr_val_rel_def,
           vyperValueTheory.evaluate_type_def, is_word_type_def] >>
      qexists_tac `a` >> simp[]) >>
  simp[loweringPostsTheory.expr_val_at_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def, vyperValueTheory.type_slot_size_def,
       vfmConstantsTheory.word_size_def] >>
  disj1_tac >>
  qexistsl_tac [`sa.cs_next_id`, `w2n a`, `64`] >>
  simp[loweringPostsTheory.val_footprint_def] >> rpt strip_tac >>
  `local_region cenv es.scopes u n lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `es.scopes`, `t`] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

(* The literal writes only inside its own fresh 64-byte allocation. *)
Theorem assign_base_ptr_one_byte_run_pure[local]:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    pure_frame cenv func es sa s t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_run_frame >> strip_tac >>
  drule_all assign_base_ptr_one_byte_alloc_endpoint >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_memory >> strip_tac >>
  match_mp_tac (exprSimPropsTheory.pure_frame_fresh_alloca
    |> Q.SPECL [`cenv`, `func`, `es`, `sa`, `s`, `t`, `sa.cs_next_id`,
                `[Lit 64w]`, `[STRING #"%" (toString sa.cs_next_var)]`,
                `w2n (a:bytes32)`, `64`]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `t.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `u.vs_memory = s.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ t.vs_memory = _` irule >>
  qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
  simp[regions_disjoint_def]
QED

Theorem assign_base_ptr_one_byte_run_post:
  !func cenv cx es sa buf sb s t ctx.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~cenv.ce_is_ctor /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    expr_post ctx func cenv cx
      (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))
      es sa sb s es (BytesV [1w]) buf.buf_operand t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_run_state_rel >> strip_tac >>
  drule_all assign_base_ptr_one_byte_run_frame >> strip_tac >>
  drule_all assign_base_ptr_one_byte_run_value >> strip_tac >>
  `locals_kept cenv es es s t` by
    (irule exprSimPropsTheory.locals_kept_regions >> first_assum ACCEPT_TAC) >>
  drule_all assign_base_ptr_one_byte_run_pure >> strip_tac >>
  simp[loweringPostsTheory.expr_post_def, vyperASTTheory.expr_type_def] >> metis_tac[]
QED
