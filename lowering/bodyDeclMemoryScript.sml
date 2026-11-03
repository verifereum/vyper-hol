(* Declaration store: source-state and memory continuation boundaries. *)
Theory bodyDeclMemory
Ancestors
  bodyCopyMemory bodyMemoryDefs stmtSimDeclMem localPtrsProps stmtSimDeclStore
  stmtSimDecl valueCopy valueCopyBytes exprOperandVar freshWrites
  valueTypingMemoryProps vyperTyping exprSim stmtSim venomState
  valueEncoding valueEncodingProofs intCallResult compileEnv exprLoweringProps
  loweringSlice exprLowering exprSimBufferStore valueEncodingProofs
  words venomExecSemantics stmtLowering context fragExec fragExecMem
  allocaHistoryFragment list rich_list

Theorem body_stmt_state_rel_declare_store_frame:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_typed_store_memory_mem_ok:
  compile_store_memory ce src dst ann ann sa = ((),sb) /\
  ~is_word_type ann /\ evaluate_type tenv ann = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ann = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule val_footprint_le >> strip_tac >>
  Cases_on `is_bytestring_type ann`
  >- (gvs[compile_store_memory_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `w`] >>
      simp[] >> metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `w`] >> simp[]
QED

Theorem body_store_memory_history[local]:
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> fs[EVERY_MEM]) >>
  drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]
QED

Theorem body_decl_frag_at_cursor[local]:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts ==>
       run_inst_seq_mem_ok (emitted_insts st st') s /\
       ?t. run_inst_seq (emitted_insts st st') s = OK t /\
           Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P' = \s. P s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P' Q R` by
    (irule frag_exec_mem_run_inst_seq >> simp[Abbr `P'`] >> metis_tac[]) >>
  fs[frag_exec_mem_def, Abbr `P'`] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem annassign_memory_store_body_frag_mem:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d R.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size tyv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        return_buf_frame d cenv sb t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with scopes :=
       (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (irule body_stmt_state_rel_declare_store_frame >> simp[] >>
     qexistsl_tac [`inst`, `s`, `sa`, `w`] >> gs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  fs[same_blocks_def] >>
  irule body_decl_frag_at_cursor >>
  asm_simp_tac (srw_ss()) [IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[]
  >- (irule body_typed_store_memory_mem_ok >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      qexistsl_tac [`w`, `get_tenv cx`, `tyv`, `v`, `sw`] >>
      simp[] >> metis_tac[])
  >- simp[stmt_state_rel_inst_idx]
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
        (irule body_store_memory_history >> simp[same_blocks_def] >> metis_tac[]) >>
      `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
         LENGTH (emitted_insts sa sb)` by simp[] >> metis_tac[])
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_DECL_MEMORY_AUDIT OK\n"
     else raise Fail "body declaration memory inherited admission"
  end) [body_stmt_state_rel_declare_store_frame, body_typed_store_memory_mem_ok,
        body_store_memory_history, body_decl_frag_at_cursor,
        annassign_memory_store_body_frag_mem];
