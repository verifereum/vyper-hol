(* Concrete mixed stack/memory staging for word-valued internal arguments. *)
Theory tupleAssignImmutableDeployIntStageWords
Ancestors
  exprSimMapKey exprSimConcatResult exprSimAlloc exprLoweringProps
  exprLowering emitHelperProps emitHelper freshWrites fragGasMode loweringHalt
  loweringStateRelDefs compileEnv venomState venomInst finite_map list rich_list

Theorem stage_word_shape[local]:
  !vals flags tys ce sa ops sb.
    LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
    EVERY is_word_type tys /\
    EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals /\
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    inst_extends sa sb /\ LENGTH ops = LENGTH vals /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >> simp[compile_stage_intcall_args_def, comp_return_def,
                inst_extends_refl, emitted_insts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `flags` >> Cases_on `tys` >> gvs[] >>
  Cases_on `h'`
  >- (gvs[compile_stage_intcall_args_def, unwrap_value_def,
          comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >>
      first_x_assum (qspecl_then [`t`, `t'`, `ce`, `sa`, `rest`, `cs'`] mp_tac) >>
      simp[emitted_insts_def]) >>
  gvs[compile_stage_intcall_args_def, unwrap_value_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_return_def] >>
  rename1 `inst_extends sa sb` >>
  first_x_assum (qspecl_then [`t`, `t'`, `ce`, `cs''`, `rest`, `sb`] mp_tac) >>
  simp[] >> strip_tac >>
  `cs''.cs_current_bb = sa.cs_current_bb /\
   cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs'' /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sa cs'')` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND1, DROP_APPEND2, mk_inst_def,
         is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa cs'' ++ emitted_insts cs'' sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[GSYM emitted_insts_def] >>
  metis_tac[inst_extends_trans, inst_extends_def]
QED

Theorem stage_words_seq[local]:
  !vals flags tys ce sa ops sb ctx func cx es s.
    LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
    EVERY is_word_type tys /\
    EVERY (\vv. ?ty op w. vv = StackValue ty op /\ is_word_type ty /\
      (!x. op = Var x ==> not_fresh_at sa x) /\
      eval_operand op s = SOME w) vals /\
    EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys /\
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func ce cx es t /\
      t.vs_labels = s.vs_labels /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
      (!i ty op. i < LENGTH vals /\ EL i vals = StackValue ty op ==>
        if EL i flags then eval_operand (EL i ops) t = eval_operand op s
        else ?aid b. sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          FLOOKUP t.vs_allocas aid =
            SOME (b, MAX 32 (type_memory_bytes ce (EL i tys))) /\
          eval_operand (EL i ops) t = SOME (n2w b) /\
          b + MAX 32 (type_memory_bytes ce (EL i tys)) < dimword (:256) /\
          (!name lb lsz. local_region ce es.scopes t name lb lsz ==>
            regions_disjoint b (MAX 32 (type_memory_bytes ce (EL i tys))) lb lsz))
Proof
  Induct
  >- (simp[compile_stage_intcall_args_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_refl, run_inst_seq_def] >>
      qexists `s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `flags` >> Cases_on `tys` >> gvs[] >>
  Cases_on `h'`
  >- (gvs[compile_stage_intcall_args_def, unwrap_value_def,
           comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `compile_stage_intcall_args ce vals t t' sa = (rest,sb)` >>
      first_x_assum (qspecl_then [`t`, `t'`, `ce`, `sa`, `rest`, `sb`,
        `ctx`, `func`, `cx`, `es`, `s`] mp_tac) >>
      simp[] >> strip_tac >> qexists `t''` >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> Cases_on `i` >> simp[]
      >- (rpt strip_tac >> gvs[] >> Cases_on `op` >> gvs[eval_operand_def]) >>
      metis_tac[]) >>
  suspend "memory_head"
QED

Resume stage_words_seq[memory_head]:
  gvs[compile_stage_intcall_args_def, unwrap_value_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_return_def] >>
  rename1 `compile_stage_intcall_args ce vals t t' sh = (rest,sb)` >>
  `ci_mono sa cs' /\ ci_mono cs' sh /\ ci_mono sh sb` by
    (conj_tac >- metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_void, pairTheory.SND] >>
     metis_tac[ci_mono_compile_stage_intcall_args, pairTheory.SND]) >>
  `cs_extends sa cs' /\ cs_extends cs' sh /\ cs_extends sh sb /\
   cs_extends cs' sb /\ cs_extends sa sh` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa cs' func /\ fn_has_code sh sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (MAX 32 (type_memory_bytes ce h'')))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  `32 <= MAX 32 (type_memory_bytes ce h'') /\
   MAX 32 (type_memory_bytes ce h'') < dimword (:256)` by simp[] >>
  drule_all hash_alloc_capacity_mstore_frame >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sh) s = OK u` >>
  `!x. not_fresh_at sa x ==> not_fresh_at sh x` by
    (gvs[ci_mono_def, not_fresh_at_def]) >>
  `EVERY (\vv. ?ty op w. vv = StackValue ty op /\ is_word_type ty /\
      (!x. op = Var x ==> not_fresh_at sh x) /\
      eval_operand op u = SOME w) vals` by
    (qpat_x_assum `EVERY _ vals` mp_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> goal_assum drule >> simp[] >>
     Cases_on `op'` >> gvs[eval_operand_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`t`, `t'`, `ce`, `sh`, `rest`, `sb`,
    `ctx`, `func`, `cx`, `es`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t''` by
    (drule_all stage_word_shape >> strip_tac >>
     `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by
       gvs[inst_extends_def] >>
     `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
       (irule emitted_insts_append >> simp[]) >>
     metis_tac[run_inst_seq_append]) >>
  suspend "memory_frames"
QED

Resume stage_words_seq[memory_frames]:
  qexists `t''` >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
    `aid < sa.cs_next_id + 2` by decide_tac >>
    qpat_x_assum `!aid b len. aid < sa.cs_next_id + 2 /\ _ ==> _` drule >>
    simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `i` >> simp[]
  >- (rpt strip_tac >> gvs[] >>
      qexistsl [`sa.cs_next_id`, `w2n addr`] >> simp[] >>
      conj_tac >- (gvs[ci_mono_def] >> decide_tac) >>
      conj_tac >- (Cases_on `buf_alloc.buf_operand` >>
        gvs[eval_operand_def] >> metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >>
      metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame]) >>
  rpt strip_tac >>
  qpat_x_assum `!i ty' op'. i < LENGTH vals /\ _ ==> _`
    (qspecl_then [`n`, `ty'`, `op'`] mp_tac) >> simp[] >>
  Cases_on `EL n t` >> simp[]
  >- (gvs[EVERY_MEM] >>
      `?w. eval_operand op' s = SOME w /\
        (!x. op' = Var x ==> not_fresh_at sa x)` by
        metis_tac[MEM_EL, contextTheory.vyper_value_11] >>
      Cases_on `op'` >> gvs[eval_operand_def] >> metis_tac[]) >>
  strip_tac >> qexistsl [`aid`, `b`] >> gvs[] >> first_assum ACCEPT_TAC
QED

Finalise stage_words_seq

Theorem tuple_immutable_stage_words_run:
  !vals flags tys ce sa ops sb ctx func cx es s.
    LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
    EVERY is_word_type tys /\
    EVERY (\vv. ?ty op w. vv = StackValue ty op /\ is_word_type ty /\
      (!x. op = Var x ==> not_fresh_at sa x) /\
      eval_operand op s = SOME w) vals /\
    EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys /\
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func ce cx es t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ LENGTH ops = LENGTH vals /\
      t.vs_labels = s.vs_labels /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
      (!i ty op. i < LENGTH vals /\ EL i vals = StackValue ty op ==>
        if EL i flags then eval_operand (EL i ops) t = eval_operand op s
        else ?aid b. sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          FLOOKUP t.vs_allocas aid =
            SOME (b, MAX 32 (type_memory_bytes ce (EL i tys))) /\
          eval_operand (EL i ops) t = SOME (n2w b) /\
          b + MAX 32 (type_memory_bytes ce (EL i tys)) < dimword (:256) /\
          (!name lb lsz. local_region ce es.scopes t name lb lsz ==>
            regions_disjoint b (MAX 32 (type_memory_bytes ce (EL i tys))) lb lsz))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all stage_words_seq >> strip_tac >>
  `EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all stage_word_shape >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all concat_straight_gas_path >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[gas_marked_path_def, eval_operand_def, lookup_var_def,
      local_region_def, stmt_state_rel_inst_idx] >>
  first_assum ACCEPT_TAC
QED

Theorem tuple_immutable_intcall_mixed_word_entry_owned:
  compile_alloc_buffer sz st1 = (buf,st2) /\
  compile_stage_intcall_args ce vals flags tys st2 = (ops,st3) /\
  LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
  EVERY is_word_type tys /\
  EVERY (\vv. ?ty op w. vv = StackValue ty op /\ is_word_type ty /\
    (!x. op = Var x ==> not_fresh_at st1 x) /\
    eval_operand op s = SOME w) vals /\
  EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys /\
  fn_has_code st1 st3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st1 /\ stmt_state_rel ctx func ce cx es s /\
  sz < dimword (:256) /\ origin.cs_next_id <= st1.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st1.cs_current_bb /\
  s.vs_inst_idx = LENGTH st1.cs_current_insts ==>
  ?t b. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx es t /\
    FLOOKUP t.vs_allocas st1.cs_next_id = SOME (b,sz) /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    b + sz < dimword (:256) /\
    origin.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id < st3.cs_next_id /\
    ~t.vs_halted /\ t.vs_current_bb = st3.cs_current_bb /\
    t.vs_inst_idx = LENGTH st3.cs_current_insts /\ LENGTH ops = LENGTH vals /\
    (!name lb lsz. local_region ce es.scopes t name lb lsz ==>
      regions_disjoint b sz lb lsz) /\
    (!x. not_fresh_at st1 x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < st1.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!i ty op. i < LENGTH vals /\ EL i vals = StackValue ty op ==>
      if EL i flags then eval_operand (EL i ops) t = eval_operand op s
      else ?aid b. st2.cs_next_id <= aid /\ aid < st3.cs_next_id /\
        FLOOKUP t.vs_allocas aid =
          SOME (b, MAX 32 (type_memory_bytes ce (EL i tys))) /\
        eval_operand (EL i ops) t = SOME (n2w b) /\
        b + MAX 32 (type_memory_bytes ce (EL i tys)) < dimword (:256) /\
        (!name lb lsz. local_region ce es.scopes t name lb lsz ==>
          regions_disjoint b (MAX 32 (type_memory_bytes ce (EL i tys))) lb lsz))
Proof
  strip_tac >>
  `ci_mono st1 st2 /\ ci_mono st2 st3` by
    metis_tac[ci_mono_compile_alloc_buffer,
              ci_mono_compile_stage_intcall_args, pairTheory.SND] >>
  `cs_extends st1 st2 /\ cs_extends st2 st3` by gvs[ci_mono_def] >>
  `fn_has_code st1 st2 func /\ fn_has_code st2 st3 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s = OK u` >>
  `u.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `local_ptrs_reserved ce st2` by
    (irule local_ptrs_reserved_next_var >> qexists `st1` >> gvs[ci_mono_def]) >>
  `EVERY (\vv. ?ty op w. vv = StackValue ty op /\ is_word_type ty /\
    (!x. op = Var x ==> not_fresh_at st2 x) /\
    eval_operand op u = SOME w) vals` by
    (qpat_x_assum `EVERY _ vals` mp_tac >> simp[EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     goal_assum drule >> simp[] >> Cases_on `op` >>
     gvs[eval_operand_def, ci_mono_def, not_fresh_at_def] >> metis_tac[]) >>
  drule_all stage_words_seq >> strip_tac >>
  `EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all stage_word_shape >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts st1 st3 = emitted_insts st1 st2 ++ emitted_insts st2 st3` by
    (irule emitted_insts_append >>
     gvs[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `emitted_insts st1 st2 = [mk_inst st1.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString st1.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts st1 st3) s = OK t` by
    metis_tac[run_inst_seq_append] >>
  `st3.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st3` by
    gvs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st1 st3) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts st1 st3) = []` by
    (simp[mk_inst_def, is_terminator_def, FILTER_EQ_NIL, EVERY_MEM] >>
     rpt strip_tac >> gvs[mk_inst_def, is_terminator_def] >>
     qpat_x_assum `EVERY _ (emitted_insts st2 st3)`
       (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `st3.cs_current_bb = st1.cs_current_bb` by metis_tac[] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  qexistsl [`t with vs_inst_idx := LENGTH st3.cs_current_insts`, `w2n w`] >>
  gvs[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def,
      lookup_var_def] >>
  conj_tac >- (gvs[ci_mono_def] >> decide_tac) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> qexists `name` >>
    drule_all (SRULE [lookup_var_def] exprSimCopyTheory.copy_buffer_local_region_frame) >>
    disch_then (qspecl_then [`es.scopes`, `name`, `lb`, `lsz`] mp_tac) >>
    gvs[local_region_def, lookup_var_def]) >>
  conj_tac >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
    qpat_x_assum `!aid b len. aid < st2.cs_next_id /\ _ ==> _` irule >>
    qexists `aid` >> gvs[ci_mono_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!i ty op. i < LENGTH vals /\ _ ==> _` drule >> simp[] >>
  Cases_on `EL i flags` >> simp[]
  >- (gvs[EVERY_MEM] >>
    `?w. eval_operand op s = SOME w /\
      (!x. op = Var x ==> not_fresh_at st1 x)` by
      metis_tac[MEM_EL, contextTheory.vyper_value_11] >>
    Cases_on `op` >> gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  simp[local_region_def, lookup_var_def]
QED
