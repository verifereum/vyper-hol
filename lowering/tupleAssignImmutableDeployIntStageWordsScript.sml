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
