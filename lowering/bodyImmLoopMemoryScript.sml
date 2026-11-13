(* Join the normalized immutable layout to memory-instrumented counted rounds. *)
Theory bodyImmLoopMemory
Ancestors
  bodyImmEntryMemory bodyImmRoundsMemory whitelistForIterImmFrag
  whitelistForIterImmLoop stmtForArrayMemoryRounds stmtSimForArrayLoop
  stmtSimProps stmtSimDefs bodyMemoryDefs loweringStateRelDefs
  exprLoweringProps exprSimProps stmtFragPtr localPtrsProps
  compileEnv context emitHelper emitHelperProps stmtLowering
  venomInst venomState venomExecSemantics fragExec loweringPosts
  vyperInterpreter vyperState words arithmetic list rich_list finite_map
  allocaHistory gasSummary gasOutcome gasContext exprSimCopy stmtLoweringMono
  stmtSimDeclCompose venomMemDefs
Libs
  monadsyntax

Theorem immutable_code_loop_outcome_mem:
  dyn = (case bd of Dynamic _ => T | Fixed _ => F) /\
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
  ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
  ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
  h = st1.cs_next_id + (if dyn then 9 else 6) /\
  nv = STRING #"%" (toString sj.cs_next_var) /\
  toto = Var (STRING #"%" (toString (st1.cs_next_var + (if dyn then 6 else 3)))) /\
  entry = fresh_label_output "iter_entry" st1.cs_next_label /\
  cond = fresh_label_output "iter_cond" (st1.cs_next_label + 1) /\
  bod = fresh_label_output "iter_body" (st1.cs_next_label + 2) /\
  incr = fresh_label_output "iter_incr" (st1.cs_next_label + 3) /\
  exit = fresh_label_output "iter_exit" (st1.cs_next_label + 4) /\
  declare_local cenv id et st1 = (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
  sa.cs_current_bb = bod /\
  sa.cs_current_insts =
    [mk_inst h MUL [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
    (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov]
      [STRING #"%" (toString (st1.cs_next_var + 6))]] else []) ++
    [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit (n2w off); toto] [ep]] /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_id = h + (if dyn then 3 else 2) /\
  sa.cs_next_label = st1.cs_next_label + 5 /\
  compile_iter_elem_copy cenv (Var ep) (Var p)
    (elem_size_in_location cenv LocCode et) LocCode F et et sa = ((),sb0) /\
  same_blocks sa sb0 /\ sb0.cs_current_bb = bod /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
  compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
  emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
  sj.cs_next_var = sb1.cs_next_var /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
  cs_extends st st1 /\ cs_extends st1 sa /\ cs_extends sa sb0 /\
  cs_extends sb0 sb1 /\ cs_extends sb1 sj /\ cs_extends sj st' /\
  fn_has_code st1 sa func /\ fn_has_code sa sb0 func /\
  fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\ fn_has_code sj st' func /\
  lookup_block st1.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      [mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p];
       mk_inst (st1.cs_next_id + 1) JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst (st1.cs_next_id + 2) ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst (st1.cs_next_id + 3) GT [lvo; Lit (n2w (bound_length bd))]
           [STRING #"%" (toString (st1.cs_next_var + 2))];
         mk_inst (st1.cs_next_id + 4) ISZERO
           [Var (STRING #"%" (toString (st1.cs_next_var + 2)))]
           [STRING #"%" (toString (st1.cs_next_var + 3))];
         mk_inst (st1.cs_next_id + 5) ASSERT
           [Var (STRING #"%" (toString (st1.cs_next_var + 3)))] []] else []) ++
      [mk_inst (h - 3) JMP [Label cond] []]|> /\
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
       mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
  st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  local_ptrs_reserved cenv st1 /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs < dimword (:256) /\ copy_old_operand st1 lvo /\
  eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
  (!ei t k. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ k < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei t) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  (!ce srcop dstop bytes ety cs ct tyv cxx cxxctx fn ee ss vv aa bb dd.
    compile_iter_elem_copy ce srcop dstop bytes LocCode F ety ety cs = ((),ct) /\
    bytes = type_memory_size tyv /\ 0 < bytes /\
    evaluate_type (get_tenv cxx) ety = SOME tyv /\
    stmt_state_rel cxxctx fn ce cxx ee ss /\
    immutable_holds ce cxx ety (Value vv) aa ee ss /\
    copy_old_operand cs srcop /\ copy_old_operand cs dstop /\
    eval_operand srcop ss = SOME aa /\ eval_operand dstop ss = SOME bb /\
    w2n bb + bytes <= ss.vs_alloca_next /\ w2n bb + bytes < dimword (:256) /\
    (ce.ce_is_ctor ==> regions_disjoint (w2n aa) bytes (w2n bb) bytes) /\
    (!region. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region ==>
      eval_operand region ss = SOME 0w /\ copy_old_operand cs region) /\
    alloca_history fn ss /\ return_buf_frame dd ce cs ss ==>
    run_inst_seq_mem_ok (emitted_insts cs ct) ss /\
    ?z. copy_runtime_frame cs ss ct z /\
      val_wf tyv vv /\ val_in_memory tyv vv (w2n bb) z.vs_memory /\
      val_footprint tyv vv <= bytes /\
      LENGTH ss.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n bb \/ w2n bb + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len ss.vs_memory) /\
      (z with <|vs_vars := ss.vs_vars; vs_memory := ss.vs_memory|>) = ss /\
      z.vs_alloca_next = ss.vs_alloca_next /\ z.vs_allocas = ss.vs_allocas /\
      alloca_history fn z /\ return_buf_frame dd ce ct z) ==>
  !k es s dst. k <= LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et)
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
      cond st1 u k es s /\
    gas_admissible (eval_for cx tv id stmts (MAP Value (DROP k vs))) ok es ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (eval_for cx tv id stmts (MAP Value (DROP k vs))) (es,s)
      (\res ee t. res = INL () /\ array_round_done d ctx func cenv cx st1 u exit ee t)
      (\res ee rr. ?ex. res = INR ex /\
        !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)
Proof
  strip_tac >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >> simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `tot = STRING #"%" (toString (st1.cs_next_var + 6))` by simp[Abbr `tot`] >>
  drule_all immutable_register_frame >> strip_tac >>
  drule_all immutable_allocation_ready >> strip_tac >>
  `?bc'. stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1)` by
    (qpat_assum `compile_stmts bc _ _ _ sb0 = _` mp_tac >>
     once_rewrite_tac[compile_stmts_env] >>
     Cases_on `stmts_env bc (InLoop exit incr) ty stmts sb0` >> simp[]) >>
  `?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `sb1` >> simp[]) >>
  qabbrev_tac `cut = sa with cs_next_var := st1.cs_next_var + 2` >>
  `st1.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb0.cs_next_var /\
   not_fresh_at cut idx /\ not_fresh_at cut p /\
   (!x. not_fresh_at cut x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep)` by
    (Cases_on `dyn` >> gvs[Abbr `cut`, Abbr `tot`, not_fresh_at_def]) >>
  `!l. lvo <> Label l` by
    (qpat_x_assum `(if dyn then _ else _) st = (lvo,st1)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `dyn` >> simp[comp_return_def, compile_imm_load_word_def] >>
     Cases_on `cenv.ce_is_ctor` >> simp[] >> Cases_on `cenv.ce_imm_alloca` >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `!k ei t. k <= LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et)
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
      cond st1 u k ei t ==>
    eval_operand lvo t = SOME (n2w (LENGTH vs))` by
    (rpt strip_tac >>
     qhdtm_x_assum `array_round_inv` mp_tac >>
     qpat_x_assum `copy_old_operand st1 lvo` mp_tac >>
     qpat_x_assum `eval_operand lvo u = _` mp_tac >>
     qpat_x_assum `!l. lvo <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `lvo` >>
     simp[copy_old_operand_def, eval_operand_def, array_round_inv_def, array_round_frame_def] >>
     metis_tac[]) >>
  suspend "join"
QED
Resume immutable_code_loop_outcome_mem[join]:
  `!k ei live. k < LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et)
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
      bod st1 u k ei live ==>
    ?s_body. s_body.vs_current_bb = sb0.cs_current_bb /\
      s_body.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s_body.vs_halted /\
      stmt_state_rel ctx func bc cx
        (ei with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) s_body /\
      ret_pc_ok bc sb0 s_body /\ gas_marked_path T ctx func live 0 (OK s_body) /\
      s_body.vs_allocas = live.vs_allocas /\ s_body.vs_alloca_next = live.vs_alloca_next /\
      alloca_history func s_body /\ return_buf_frame d bc sb0 s_body /\
      (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
        lookup_var x s_body = lookup_var x live)` by suspend "entry" >>
  `!k ei. k < LENGTH vs /\ P ei /\ lookup_scopes id ei.scopes = NONE ==>
    cenv_top_ext cenv bc ((FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    stmt_frag_mem d ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    (!gs r ee. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,ee) ==>
      stmt_res_ok (InLoop exit incr) r /\
      ?sc rest. ee.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (ee with scopes := rest) /\ lookup_scopes id rest = NONE))` by suspend "callbacks" >>
  `!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv /\
    not_local_ptr cenv scopes dv` by metis_tac[] >>
  `dv <> idx /\ dv <> p /\ p <> idx /\ p <> nv` by
    (qpat_x_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `!x. not_fresh_at st1 x ==> x <> dv /\ x <> idx /\ x <> nv` by
    (qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ ~MEM x _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  `~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func` by simp[] >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all immutable_prepared_loop_outcome_mem >> simp[]
QED
Resume immutable_code_loop_outcome_mem[entry]:
  map_every qx_gen_tac [`j`, `ei`, `live`] >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst (type_memory_bytes cenv et)
    (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
    bod st1 j ei live /\ array_round_frame d func cenv st1 u live` by
    (qpat_x_assum `array_round_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ live` mp_tac >>
     simp[array_round_inv_def]) >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
     (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >> simp[]) >>
  `type_memory_bytes cenv et < dimword (:256)` by decide_tac >>
  `w2n dst + type_memory_bytes cenv et < dimword (:256)` by
    (metis_tac[immutable_entry_allocation_bound]) >>
  qhdtm_assum `array_loop_inv` mp_tac >>
  pure_rewrite_tac[array_loop_inv_def] >> strip_tac >>
  qpat_assum `array_round_frame _ _ _ _ _ live` mp_tac >>
  pure_rewrite_tac[array_round_frame_def] >> strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: ei.scopes)` by
    (irule cenv_top_ext_declare_local >>
     qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  `not_local_ptr bc (FEMPTY :: ei.scopes) p` by
    (irule not_local_ptr_name_update >> qexists_tac `cenv` >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  `not_local_ptr cenv ei.scopes ov /\ not_local_ptr cenv ei.scopes tot /\
   not_local_ptr cenv ei.scopes ep` by metis_tac[] >>
  `immutable_holds cenv cx et (Value (EL j vs))
    (n2w off + n2w ((if dyn then 32 else 0) + j * type_memory_size tv)) ei live` by
    (qpat_assum `!ei t k. _ ==> immutable_holds _ _ _ _ _ _ _` drule_all >> simp[]) >>
  `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by
    (qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ ~MEM x _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  `st1.cs_next_var <= st1.cs_next_var` by simp[] >>
  drule_all immutable_return_pc_ready >> strip_tac >>
  `ret_pc_ok bc sb0 live` by
    (qpat_x_assum `ret_pc_ok cenv st1 live` mp_tac >>
     qpat_x_assum `bc.ce_return_pc = cenv.ce_return_pc` mp_tac >>
     `st1.cs_next_var <= sb0.cs_next_var` by
       (qpat_x_assum `sa.cs_next_var = _` mp_tac >>
        qpat_x_assum `sa.cs_next_var <= sb0.cs_next_var` mp_tac >>
        rpt (pop_assum kall_tac) >> Cases_on `dyn` >> simp[]) >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
     simp[ret_pc_ok_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `return_buf_frame d cenv sa live /\
   (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==>
     x <> ov /\ x <> tot /\ x <> ep)` by
    (qpat_x_assum `return_buf_frame d cenv st1 live` mp_tac >>
     qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `d` >>
     simp[return_buf_frame_def] >> rename1 `SOME pair` >> PairCases_on `pair` >>
     simp[return_buf_frame_def] >> strip_tac >> strip_tac >>
     conj_tac >- metis_tac[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region live = SOME 0w /\ copy_old_operand sa region /\
    (!x. region = Var x ==> x <> ov /\ x <> tot /\ x <> ep)` by
    (qpat_x_assum `stmt_state_rel ctx func cenv cx ei live` mp_tac >>
     qpat_x_assum `local_ptrs_reserved cenv st1` mp_tac >>
     qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, immutable_base_zero_def, local_ptrs_reserved_def,
       copy_old_operand_def] >> metis_tac[]) >>
  `w2n dst + type_memory_bytes cenv et <= live.vs_alloca_next` by
    (qpat_x_assum `stmt_state_rel ctx func cenv cx ei live` mp_tac >>
     qpat_x_assum `FLOOKUP live.vs_allocas _ = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `sa.cs_current_insts =
    [mk_inst h MUL [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
    (if dyn then [mk_inst (h+1) ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst (h + if dyn then 2 else 1) ADD
      [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]` by
    (qpat_x_assum `sa.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `toto = _` mp_tac >> qpat_x_assum `ov = _` mp_tac >>
     qpat_x_assum `tot = STRING _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `dyn` >> simp[]) >>
  `0 < elem_size_in_location cenv LocCode et /\
   elem_size_in_location cenv LocCode et <= type_memory_bytes cenv et /\
   w2n dst + elem_size_in_location cenv LocCode et < dimword (:256) /\
   w2n dst + elem_size_in_location cenv LocCode et <= live.vs_alloca_next` by
    (qpat_x_assum `elem_size_in_location _ _ _ = _` mp_tac >>
     qpat_x_assum `type_memory_bytes _ _ = _` mp_tac >>
     qpat_x_assum `0 < type_memory_size tv` mp_tac >>
     qpat_x_assum `w2n dst + type_memory_bytes cenv et < _` mp_tac >>
     qpat_x_assum `w2n dst + type_memory_bytes cenv et <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `live.vs_current_bb = sb0.cs_current_bb` by metis_tac[] >>
  `immutable_holds cenv cx et (Value (EL j vs))
    (n2w off + n2w ((if dyn then 32 else 0) + j * elem_size_in_location cenv LocCode et)) ei live` by metis_tac[] >>
  `p <> ov /\ p <> ep /\ idx <> ov /\ idx <> ep` by
    (qpat_x_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  drule immutable_array_entry_run_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sa.cs_current_insts = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP live.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `ret_pc_ok bc sb0 live`)) >>
  disch_then (drule_at (Pat `evaluate_type (get_tenv cx) et = SOME tv`)) >>
  disch_then (drule_at (Pat `lookup_var idx live = _`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_scopes id ei.scopes = NONE`)) >>
  disch_then (drule_at (Pat `return_buf_frame d cenv sa live`)) >>
  disch_then (drule_at (Pat `lookup_block sb0.cs_current_bb _ = _`)) >>
  disch_then (drule_all o SRULE []) >>
  strip_tac >> goal_assum (drule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume immutable_code_loop_outcome_mem[callbacks]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule cenv_top_ext_declare_local >>
      qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ei k gs r es2. _` drule_all >> strip_tac >>
  conj_tac >- metis_tac[] >> goal_assum (drule_at Any) >> simp[]
QED
Finalise immutable_code_loop_outcome_mem
