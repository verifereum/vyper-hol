(* Actual repeated execution of one widened-string array loop body. *)
Theory typedCopyArrayExecutionPtr
Ancestors typedCopyLoopLayoutPtr typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr
  typedCopyBytesRobustPtr normalizationPrefixPtr exprSimAggregateEncoding
  valueEncodingProps typedCopyRobustFramePtr fragContinuationPtr
  venomExecSemantics venomInst venomState

Theorem compile_copy_sarray_strings_two_frag_ptr:
  !ce cx ctx PG R sa sb src dst G tn s a b x y.
    compile_copy_sarray_typed ce (Var dst) (BaseT (StringT 33))
      (Var src) (BaseT (StringT 1)) 2 sa = ((),sb) /\
    ~block_is_terminated sa /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
    type_memory_bytes ce (BaseT (StringT 1)) = 64 /\
    type_memory_bytes ce (BaseT (StringT 33)) = 96 /\
    LENGTH x <= 1 /\ LENGTH y <= 1 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s 128 /\ ptr_covers G tn dst s 192 /\
    w2n a + 128 < dimword(:256) /\ w2n b + 192 < dimword(:256) /\
    (w2n a + 128 <= w2n b \/ w2n b + 192 <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV (BaseTV (StringT 1)) (Fixed 2))
        (ArrayV (make_array_value (BaseTV (StringT 1)) (Fixed 2)
          [StringV x; StringV y])) (w2n a) m) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t u. g=G /\ t=tn /\ u=s)
        (\g t u. g=Gf /\ t=tnf /\ u=sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (ArrayTV (BaseTV (StringT 33)) (Fixed 2))
          (ArrayV (make_array_value (BaseTV (StringT 1)) (Fixed 2)
            [StringV x; StringV y])) (w2n b) m) /\
      (!i. ~(w2n b <= i /\ i < w2n b+192) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\ tnf.t_imm=tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
        op_taint tnf (Var p)=op_taint tn (Var p)) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tnf sf)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. i < 2 ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (BaseTV (StringT 1))
        (EL i [StringV x; StringV y]) (w2n a + i*64) m` by
    (qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH [StringV x; StringV y]` by simp[] >>
     drule vyperValueTheory.enumerate_static_array_ALOOKUP >>
     disch_then (qspecl_then [`default_value (BaseTV (StringT 1))`, `0`]
       assume_tac) >>
     qx_gen_tac `m` >> strip_tac >>
     qpat_x_assum `!m. mem_agree_outside _ _ m ==> val_in_memory (ArrayTV _ _) _ _ m`
       (qspec_then `m` mp_tac) >>
     simp[vyperValueTheory.make_array_value_def] >>
     strip_tac >>
     Cases_on `EL i [StringV x; StringV y] = default_value (BaseTV (StringT 1))` >>
     gvs[valueEncodingPropsTheory.val_in_memory_sarray,
         valueEncodingTheory.type_memory_size_def,
         vfmConstantsTheory.word_size_def] >>
     drule_all valueEncodingProofsTheory.kvs_in_memory_lookup >>
     simp[valueEncodingTheory.type_memory_size_def,
          vfmConstantsTheory.word_size_def]) >>
  `~(type_memory_bytes ce (BaseT (StringT 33)) =
       type_memory_bytes ce (BaseT (StringT 1)) /\
       ~is_abi_dynamic ce.ce_struct_fields (BaseT (StringT 33)))` by simp[] >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `compile_store_bytestring (Var sp) (Var dp) si = ((),se)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once contextTheory.compile_store_memory_typed_def,
          compileEnvTheory.is_word_type_def,
          compileEnvTheory.is_bytestring_type_def]) >>
  `not_fresh_at si sp /\ not_fresh_at si dp /\
   not_fresh_at si ctr /\ not_fresh_at si src /\ not_fresh_at si dst` by
    (qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!p. not_fresh_at sa p ==>
     ~MEM p [ctr;lt;done;so;doff;sp;dp]` by
    (qx_gen_tac `p` >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >> strip_tac >>
     simp[] >> rpt conj_tac >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` by
    simp[ASCIInumbersTheory.toString_11] >>
  `si.cs_blocks = sb'.cs_blocks /\ si.cs_current_bb = sb'.cs_current_bb /\
   si.cs_current_insts = sb'.cs_current_insts ++
     [mk_inst sb'.cs_next_id MUL [Var ctr;Lit (n2w 64)] [so];
      mk_inst (sb'.cs_next_id+1) MUL [Var ctr;Lit (n2w 96)] [doff];
      mk_inst (sb'.cs_next_id+2) ADD [Var src;Var so] [sp];
      mk_inst (sb'.cs_next_id+3) ADD [Var dst;Var doff] [dp]]` by
    (qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  qabbrev_tac `sinit = jump_to cond (update_var ctr 0w s)` >>
  qabbrev_tac `ginit = DRESTRICT G (COMPL {ctr})` >>
  qabbrev_tac `tinit = tn with t_var := tn.t_var |+ (ctr,{})` >>
  qabbrev_tac `sh = jump_to body'
    (update_var done 0w (update_var lt 1w sinit))` >>
  qabbrev_tac `gh = DRESTRICT (DRESTRICT ginit (COMPL {lt})) (COMPL {done})` >>
  qabbrev_tac `th = tinit with t_var := (tinit.t_var |+ (lt,{})) |+ (done,{})` >>
  `lookup_var ctr sh = SOME (n2w 0) /\ op_taint th (Var ctr) = {} /\
   lookup_var src sh = SOME a /\ lookup_var dst sh = SOME b /\
   ptr_covers gh th src sh 128 /\ ptr_covers gh th dst sh 192 /\
   ALL_DISTINCT [so;doff;sp;dp] /\
   (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ src <> v /\ dst <> v) /\
   0*64 < 128 /\ 0*64+64 <= 128 /\ 0*96 < 192 /\ 0*96+96 <= 192 /\
   w2n a+0*64 < dimword(:256) /\ w2n b+0*96 < dimword(:256)` by
    suspend "address0_resources" >>
  drule_all typedCopyAmbientFramePtrTheory.typed_copy_loop_address_ambient_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `lookup_var sp u0 = SOME _` >>
  rename1 `ptr_covers ga0 ta0 sp u0 64` >>
  qabbrev_tac `nx = 32 + 32 * ((LENGTH x + 31) DIV 32)` >>
  `nx = 32 + 32 * ((LENGTH x + 31) DIV 32) /\
   LENGTH x + 31 < dimword(:256) /\ nx < dimword(:256) /\
   ptr_covers ga0 ta0 sp u0 nx /\ ptr_covers ga0 ta0 dp u0 nx /\
   is_bytestring_type (BaseT (StringT 1)) /\
   is_bytestring_type (BaseT (StringT 33)) /\
   evaluate_type FEMPTY (BaseT (StringT 1)) = SOME (BaseTV (StringT 1)) /\
   evaluate_type FEMPTY (BaseT (StringT 33)) = SOME (BaseTV (StringT 33)) /\
   value_has_type (BaseTV (StringT 1)) (StringV x) /\
   value_has_type (BaseTV (StringT 33)) (StringV x) /\
   (!m. mem_agree_outside ta0.t_mem u0.vs_memory m ==>
      val_in_memory (BaseTV (StringT 1)) (StringV x)
        (w2n (n2w (w2n a + 0*64):256 word)) m)` by
    suspend "copy0_resources" >>
  Q.SUBGOAL_THEN
    `(?bs. StringV x = BytesV bs /\ LENGTH x = LENGTH bs) \/
     (?str. StringV x = StringV str /\ LENGTH x = LENGTH str)`
    assume_tac >- simp[] >>
  drule_all compile_store_bytestring_robust_ambient_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `frag_exec_ptr cx ctx PG si se
    (\g t v. g = ga0 /\ t = ta0 /\ v = u0)
    (\g t v. g = gc0 /\ t = tc0 /\ v = v0) R` >>
  qabbrev_tac `tmp = STRCAT "%" (toString se.cs_next_var)` >>
  qabbrev_tac `sback1 = jump_to cond
    (update_var ctr (n2w 1) (update_var tmp (n2w 1) v0))` >>
  qabbrev_tac `gback1 = DRESTRICT (DRESTRICT gc0 (COMPL {tmp})) (COMPL {ctr})` >>
  qabbrev_tac `tback1 = tc0 with t_var := (tc0.t_var |+ (tmp,{})) |+ (ctr,{})` >>
  qabbrev_tac `sh1 = jump_to body'
    (update_var done 0w (update_var lt 1w sback1))` >>
  qabbrev_tac `gh1 = DRESTRICT (DRESTRICT gback1 (COMPL {lt})) (COMPL {done})` >>
  qabbrev_tac `th1 = tback1 with t_var := (tback1.t_var |+ (lt,{})) |+ (done,{})` >>
  `lookup_var ctr sh1 = SOME (n2w 1) /\ op_taint th1 (Var ctr) = {} /\
   lookup_var src sh1 = SOME a /\ lookup_var dst sh1 = SOME b /\
   ptr_covers gh1 th1 src sh1 128 /\ ptr_covers gh1 th1 dst sh1 192 /\
   1*64 < 128 /\ 1*64+64 <= 128 /\ 1*96 < 192 /\ 1*96+96 <= 192 /\
   w2n a+1*64 < dimword(:256) /\ w2n b+1*96 < dimword(:256)` by
    suspend "address1_resources" >>
  drule_all typedCopyAmbientFramePtrTheory.typed_copy_loop_address_ambient_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `frag_exec_ptr cx ctx PG sb' si
    (\g t v. g = gh1 /\ t = th1 /\ v = sh1)
    (\g t v. g = ga1 /\ t = ta1 /\ v = u1) R` >>
  qabbrev_tac `ny = 32 + 32 * ((LENGTH y + 31) DIV 32)` >>
  `ny = 32 + 32 * ((LENGTH y + 31) DIV 32) /\
   LENGTH y + 31 < dimword(:256) /\ ny < dimword(:256) /\
   ptr_covers ga1 ta1 sp u1 ny /\ ptr_covers ga1 ta1 dp u1 ny /\
   value_has_type (BaseTV (StringT 1)) (StringV y) /\
   value_has_type (BaseTV (StringT 33)) (StringV y) /\
   (!m. mem_agree_outside ta1.t_mem u1.vs_memory m ==>
      val_in_memory (BaseTV (StringT 1)) (StringV y)
        (w2n (n2w (w2n a + 1*64):256 word)) m)` by
    suspend "copy1_resources" >>
  Q.SUBGOAL_THEN
    `(?bs. StringV y = BytesV bs /\ LENGTH y = LENGTH bs) \/
     (?str. StringV y = StringV str /\ LENGTH y = LENGTH str)`
    assume_tac >- simp[] >>
  drule_all compile_store_bytestring_robust_ambient_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `frag_exec_ptr cx ctx PG si se
    (\g t v. g = ga1 /\ t = ta1 /\ v = u1)
    (\g t v. g = gc1 /\ t = tc1 /\ v = v1) R` >>
  qabbrev_tac `sback2 = jump_to cond
    (update_var ctr (n2w 2) (update_var tmp (n2w 2) v1))` >>
  qabbrev_tac `gback2 = DRESTRICT (DRESTRICT gc1 (COMPL {tmp})) (COMPL {ctr})` >>
  qabbrev_tac `tback2 = tc1 with t_var := (tc1.t_var |+ (tmp,{})) |+ (ctr,{})` >>
  qabbrev_tac `sf = jump_to exit
    (update_var done 1w (update_var lt 0w sback2))` >>
  qabbrev_tac `gf = DRESTRICT (DRESTRICT gback2 (COMPL {lt})) (COMPL {done})` >>
  qabbrev_tac `tf = tback2 with t_var := (tback2.t_var |+ (lt,{})) |+ (done,{})` >>
  qexistsl [`gf`, `tf`, `sf`] >>
  conj_tac >- suspend "continuation" >>
  suspend "final_resources"
QED

Resume compile_copy_sarray_strings_two_frag_ptr[continuation]:
  pure_rewrite_tac[bodyPtrDefsTheory.frag_exec_ptr_def] >>
  rpt gen_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qpat_x_assum `_ = G` SUBST_ALL_TAC >>
  qpat_x_assum `_ = tn` SUBST_ALL_TAC >>
  qpat_x_assum `_ = s` SUBST_ALL_TAC >>
  qabbrev_tac `C = \g t u g' t' v.
    !fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        ghost_run fuel' ctx fn PG g t u = ghost_run fuel ctx fn PG g' t' v /\
        (ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG g' t' v ==>
         ptr_safe_run (cx_dead cx) 0 fuel' ctx fn PG g t u)` >>
  `!g0 t0 u g1 t1 v g2 t2 w.
     C g0 t0 u g1 t1 v /\ C g1 t1 v g2 t2 w ==> C g0 t0 u g2 t2 w` by
    (simp_tac (srw_ss()) [Abbr `C`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `fn_has_code sb' si fn /\ fn_has_code si se fn` by
    suspend "code_containment" >>
  `C G tn s gh th sh /\ ~sh.vs_halted /\
   sh.vs_current_bb = sb'.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sb'.cs_current_insts` by
    suspend "initial_control" >>
  `(~v0.vs_halted /\ v0.vs_current_bb = se.cs_current_bb /\
     v0.vs_inst_idx = LENGTH se.cs_current_insts ==>
       C gc0 tc0 v0 gh1 th1 sh1 /\ ~sh1.vs_halted /\
       sh1.vs_current_bb = sb'.cs_current_bb /\
       sh1.vs_inst_idx = LENGTH sb'.cs_current_insts) /\
   (~v1.vs_halted /\ v1.vs_current_bb = se.cs_current_bb /\
     v1.vs_inst_idx = LENGTH se.cs_current_insts ==>
       C gc1 tc1 v1 gf tf sf /\ ~sf.vs_halted /\
       sf.vs_current_bb = sb.cs_current_bb /\
       sf.vs_inst_idx = LENGTH sb.cs_current_insts)` by
    suspend "later_control" >>
  qpat_x_assum `frag_exec_ptr _ _ _ sb' si (\g t v. g = gh /\ _) _ _`
    mp_tac >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.frag_exec_ptr_def] >>
  disch_then drule_all >>
  reverse strip_tac
  >- (rename1 `exit_result (run_from f0 ctx fn sh)` >>
      `!e. run_from f0 ctx fn sh <> Error e` by
        metis_tac[fragExecTheory.exit_result_not_error] >>
      qpat_x_assum `C G tn s gh th sh` mp_tac >>
      simp_tac (srw_ss()) [Abbr `C`] >>
      disch_then drule_all >> strip_tac >>
      rename1 `run_from f1 ctx fn s = run_from f0 ctx fn sh` >>
      disj2_tac >> qexists_tac `f1` >> asm_rewrite_tac[] >>
      first_x_assum irule >> asm_rewrite_tac[]) >>
  `C gh th sh ga0 ta0 u0` by
    (simp_tac (srw_ss()) [Abbr `C`] >> metis_tac[]) >>
  `C G tn s ga0 ta0 u0` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`gh`, `th`, `sh`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ si se (\g t v. g = ga0 /\ _) _ _`
    mp_tac >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.frag_exec_ptr_def] >>
  disch_then drule_all >>
  reverse strip_tac
  >- (rename1 `exit_result (run_from f0 ctx fn u0)` >>
      `!e. run_from f0 ctx fn u0 <> Error e` by
        metis_tac[fragExecTheory.exit_result_not_error] >>
      qpat_x_assum `C G tn s ga0 ta0 u0` mp_tac >>
      simp_tac (srw_ss()) [Abbr `C`] >>
      disch_then drule_all >> strip_tac >>
      rename1 `run_from f1 ctx fn s = run_from f0 ctx fn u0` >>
      disj2_tac >> qexists_tac `f1` >> asm_rewrite_tac[] >>
      first_x_assum irule >> asm_rewrite_tac[]) >>
  `C ga0 ta0 u0 gc0 tc0 v0` by
    (simp_tac (srw_ss()) [Abbr `C`] >> metis_tac[]) >>
  `C G tn s gc0 tc0 v0` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`ga0`, `ta0`, `u0`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `~v0.vs_halted /\ _ ==> _` drule_all >> strip_tac >>
  `C G tn s gh1 th1 sh1` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`gc0`, `tc0`, `v0`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ sb' si (\g t v. g = gh1 /\ _) _ _`
    mp_tac >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.frag_exec_ptr_def] >>
  disch_then drule_all >>
  reverse strip_tac
  >- (rename1 `exit_result (run_from f0 ctx fn sh1)` >>
      `!e. run_from f0 ctx fn sh1 <> Error e` by
        metis_tac[fragExecTheory.exit_result_not_error] >>
      qpat_x_assum `C G tn s gh1 th1 sh1` mp_tac >>
      simp_tac (srw_ss()) [Abbr `C`] >>
      disch_then drule_all >> strip_tac >>
      rename1 `run_from f1 ctx fn s = run_from f0 ctx fn sh1` >>
      disj2_tac >> qexists_tac `f1` >> asm_rewrite_tac[] >>
      first_x_assum irule >> asm_rewrite_tac[]) >>
  `C gh1 th1 sh1 ga1 ta1 u1` by
    (simp_tac (srw_ss()) [Abbr `C`] >> metis_tac[]) >>
  `C G tn s ga1 ta1 u1` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`gh1`, `th1`, `sh1`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ si se (\g t v. g = ga1 /\ _) _ _`
    mp_tac >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.frag_exec_ptr_def] >>
  disch_then drule_all >>
  reverse strip_tac
  >- (rename1 `exit_result (run_from f0 ctx fn u1)` >>
      `!e. run_from f0 ctx fn u1 <> Error e` by
        metis_tac[fragExecTheory.exit_result_not_error] >>
      qpat_x_assum `C G tn s ga1 ta1 u1` mp_tac >>
      simp_tac (srw_ss()) [Abbr `C`] >>
      disch_then drule_all >> strip_tac >>
      rename1 `run_from f1 ctx fn s = run_from f0 ctx fn u1` >>
      disj2_tac >> qexists_tac `f1` >> asm_rewrite_tac[] >>
      first_x_assum irule >> asm_rewrite_tac[]) >>
  `C ga1 ta1 u1 gc1 tc1 v1` by
    (qpat_x_assum `!fuel. (!e. run_from fuel ctx fn v1 <> Error e) ==> _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `C`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `C G tn s gc1 tc1 v1` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`ga1`, `ta1`, `u1`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `~v1.vs_halted /\ _ ==> _` drule_all >> strip_tac >>
  `C G tn s gf tf sf` by
    (qpat_assum `!g0 t0 u g1 t1 v g2 t2 w. _` irule >>
     qexistsl_tac [`gc1`, `tc1`, `v1`] >> asm_rewrite_tac[]) >>
  disj1_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `C G tn s gf tf sf` mp_tac >>
  simp_tac (srw_ss()) [Abbr `C`]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[address0_resources]:
  `~MEM src [ctr;lt;done;so;doff;sp;dp] /\
   ~MEM dst [ctr;lt;done;so;doff;sp;dp]` by metis_tac[] >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `sc = _` kall_tac >>
  qpat_x_assum `sb' = _` kall_tac >>
  qpat_x_assum `si = _` kall_tac >>
  qpat_x_assum `tail = _` kall_tac >>
  qpat_x_assum `sb = _` kall_tac >>
  qpat_x_assum `cond = _` kall_tac >>
  qpat_x_assum `body' = _` kall_tac >>
  qpat_x_assum `exit = _` kall_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`ctr = _`, `lt = _`, `done = _`, `so = _`, `doff = _`, `sp = _`, `dp = _`] >>
  gvs[Abbr `sh`, Abbr `gh`, Abbr `th`, Abbr `sinit`, Abbr `ginit`, Abbr `tinit`,
      bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
      finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
      ptrDisciplineTheory.op_taint_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[copy0_resources]:
  `nx <= 64 /\ nx <= 96` by
    (qpat_x_assum `LENGTH x <= 1` mp_tac >>
     simp_tac (srw_ss()) [Abbr `nx`] >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `LENGTH x = 0 \/ LENGTH x = 1` by decide_tac >> simp[]) >>
  `ptr_covers ga0 ta0 sp u0 nx` by
    (qpat_x_assum `ptr_covers ga0 ta0 sp u0 64` mp_tac >>
     qpat_x_assum `nx <= 64` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def] >>
     rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  `ptr_covers ga0 ta0 dp u0 nx` by
    (qpat_x_assum `ptr_covers ga0 ta0 dp u0 96` mp_tac >>
     qpat_x_assum `nx <= 64` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def] >>
     rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  conj_tac >- simp_tac (srw_ss()) [Abbr `nx`] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  simp_tac (srw_ss()) [compileEnvTheory.is_bytestring_type_def,
    vyperValueTheory.evaluate_type_def] >>
  simp_tac (srw_ss()) [boolTheory.LET_THM, vfmConstantsTheory.word_size_def,
    vyperValueTheory.type_slot_size_def,
    vyperTypingTheory.value_has_type_def, wordsTheory.dimword_def,
    arithmeticTheory.LESS_MOD] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  qpat_x_assum `!i. i < 2 ==> _` (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `u0.vs_memory = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `ta0.t_mem = _` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [Abbr `sh`, Abbr `th`, Abbr `sinit`, Abbr `tinit`,
    venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
    wordsTheory.w2n_lt, arithmeticTheory.LESS_MOD] >>
  qspec_then `a` mp_tac wordsTheory.w2n_lt >>
  simp_tac (srw_ss()) [wordsTheory.dimword_def] >>
  disch_then (fn th => simp_tac (srw_ss()) [th, arithmeticTheory.LESS_MOD])
QED

Resume compile_copy_sarray_strings_two_frag_ptr[address1_resources]:
  `si.cs_next_var <= se.cs_next_var` by
    (qspec_then `Var sp` (qspec_then `Var dp` (qspec_then `si` mp_tac))
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [exprLoweringPropsTheory.ci_mono_def]) >>
  `!p. not_fresh_at si p ==> p <> tmp` by
    (simp_tac (srw_ss()) [Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >>
     first_x_assum (qspec_then `se.cs_next_var - si.cs_next_var` mp_tac) >>
     `si.cs_next_var + (se.cs_next_var - si.cs_next_var) = se.cs_next_var` by decide_tac >>
     asm_rewrite_tac[]) >>
  `ctr <> tmp /\ src <> tmp /\ dst <> tmp` by metis_tac[] >>
  `~MEM src [ctr;lt;done;so;doff;sp;dp] /\
   ~MEM dst [ctr;lt;done;so;doff;sp;dp]` by metis_tac[] >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sc = _`, `sb' = _`, `si = _`, `tail = _`, `sb = _`,
     `cond = _`, `body' = _`, `exit = _`, `ctr = _`, `lt = _`,
     `done = _`, `so = _`, `doff = _`, `sp = _`, `dp = _`] >>
  `lookup_var src v0 = lookup_var src sh /\
   FLOOKUP gc0 src = FLOOKUP gh src /\
   op_taint tc0 (Var src) = op_taint th (Var src)` by
    (qpat_assum `!p. not_fresh_at si p ==> _` (qspec_then `src` mp_tac) >>
     qpat_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `src` mp_tac) >>
     simp[]) >>
  `lookup_var dst v0 = lookup_var dst sh /\
   FLOOKUP gc0 dst = FLOOKUP gh dst /\
   op_taint tc0 (Var dst) = op_taint th (Var dst)` by
    (qpat_assum `!p. not_fresh_at si p ==> _` (qspec_then `dst` mp_tac) >>
     qpat_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `dst` mp_tac) >>
     simp[]) >>
  `ptr_covers gc0 tc0 src v0 128 /\ ptr_covers gc0 tc0 dst v0 192` by
    (qpat_assum `ptr_covers gh th src sh 128` mp_tac >>
     qpat_assum `ptr_covers gh th dst sh 192` mp_tac >>
     ntac 2 (qpat_x_assum `lookup_var _ v0 = lookup_var _ sh` mp_tac) >>
     ntac 2 (qpat_x_assum `FLOOKUP gc0 _ = FLOOKUP gh _` mp_tac) >>
     ntac 2 (qpat_x_assum `op_taint tc0 (Var _) = op_taint th (Var _)` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[]) >>
  simp_tac (srw_ss()) [Abbr `sh1`, Abbr `gh1`, Abbr `th1`, Abbr `sback1`,
       Abbr `gback1`, Abbr `tback1`] >>
  qpat_assum `ptr_covers gc0 tc0 src v0 128` mp_tac >>
  qpat_assum `ptr_covers gc0 tc0 dst v0 192` mp_tac >>
  ntac 2 (qpat_x_assum `lookup_var _ v0 = lookup_var _ sh` mp_tac) >>
  qpat_assum `lookup_var src sh = SOME a` mp_tac >>
  qpat_assum `lookup_var dst sh = SOME b` mp_tac >>
  qpat_assum `w2n a + 128 < _` mp_tac >>
  qpat_assum `w2n b + 192 < _` mp_tac >>
  ntac 2 (qpat_x_assum `~MEM _ [ctr;lt;done;so;doff;sp;dp]` mp_tac) >>
  qpat_assum `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
  qpat_assum `src <> tmp` mp_tac >>
  qpat_assum `dst <> tmp` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       venomStateTheory.jump_to_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[copy1_resources]:
  `ny <= 64 /\ ny <= 96` by
    (qpat_x_assum `LENGTH y <= 1` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ny`] >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `LENGTH y = 0 \/ LENGTH y = 1` by decide_tac >> simp[]) >>
  `ptr_covers ga1 ta1 sp u1 ny` by
    (qpat_x_assum `ptr_covers ga1 ta1 sp u1 64` mp_tac >>
     qpat_x_assum `ny <= 64` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def] >>
     rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  `ptr_covers ga1 ta1 dp u1 ny` by
    (qpat_x_assum `ptr_covers ga1 ta1 dp u1 96` mp_tac >>
     qpat_x_assum `ny <= 64` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_covers_def] >>
     rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  conj_tac >- simp_tac (srw_ss()) [Abbr `ny`] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- simp[vyperTypingTheory.value_has_type_def] >>
  conj_tac >- simp[vyperTypingTheory.value_has_type_def] >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sc = _`, `sb' = _`, `si = _`, `tail = _`, `sb = _`,
     `cond = _`, `body' = _`, `exit = _`, `ctr = _`, `lt = _`,
     `done = _`, `so = _`, `doff = _`, `sp = _`, `dp = _`] >>
  `nx <= 64` by
    (qpat_x_assum `LENGTH x <= 1` mp_tac >>
     simp_tac (srw_ss()) [Abbr `nx`] >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> `LENGTH x = 0 \/ LENGTH x = 1` by decide_tac >> simp[]) >>
  `w2n (n2w (w2n b + 0*96):256 word) = w2n b` by
    simp[wordsTheory.w2n_lt, arithmeticTheory.LESS_MOD] >>
  `!m. mem_agree_outside ta0.t_mem u0.vs_memory m ==>
       val_in_memory (BaseTV (StringT 1)) (StringV y) (w2n a + 64) m` by
    (qpat_x_assum `!i. i < 2 ==> _` (qspec_then `1` mp_tac) >>
     simp_tac (srw_ss()) [] >>
     qpat_assum `u0.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `ta0.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [Abbr `sh`, Abbr `th`, Abbr `sinit`, Abbr `tinit`,
       venomStateTheory.jump_to_def, venomStateTheory.update_var_def]) >>
  `val_wf (BaseTV (StringT 1)) (StringV y)` by
    simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def,
         vfmConstantsTheory.word_size_def] >>
  Q.SUBGOAL_THEN
   `w2n a + 64 + type_memory_size (BaseTV (StringT 1)) <= w2n b \/
    w2n b + nx <= w2n a + 64` assume_tac >-
    (simp_tac (srw_ss()) [valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tc0.t_mem v0.vs_memory m ==>
       val_in_memory (BaseTV (StringT 1)) (StringV y) (w2n a + 64) m` by
    (qpat_assum `!ft fv p. _` (qspecl_then
       [`BaseTV (StringT 1)`, `StringV y`, `w2n a + 64`] match_mp_tac) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >-
       (qpat_x_assum `_ \/ w2n b + nx <= w2n a + 64` mp_tac >>
        qpat_assum `w2n (n2w (w2n b + 0*96):256 word) = w2n b`
          (fn th => rewrite_tac[th]) >>
        simp_tac (srw_ss()) []) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `w2n (n2w (w2n a + 1*64):256 word) = w2n a + 64` by
    (simp_tac (srw_ss()) [arithmeticTheory.LESS_MOD] >> decide_tac) >>
  qpat_assum `!m. mem_agree_outside tc0.t_mem v0.vs_memory m ==> _` mp_tac >>
  qpat_assum `u1.vs_memory = sh1.vs_memory` (fn th => rewrite_tac[th]) >>
  qpat_assum `ta1.t_mem = th1.t_mem` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [Abbr `sh1`, Abbr `th1`, Abbr `sback1`, Abbr `tback1`,
    venomStateTheory.jump_to_def, venomStateTheory.update_var_def] >>
  `w2n a + 64 < dimword(:256)` by decide_tac >>
  qpat_assum `w2n a + 64 < dimword(:256)`
    (fn th => simp_tac (srw_ss()) [th, arithmeticTheory.LESS_MOD])
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_resources]:
  conj_tac >- suspend "final_representation" >>
  conj_tac >- suspend "final_exterior" >>
  conj_tac >- suspend "final_storage_taint" >>
  conj_tac >- suspend "final_transient_taint" >>
  conj_tac >- suspend "final_immutable_taint" >>
  conj_tac >- suspend "final_old_names" >>
  suspend "final_stor_ok"
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_representation]:
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sc = _`, `sb' = _`, `si = _`, `tail = _`, `sb = _`,
     `cond = _`, `body' = _`, `exit = _`, `ctr = _`, `lt = _`,
     `done = _`, `so = _`, `doff = _`, `sp = _`, `dp = _`] >>
  `!m. mem_agree_outside ta1.t_mem u1.vs_memory m ==>
       val_in_memory (BaseTV (StringT 33)) (StringV x) (w2n b) m` by
    (qpat_assum `!m. mem_agree_outside tc0.t_mem v0.vs_memory m ==> _` mp_tac >>
     qpat_assum `u1.vs_memory = sh1.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `ta1.t_mem = th1.t_mem` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [Abbr `sh1`, Abbr `th1`, Abbr `sback1`, Abbr `tback1`,
       venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
       wordsTheory.w2n_lt, arithmeticTheory.LESS_MOD]) >>
  `w2n (n2w (w2n b + 1*96):256 word) = w2n b + 96` by
    (simp_tac (srw_ss()) [arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `!m. mem_agree_outside tc1.t_mem v1.vs_memory m ==>
       val_in_memory (BaseTV (StringT 33)) (StringV x) (w2n b) m` by
    (qpat_assum `!ft fv p. _ ==> !m. mem_agree_outside tc1.t_mem _ m ==> _`
       (qspecl_then [`BaseTV (StringT 33)`, `StringV x`, `w2n b`] match_mp_tac) >>
     conj_tac >- simp[valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def] >>
     conj_tac >-
       (qpat_assum `w2n (n2w (w2n b + 1*96):256 word) = w2n b + 96`
          (fn th => rewrite_tac[th]) >>
        simp_tac (srw_ss()) [valueEncodingTheory.type_memory_size_def,
          vfmConstantsTheory.word_size_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `!m. mem_agree_outside tc1.t_mem v1.vs_memory m ==>
       val_in_memory (BaseTV (StringT 33)) (StringV y) (w2n b + 96) m` by
    (qpat_assum `!m. mem_agree_outside tc1.t_mem v1.vs_memory m ==>
       val_in_memory _ _ (w2n (n2w _)) m` mp_tac >>
     `w2n b + 96 < dimword(:256)` by decide_tac >>
     qpat_assum `w2n b + 96 < dimword(:256)`
       (fn th => simp_tac (srw_ss()) [th, arithmeticTheory.LESS_MOD])) >>
  simp_tac (srw_ss()) [Abbr `sf`, Abbr `tf`, Abbr `sback2`, Abbr `tback2`,
    venomStateTheory.jump_to_def, venomStateTheory.update_var_def] >>
  ntac 2 (qpat_x_assum `!m. mem_agree_outside tc1.t_mem v1.vs_memory m ==> _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [vyperValueTheory.make_array_value_def,
     valueEncodingPropsTheory.val_in_memory_sarray] >>
  rpt strip_tac >>
  Cases_on `x = ""` >> Cases_on `y = ""` >>
  gvs[vyperValueTheory.enumerate_static_array_def,
      vyperValueTheory.default_value_def, valueEncodingDefsTheory.val_in_memory_def,
      valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  rpt strip_tac >> gvs[] >>
  `i = 0 \/ i = 1` by decide_tac >> gvs[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_storage_taint]:
  simp[Abbr `tf`, Abbr `tback2`, Abbr `th1`, Abbr `tback1`,
       Abbr `th`, Abbr `tinit`]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_transient_taint]:
  simp[Abbr `tf`, Abbr `tback2`, Abbr `th1`, Abbr `tback1`,
       Abbr `th`, Abbr `tinit`]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_immutable_taint]:
  simp[Abbr `tf`, Abbr `tback2`, Abbr `th1`, Abbr `tback1`,
       Abbr `th`, Abbr `tinit`]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_exterior]:
  qx_gen_tac `i` >> strip_tac >>
  `nx <= 64 /\ ny <= 64` by
    (qpat_assum `LENGTH x <= 1` mp_tac >>
     qpat_assum `LENGTH y <= 1` mp_tac >>
     simp_tac (srw_ss()) [Abbr `nx`, Abbr `ny`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `LENGTH x = 0 \/ LENGTH x = 1` by decide_tac >>
     `LENGTH y = 0 \/ LENGTH y = 1` by decide_tac >> simp[]) >>
  `w2n (n2w (w2n b + 0*96):256 word) = w2n b /\
   w2n (n2w (w2n b + 1*96):256 word) = w2n b + 96` by
    (simp_tac (srw_ss()) [arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `~(w2n (n2w (w2n b + 0*96):256 word) <= i /\
      i < w2n (n2w (w2n b + 0*96):256 word) + nx) /\
   ~(w2n (n2w (w2n b + 1*96):256 word) <= i /\
      i < w2n (n2w (w2n b + 1*96):256 word) + ny)` by
    (asm_rewrite_tac[] >> decide_tac) >>
  qpat_assum `!i. _ ==> mem_bytes_at i 1 v0.vs_memory = _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!i. _ ==> mem_bytes_at i 1 v1.vs_memory = _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!i. _ ==> (i IN tc0.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> disch_tac >>
  qpat_assum `!i. _ ==> (i IN tc1.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> disch_tac >>
  qpat_x_assum `mem_bytes_at i 1 v0.vs_memory = _` mp_tac >>
  qpat_x_assum `mem_bytes_at i 1 v1.vs_memory = _` mp_tac >>
  qpat_x_assum `i IN tc0.t_mem <=> _` mp_tac >>
  qpat_x_assum `i IN tc1.t_mem <=> _` mp_tac >>
  qpat_assum `u0.vs_memory = sh.vs_memory` mp_tac >>
  qpat_assum `u1.vs_memory = sh1.vs_memory` mp_tac >>
  qpat_assum `ta0.t_mem = th.t_mem` mp_tac >>
  qpat_assum `ta1.t_mem = th1.t_mem` mp_tac >>
  simp_tac (srw_ss()) [Abbr `sf`, Abbr `tf`, Abbr `sback2`, Abbr `tback2`,
       Abbr `sh1`, Abbr `th1`, Abbr `sback1`, Abbr `tback1`,
       Abbr `sh`, Abbr `th`, Abbr `sinit`, Abbr `tinit`,
       venomStateTheory.jump_to_def, venomStateTheory.update_var_def] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_old_names]:
  qx_gen_tac `p` >> strip_tac >>
  `sa.cs_next_var <= si.cs_next_var` by
    (qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `not_fresh_at si p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `si.cs_next_var <= se.cs_next_var` by
    (qspec_then `Var sp` (qspec_then `Var dp` (qspec_then `si` mp_tac))
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [exprLoweringPropsTheory.ci_mono_def]) >>
  `!q. not_fresh_at si q ==> q <> tmp` by
    (simp_tac (srw_ss()) [Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >>
     first_x_assum (qspec_then `se.cs_next_var - si.cs_next_var` mp_tac) >>
     `si.cs_next_var + (se.cs_next_var - si.cs_next_var) = se.cs_next_var` by decide_tac >>
     asm_rewrite_tac[]) >>
  `p <> tmp` by metis_tac[] >>
  `~MEM p [ctr;lt;done;so;doff;sp;dp]` by metis_tac[] >>
  ntac 2 (qpat_x_assum `!p. not_fresh_at si p ==> lookup_var p _ = _ /\ _`
    (qspec_then `p` mp_tac)) >>
  ntac 2 (qpat_x_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `p` mp_tac)) >>
  simp_tac (srw_ss()) [] >>
  `~MEM p [so;doff;sp;dp]` by
    (qpat_assum `~MEM p [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_assum `not_fresh_at si p` mp_tac >>
  qpat_assum `~MEM p [so;doff;sp;dp]` mp_tac >>
  qpat_x_assum `~MEM p [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
  qpat_assum `p <> tmp` mp_tac >>
  simp_tac (srw_ss()) [Abbr `sf`, Abbr `gf`, Abbr `tf`,
    Abbr `sback2`, Abbr `gback2`, Abbr `tback2`,
    Abbr `sh1`, Abbr `gh1`, Abbr `th1`, Abbr `sback1`, Abbr `gback1`, Abbr `tback1`,
    Abbr `sh`, Abbr `gh`, Abbr `th`, Abbr `sinit`, Abbr `ginit`, Abbr `tinit`] >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [venomStateTheory.lookup_var_def,
    venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
    ptrDisciplineTheory.op_taint_def] >> rpt strip_tac >> gvs[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[final_stor_ok]:
  rpt (qpat_x_assum `_.vs_call_ctx = _` mp_tac) >>
  rpt (qpat_x_assum `_.vs_accounts = _` mp_tac) >>
  rpt (qpat_x_assum `_.vs_transient = _` mp_tac) >>
  rpt (qpat_x_assum `_.t_stor = _` mp_tac) >>
  rpt (qpat_x_assum `_.t_trans = _` mp_tac) >>
  rpt (qpat_x_assum `_.t_imm = _` mp_tac) >>
  simp_tac (srw_ss()) [Abbr `sf`, Abbr `tf`, Abbr `sback2`, Abbr `tback2`,
    Abbr `sh1`, Abbr `th1`, Abbr `sback1`, Abbr `tback1`,
    Abbr `sh`, Abbr `th`, Abbr `sinit`, Abbr `tinit`,
    venomStateTheory.jump_to_def, venomStateTheory.update_var_def] >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.stor_taint_ok_def] >>
  rpt strip_tac >> gvs[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[code_containment]:
  `cs_extends sa sb'` by
    (simp_tac (srw_ss()) [compileEnvTheory.cs_extends_def] >>
     qexists `TAKE 2 sb'.cs_blocks` >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `cs_extends sb' si` by
    (simp_tac (srw_ss()) [compileEnvTheory.cs_extends_def] >> qexists `[]` >>
     qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `cs_extends si se` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `BaseT (StringT 33)`,
       `Var sp`, `BaseT (StringT 1)`, `si`] mp_tac) >>
     asm_rewrite_tac[] >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends se sb` by
    (simp_tac (srw_ss()) [compileEnvTheory.cs_extends_def] >>
     qexists `[HD sb.cs_blocks]` >>
     qpat_assum `sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tail = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `cs_extends si sb` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `se` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends sb' sb` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `si` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code sb' sb fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code si sb fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[initial_control]:
  qabbrev_tac `entry = HD (TL si.cs_blocks)` >>
  qabbrev_tac `test = HD si.cs_blocks` >>
  qabbrev_tac `back = HD sb.cs_blocks` >>
  `si.cs_blocks = test :: entry :: sa.cs_blocks /\
   entry.bb_label = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts entry.bb_instructions` by
    (simp_tac (srw_ss()) [Abbr `entry`, Abbr `test`] >>
     qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `sb.cs_blocks = back :: se.cs_blocks /\
   back.bb_label = se.cs_current_bb /\
   isPREFIX se.cs_current_insts back.bb_instructions` by
    (simp_tac (srw_ss()) [Abbr `back`] >>
     qpat_assum `sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tail = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule_all typed_copy_loop_slice_locations >> strip_tac >>
  `entry.bb_instructions = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
     mk_inst (sa.cs_next_id+1) JMP [Label cond] []] /\
   test.bb_label = cond /\
   test.bb_instructions =
    [mk_inst sc.cs_next_id LT [Var ctr;Lit 2w] [lt];
     mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
     mk_inst (sc.cs_next_id+2) JNZ [Var done;Label exit;Label body'] []]` by
    (simp_tac (srw_ss()) [Abbr `entry`, Abbr `test`] >>
     qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  reverse conj_tac
  >- (simp_tac (srw_ss()) [Abbr `sh`, Abbr `sinit`, jump_to_def,
         update_var_def] >>
      qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME entry` by
    metis_tac[] >>
  `!fuel. run_from (SUC fuel) ctx fn s =
     run_blocks (SUC fuel) ctx fn sinit` by
    (qpat_assum `lookup_block s.vs_current_bb _ = _` mp_tac >>
     qpat_assum `entry.bb_instructions = _` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sinit`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[fragExecTheory.run_from_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def] >>
     simp[Once exec_block_def, get_instruction_def, update_var_def,
       step_inst_non_invoke, is_terminator_def, listTheory.EL_APPEND_EQN,
       arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, jump_to_def]) >>
  `lookup_block sinit.vs_current_bb fn.fn_blocks = SOME test /\
   sinit.vs_inst_idx = 0 /\ ~sinit.vs_halted /\
   lookup_var ctr sinit = SOME (n2w 0) /\ ctr <> lt /\ ctr <> done /\
   phi_prefix_length test.bb_instructions = 0` by
    (simp_tac (srw_ss()) [Abbr `sinit`, jump_to_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt conj_tac
     >- metis_tac[]
     >- asm_rewrite_tac[]
     >- (qpat_x_assum `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[])
     >- (qpat_x_assum `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[])
     >> qpat_assum `test.bb_instructions = _` (fn th => rewrite_tac[th]) >>
        simp[phi_prefix_length_def, mk_inst_def]) >>
  `!fuel. run_from (SUC fuel) ctx fn sinit =
     run_blocks (SUC fuel) ctx fn sh` by
    (simp_tac (srw_ss()) [Abbr `sh`] >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `0`, `n` |-> `2`] (SPEC_ALL typed_copy_loop_test_run))) >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `?target. lookup_block body' fn.fn_blocks = SOME target /\
     phi_prefix_length target.bb_instructions = 0` by
    (qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fn_has_code sa sb fn` mp_tac >>
     qpat_assum `~(type_memory_bytes _ _ = _ /\ _)` mp_tac >>
     qpat_assum `body' = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all compile_copy_sarray_typed_loop_no_phi >> metis_tac[]) >>
  `!fuel. ghost_run (SUC fuel) ctx fn PG ginit tinit sinit =
     ghost_run fuel ctx fn PG gh th sh` by
    (simp_tac (srw_ss()) [Abbr `gh`, Abbr `th`, Abbr `sh`] >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `0`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_test_ghost_run))) >>
     disch_then (qspecl_then [`tinit`, `ctx`, `PG`, `ginit`] ACCEPT_TAC)) >>
  `op_taint tinit (Var ctr) = {}` by
    simp[Abbr `tinit`, ptrDisciplineTheory.op_taint_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  `!fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG gh th sh ==>
     ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG ginit tinit sinit` by
    (simp_tac (srw_ss()) [Abbr `gh`, Abbr `th`, Abbr `sh`] >>
     rpt strip_tac >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `0`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_test_ptr_safe))) >>
     simp[]) >>
  `step_prov PG G (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr])
       (update_var ctr 0w s) = ginit /\
   step_taint (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) s
       (update_var ctr 0w s) tn = tinit` by
    (simp_tac (srw_ss()) [Abbr `ginit`, Abbr `tinit`] >>
     POP_ASSUM_LIST (K all_tac) >>
     `new_site_bytes s (update_var ctr 0w s) = {}` by
       simp[ptrDisciplineTheory.new_site_bytes_def, update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
     simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
       ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.step_taint_def,
       ptrDisciplineTheory.set_var_taint_def, mk_inst_def,
       ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.store_taint_def,
       ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.out_taint_def,
       ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.imm_taint_def,
       ptrDisciplineTheory.range_bytes_def,
       ptrDisciplineTheory.taint_component_equality, eval_operand_def]) >>
  `!fuel. ghost_run (SUC fuel) ctx fn PG G tn s =
     ghost_run fuel ctx fn PG ginit tinit sinit` by
    (qpat_assum `step_prov PG G _ _ = ginit` mp_tac >>
     qpat_assum `step_taint _ s _ tn = tinit` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb _ = _` mp_tac >>
     qpat_assum `entry.bb_instructions = _` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     `lookup_block cond fn.fn_blocks = SOME test` by metis_tac[] >>
     pop_assum mp_tac >>
     qpat_assum `phi_prefix_length test.bb_instructions = 0` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sinit`, mk_inst_def] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[ptrSafeRunTheory.ghost_run_def,
       Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, is_terminator_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
     simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       update_var_def, step_inst_non_invoke, listTheory.EL_APPEND_EQN,
       arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, is_terminator_def, jump_to_def] >>
     qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
     qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
     `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
       (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
        simp[Abbr `sj`] >> metis_tac[]) >>
     simp[Once ptrSafeRunTheory.ghost_blocks_def, Abbr `sj`,
       GSYM arithmeticTheory.ADD1] >>
     Cases_on `test.bb_instructions`
     >- simp[eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[phi_prefix_length_def, eval_phis_def]) >>
  `!fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG ginit tinit sinit ==>
     ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG G tn s` by
    (qpat_assum `step_prov PG G _ _ = ginit` mp_tac >>
     qpat_assum `step_taint _ s _ tn = tinit` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb _ = _` mp_tac >>
     qpat_assum `entry.bb_instructions = _` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     `lookup_block cond fn.fn_blocks = SOME test` by metis_tac[] >>
     pop_assum mp_tac >>
     qpat_assum `phi_prefix_length test.bb_instructions = 0` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sinit`, mk_inst_def] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[ptrSafeRunTheory.ptr_safe_run_def,
       Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def, step_inst_non_invoke,
       listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, is_terminator_def] >>
     conj_tac
     >- (simp[ptrSafeRunTheory.ptr_inst_ok_def,
           ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
           ptrDisciplineTheory.allocas_from_def,
           codegenRelTheory.source_memory_write_ranges_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           ptrDisciplineTheory.op_taint_def] >>
         simp[step_inst_non_invoke, step_inst_base_def,
           eval_operand_def, update_var_def]) >>
     simp[ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke,
       step_inst_base_def, eval_operand_def] >>
     simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def, update_var_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, is_terminator_def, jump_to_def] >>
     conj_tac
     >- (simp[ptrSafeRunTheory.ptr_inst_ok_def,
           ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
           ptrDisciplineTheory.allocas_from_def,
           codegenRelTheory.source_memory_write_ranges_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           ptrDisciplineTheory.op_taint_def] >>
         simp[step_inst_non_invoke, step_inst_base_def,
           eval_operand_def, jump_to_def]) >>
     qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
     qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
     `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
       (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
        simp[Abbr `sj`] >> metis_tac[]) >>
     simp[Once ptrSafeRunTheory.ptr_safe_blocks_def, Abbr `sj`,
       GSYM arithmeticTheory.ADD1] >>
     qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptrSafeRunTheory.ptr_safe_run_def, GSYM arithmeticTheory.ADD1,
       update_var_def, jump_to_def] >>
     Cases_on `test.bb_instructions`
     >- simp[eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[phi_prefix_length_def, eval_phis_def]) >>
  `!fuel. run_blocks (SUC fuel) ctx fn sinit =
      run_from fuel ctx fn sinit` by
    (rpt gen_tac >> drule_all fragExecTheory.run_blocks_run_from_no_phi >> simp[]) >>
  `!fuel. run_blocks (SUC fuel) ctx fn sh =
      run_from fuel ctx fn sh` by
    (rpt gen_tac >> irule EQ_TRANS >>
     irule_at Any fragExecTheory.run_blocks_run_from_no_phi >>
     simp_tac (srw_ss()) [Abbr `sh`, jump_to_def, update_var_def] >>
     metis_tac[]) >>
  qpat_assum `!fuel. run_from (SUC fuel) ctx fn s = _` mp_tac >>
  qpat_assum `!fuel. run_from (SUC fuel) ctx fn sinit = _` mp_tac >>
  qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG G tn s = _` mp_tac >>
  qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG ginit tinit sinit = _` mp_tac >>
  qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ ginit tinit sinit ==> _` mp_tac >>
  qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ gh th sh ==> _` mp_tac >>
  qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sinit = _` mp_tac >>
  qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sh = _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `C`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qexists_tac `SUC (SUC fuel)` >> simp[]
QED

Resume compile_copy_sarray_strings_two_frag_ptr[later_control]:
  qabbrev_tac `entry = HD (TL si.cs_blocks)` >>
  qabbrev_tac `test = HD si.cs_blocks` >>
  qabbrev_tac `back = HD sb.cs_blocks` >>
  `si.cs_blocks = test :: entry :: sa.cs_blocks /\
   entry.bb_label = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts entry.bb_instructions` by
    (simp_tac (srw_ss()) [Abbr `entry`, Abbr `test`] >>
     qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `sb.cs_blocks = back :: se.cs_blocks /\
   back.bb_label = se.cs_current_bb /\
   isPREFIX se.cs_current_insts back.bb_instructions` by
    (simp_tac (srw_ss()) [Abbr `back`] >>
     qpat_assum `sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tail = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule_all typed_copy_loop_slice_locations >> strip_tac >>
  `back.bb_instructions = se.cs_current_insts ++
    [mk_inst se.cs_next_id ADD [Var ctr;Lit 1w] [tmp];
     mk_inst (se.cs_next_id+1) ASSIGN [Var tmp] [ctr];
     mk_inst (se.cs_next_id+2) JMP [Label cond] []] /\
   test.bb_label = cond /\
   test.bb_instructions =
    [mk_inst sc.cs_next_id LT [Var ctr;Lit 2w] [lt];
     mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
     mk_inst (sc.cs_next_id+2) JNZ [Var done;Label exit;Label body'] []]` by
    (simp_tac (srw_ss()) [Abbr `back`, Abbr `test`] >>
     qpat_assum `sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tail = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `si.cs_next_var <= se.cs_next_var` by
    (qspec_then `Var sp` (qspec_then `Var dp` (qspec_then `si` mp_tac))
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [exprLoweringPropsTheory.ci_mono_def]) >>
  `!p. not_fresh_at si p ==> p <> tmp` by
    (simp_tac (srw_ss()) [Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >>
     first_x_assum (qspec_then `se.cs_next_var - si.cs_next_var` mp_tac) >>
     `si.cs_next_var + (se.cs_next_var - si.cs_next_var) = se.cs_next_var` by decide_tac >>
     asm_rewrite_tac[]) >>
  `ctr <> tmp /\ ctr <> lt /\ ctr <> done /\ ~MEM ctr [so;doff;sp;dp]` by
    (qpat_assum `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` mp_tac >>
     qpat_assum `!p. not_fresh_at si p ==> p <> tmp` mp_tac >>
     qpat_assum `not_fresh_at si ctr` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  `lookup_var ctr v0 = SOME (n2w 0) /\ FLOOKUP gc0 ctr = NONE /\
   op_taint tc0 (Var ctr) = {}` by
    (qpat_assum `!p. not_fresh_at si p ==> _` (qspec_then `ctr` mp_tac) >>
     qpat_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `ctr` mp_tac) >>
     simp[Abbr `gh`, Abbr `ginit`, finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `lookup_var ctr v1 = SOME (n2w 1) /\ FLOOKUP gc1 ctr = NONE /\
   op_taint tc1 (Var ctr) = {}` by
    (qpat_assum `!p. not_fresh_at si p ==> _` (qspec_then `ctr` mp_tac) >>
     qpat_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `ctr` mp_tac) >>
     simp[Abbr `gh1`, Abbr `gback1`, finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `lookup_block cond fn.fn_blocks = SOME test /\
   phi_prefix_length test.bb_instructions = 0` by
    (conj_tac >- metis_tac[] >>
     qpat_assum `test.bb_instructions = _` (fn th => rewrite_tac[th]) >>
     simp[phi_prefix_length_def, mk_inst_def]) >>
  `?target. lookup_block body' fn.fn_blocks = SOME target /\
     phi_prefix_length target.bb_instructions = 0` by
    (qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fn_has_code sa sb fn` mp_tac >>
     qpat_assum `~(type_memory_bytes _ _ = _ /\ _)` mp_tac >>
     qpat_assum `body' = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all compile_copy_sarray_typed_loop_no_phi >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >>
      reverse conj_tac
      >- (simp_tac (srw_ss()) [Abbr `sh1`, Abbr `sback1`, jump_to_def,
            update_var_def] >>
          qpat_assum `sb' = _` (fn th => rewrite_tac[th]) >> simp[]) >>
      `lookup_block v0.vs_current_bb fn.fn_blocks = SOME back` by metis_tac[] >>
      `!fuel. run_from (SUC fuel) ctx fn v0 =
         run_blocks (SUC fuel) ctx fn sback1` by
        (simp_tac (srw_ss()) [Abbr `sback1`] >>
         irule (SRULE [wordsTheory.dimword_def]
           (Q.INST [`i` |-> `0`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_backedge_run))) >>
         simp[] >> metis_tac[]) >>
      `lookup_block sback1.vs_current_bb fn.fn_blocks = SOME test /\
       sback1.vs_inst_idx = 0 /\ ~sback1.vs_halted /\
       lookup_var ctr sback1 = SOME (n2w 1)` by
        (simp_tac (srw_ss()) [Abbr `sback1`, jump_to_def, update_var_def,
           lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
      `!fuel. ghost_run (SUC fuel) ctx fn PG gc0 tc0 v0 =
         ghost_run fuel ctx fn PG gback1 tback1 sback1` by
        (simp_tac (srw_ss()) [Abbr `sback1`, Abbr `gback1`, Abbr `tback1`] >>
         irule (SRULE [wordsTheory.dimword_def]
           (Q.INST [`i` |-> `0`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_backedge_ghost_run))) >>
         simp[] >> metis_tac[]) >>
      `!fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG gback1 tback1 sback1 ==>
         ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG gc0 tc0 v0` by
        (qpat_assum `lookup_block v0.vs_current_bb _ = SOME back` mp_tac >>
         qpat_assum `back.bb_instructions = _` mp_tac >>
         qpat_assum `v0.vs_inst_idx = _` mp_tac >>
         qpat_assum `~v0.vs_halted` mp_tac >>
         qpat_assum `lookup_var ctr v0 = _` mp_tac >>
         qpat_assum `FLOOKUP gc0 ctr = NONE` mp_tac >>
         qpat_assum `op_taint tc0 (Var ctr) = {}` mp_tac >>
         qpat_assum `ctr <> tmp` mp_tac >>
         qpat_assum `lookup_block cond _ = SOME test` mp_tac >>
         qpat_assum `phi_prefix_length test.bb_instructions = 0` mp_tac >>
         qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
         simp_tac (srw_ss()) [Abbr `sback1`, Abbr `gback1`, Abbr `tback1`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         irule (SRULE [wordsTheory.dimword_def]
           (Q.INST [`i` |-> `0`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_backedge_ptr_safe))) >>
         simp_tac (srw_ss()) [] >> metis_tac[]) >>
      `!fuel. run_from (SUC fuel) ctx fn sback1 =
         run_blocks (SUC fuel) ctx fn sh1` by
        (simp_tac (srw_ss()) [Abbr `sh1`] >>
         drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
           (Q.INST [`i` |-> `1`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_test_run))) >>
         disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
      `!fuel. ghost_run (SUC fuel) ctx fn PG gback1 tback1 sback1 =
         ghost_run fuel ctx fn PG gh1 th1 sh1` by
        (simp_tac (srw_ss()) [Abbr `gh1`, Abbr `th1`, Abbr `sh1`] >>
         drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
           (Q.INST [`i` |-> `1`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_test_ghost_run))) >>
         disch_then (qspecl_then [`tback1`, `ctx`, `PG`, `gback1`] ACCEPT_TAC)) >>
      `op_taint tback1 (Var ctr) = {}` by
        simp[Abbr `tback1`, ptrDisciplineTheory.op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
      `!fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG gh1 th1 sh1 ==>
         ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG gback1 tback1 sback1` by
        (simp_tac (srw_ss()) [Abbr `gh1`, Abbr `th1`, Abbr `sh1`] >>
         rpt strip_tac >>
         drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
           (Q.INST [`i` |-> `1`, `n` |-> `2`]
             (SPEC_ALL typed_copy_loop_test_ptr_safe))) >> simp[]) >>
      `!fuel. run_blocks (SUC fuel) ctx fn sback1 =
          run_from fuel ctx fn sback1` by
        (rpt gen_tac >> drule_all fragExecTheory.run_blocks_run_from_no_phi >> simp[]) >>
      `!fuel. run_blocks (SUC fuel) ctx fn sh1 =
          run_from fuel ctx fn sh1` by
        (rpt gen_tac >> irule EQ_TRANS >>
         irule_at Any fragExecTheory.run_blocks_run_from_no_phi >>
         simp_tac (srw_ss()) [Abbr `sh1`, jump_to_def, update_var_def] >>
         metis_tac[]) >>
      qpat_assum `!fuel. run_from (SUC fuel) ctx fn v0 = _` mp_tac >>
      qpat_assum `!fuel. run_from (SUC fuel) ctx fn sback1 = _` mp_tac >>
      qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG gc0 tc0 v0 = _` mp_tac >>
      qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG gback1 tback1 sback1 = _` mp_tac >>
      qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ gback1 tback1 sback1 ==> _` mp_tac >>
      qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ gh1 th1 sh1 ==> _` mp_tac >>
      qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sback1 = _` mp_tac >>
      qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sh1 = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `C`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      qexists_tac `SUC (SUC fuel)` >> simp[]) >>
  strip_tac >>
  reverse conj_tac
  >- (simp_tac (srw_ss()) [Abbr `sf`, Abbr `sback2`, jump_to_def,
        update_var_def] >>
      qpat_assum `sb = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `lookup_block v1.vs_current_bb fn.fn_blocks = SOME back` by metis_tac[] >>
  `!fuel. run_from (SUC fuel) ctx fn v1 =
     run_blocks (SUC fuel) ctx fn sback2` by
    (simp_tac (srw_ss()) [Abbr `sback2`] >>
     irule (SRULE [wordsTheory.dimword_def]
       (Q.INST [`i` |-> `1`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_backedge_run))) >> simp[] >> metis_tac[]) >>
  `lookup_block sback2.vs_current_bb fn.fn_blocks = SOME test /\
   sback2.vs_inst_idx = 0 /\ ~sback2.vs_halted /\
   lookup_var ctr sback2 = SOME (n2w 2)` by
    (simp_tac (srw_ss()) [Abbr `sback2`, jump_to_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!fuel. ghost_run (SUC fuel) ctx fn PG gc1 tc1 v1 =
     ghost_run fuel ctx fn PG gback2 tback2 sback2` by
    (simp_tac (srw_ss()) [Abbr `sback2`, Abbr `gback2`, Abbr `tback2`] >>
     irule (SRULE [wordsTheory.dimword_def]
       (Q.INST [`i` |-> `1`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_backedge_ghost_run))) >> simp[] >> metis_tac[]) >>
  `!fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG gback2 tback2 sback2 ==>
     ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG gc1 tc1 v1` by
    (qpat_assum `lookup_block v1.vs_current_bb _ = SOME back` mp_tac >>
     qpat_assum `back.bb_instructions = _` mp_tac >>
     qpat_assum `v1.vs_inst_idx = _` mp_tac >>
     qpat_assum `~v1.vs_halted` mp_tac >>
     qpat_assum `lookup_var ctr v1 = _` mp_tac >>
     qpat_assum `FLOOKUP gc1 ctr = NONE` mp_tac >>
     qpat_assum `op_taint tc1 (Var ctr) = {}` mp_tac >>
     qpat_assum `ctr <> tmp` mp_tac >>
     qpat_assum `lookup_block cond _ = SOME test` mp_tac >>
     qpat_assum `phi_prefix_length test.bb_instructions = 0` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sback2`, Abbr `gback2`, Abbr `tback2`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule (SRULE [wordsTheory.dimword_def]
       (Q.INST [`i` |-> `1`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_backedge_ptr_safe))) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `!fuel. run_from (SUC fuel) ctx fn sback2 =
     run_blocks (SUC fuel) ctx fn sf` by
    (simp_tac (srw_ss()) [Abbr `sf`] >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `2`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_test_run))) >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  simp_tac (srw_ss()) [Abbr `C`] >> rpt strip_tac >>
  `!e. run_from fuel ctx fn sf <> Error e` by metis_tac[] >>
  `sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted` by
    (simp_tac (srw_ss()) [Abbr `sf`, Abbr `sback2`, jump_to_def, update_var_def] >>
     qpat_assum `sb = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `?last. lookup_block sf.vs_current_bb fn.fn_blocks = SOME last` by
    (qpat_assum `fn_has_code sa sb fn` mp_tac >>
     qpat_assum `sf.vs_current_bb = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[fragExecTheory.fn_has_code_def] >> metis_tac[]) >>
  `phi_prefix_length last.bb_instructions = 0` by
    (irule fragContinuationPtrTheory.run_from_nonerror_no_phi >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_block exit fn.fn_blocks = SOME last` by
    (qpat_assum `lookup_block sf.vs_current_bb _ = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sf`, jump_to_def]) >>
  `!k. ghost_run (SUC k) ctx fn PG gback2 tback2 sback2 =
     ghost_run k ctx fn PG gf tf sf` by
    (simp_tac (srw_ss()) [Abbr `gf`, Abbr `tf`, Abbr `sf`] >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `2`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_test_ghost_run))) >>
     disch_then (qspecl_then [`tback2`, `ctx`, `PG`, `gback2`] ACCEPT_TAC)) >>
  `op_taint tback2 (Var ctr) = {}` by
    simp[Abbr `tback2`, ptrDisciplineTheory.op_taint_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  `!k. ptr_safe_run (cx_dead cx) 0 k ctx fn PG gf tf sf ==>
     ptr_safe_run (cx_dead cx) 0 (SUC k) ctx fn PG gback2 tback2 sback2` by
    (simp_tac (srw_ss()) [Abbr `gf`, Abbr `tf`, Abbr `sf`] >>
     rpt strip_tac >>
     drule_all (SRULE [wordsTheory.dimword_def, bool_to_word_def]
       (Q.INST [`i` |-> `2`, `n` |-> `2`]
         (SPEC_ALL typed_copy_loop_test_ptr_safe))) >> simp[]) >>
  `!k. run_blocks (SUC k) ctx fn sback2 = run_from k ctx fn sback2` by
    (qpat_assum `lookup_block sback2.vs_current_bb _ = SOME test` mp_tac >>
     qpat_assum `phi_prefix_length test.bb_instructions = 0` mp_tac >>
     qpat_assum `sback2.vs_inst_idx = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all fragExecTheory.run_blocks_run_from_no_phi >> simp[]) >>
  `!k. run_blocks (SUC k) ctx fn sf = run_from k ctx fn sf` by
    (qpat_assum `lookup_block sf.vs_current_bb _ = SOME last` mp_tac >>
     qpat_assum `phi_prefix_length last.bb_instructions = 0` mp_tac >>
     qpat_assum `sf.vs_inst_idx = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all fragExecTheory.run_blocks_run_from_no_phi >> simp[]) >>
  qpat_assum `!fuel. run_from (SUC fuel) ctx fn v1 = _` mp_tac >>
  qpat_assum `!fuel. run_from (SUC fuel) ctx fn sback2 = _` mp_tac >>
  qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG gc1 tc1 v1 = _` mp_tac >>
  qpat_assum `!fuel. ghost_run (SUC fuel) ctx fn PG gback2 tback2 sback2 = _` mp_tac >>
  qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ gback2 tback2 sback2 ==> _` mp_tac >>
  qpat_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ gf tf sf ==> _` mp_tac >>
  qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sback2 = _` mp_tac >>
  qpat_assum `!fuel. run_blocks (SUC fuel) ctx fn sf = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qexists_tac `SUC (SUC fuel)` >> simp[]
QED

Finalise compile_copy_sarray_strings_two_frag_ptr
