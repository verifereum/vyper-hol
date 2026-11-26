Theory bodyECMulLaunchCodeMods
Ancestors
  bodyPtrPrecompileBuiltinsCompilerStages bodyMemEcArithCode
  gasShadowCompileBuiltinScalar gasShadowCompileContext generatedGasOrigin
  stmtReasonLitFragMemory gasShadowState compileEnv exprLoweringProps
  loweringHalt loweringStateRelDefs emitHelper exprSimPrecompiles fragExec
  builtinMisc context venomInst rich_list

Theorem ecmul_shadow_cut[local]:
  gas_shadow_compiles f f /\ f s = (x,u) /\ gas_shadow_state s t ==>
  ?v. f t = (x,v) /\ gas_shadow_state u v
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum (qspecl_then [`s`,`t`] mp_tac) >>
  Cases_on `f t` >> simp[]
QED

Theorem ecmul_grouped_payload[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      d0 <- emit_op ADD [buf; Lit 0w];
      emit_void MSTORE [d0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      d1 <- emit_op ADD [buf; Lit 32w];
      emit_void MSTORE [d1; y];
      d2 <- emit_op ADD [buf; Lit 64w];
      emit_void MSTORE [d2; scalar] od) =
  (do (do xp <- emit_op ADD [p; Lit 0w]; x <- emit_op MLOAD [xp];
          d0 <- emit_op ADD [buf; Lit 0w]; emit_void MSTORE [d0; x] od);
      (do yp <- emit_op ADD [p; Lit 32w]; y <- emit_op MLOAD [yp];
          d1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [d1; y] od);
      d2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [d2; scalar] od)
Proof
  simp[comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem ecmul_buffer_compiler[local]:
  compile_ecmul_point p scalar =
  (do bufs <-
        (do ib <- compile_alloc_buffer 96;
            (do xp <- emit_op ADD [p; Lit 0w]; x <- emit_op MLOAD [xp];
                d0 <- emit_op ADD [ib.buf_operand; Lit 0w];
                emit_void MSTORE [d0; x] od);
            (do yp <- emit_op ADD [p; Lit 32w]; y <- emit_op MLOAD [yp];
                d1 <- emit_op ADD [ib.buf_operand; Lit 32w];
                emit_void MSTORE [d1; y] od);
            (do d2 <- emit_op ADD [ib.buf_operand; Lit 64w];
                emit_void MSTORE [d2; scalar] od);
            ob <- compile_alloc_buffer 64;
            return (ib,ob) od);
      gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 7w; (FST bufs).buf_operand; Lit 96w;
         (SND bufs).buf_operand; Lit 64w];
      emit_void ASSERT [success]; return (SND bufs).buf_operand od)
Proof
  simp[ecmul_compiler_grouped, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem ecmul_buffer_shadow[local]:
  f = (do ib <- compile_alloc_buffer 96;
          (do xp <- emit_op ADD [p; Lit 0w]; x <- emit_op MLOAD [xp];
              d0 <- emit_op ADD [ib.buf_operand; Lit 0w];
              emit_void MSTORE [d0; x] od);
          (do yp <- emit_op ADD [p; Lit 32w]; y <- emit_op MLOAD [yp];
              d1 <- emit_op ADD [ib.buf_operand; Lit 32w];
              emit_void MSTORE [d1; y] od);
          (do d2 <- emit_op ADD [ib.buf_operand; Lit 64w];
              emit_void MSTORE [d2; scalar] od);
          ob <- compile_alloc_buffer 64;
          return (ib,ob) od) ==>
  gas_shadow_compiles f f
Proof
  disch_then SUBST1_TAC >> simp[comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac >-
         simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
              gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem ecmul_suffix_blocks[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit 7w; i; Lit 96w; o'; Lit 64w];
      emit_void ASSERT [success]; return o' od) sm = (res,sb) ==>
  same_blocks sm sb
Proof
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
  metis_tac[same_blocks_trans]
QED

Theorem ecmul_mono_cut[local]:
  same_blocks a b /\ b.cs_current_insts = a.cs_current_insts ++ ins /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var ==>
  ci_mono a b
Proof
  simp[same_blocks_def, ci_mono_def, cs_extends_def, IS_PREFIX_APPEND] >>
  strip_tac >> qexists `[]` >> simp[]
QED

Theorem ecmul_shadow_launch_cut[local]:
  compile_ecmul_point p scalar sf = (res,sb) /\
  compile_ecmul_point p scalar tf = (res,tb) /\ gas_shadow_state sf tf /\
  compile_alloc_buffer 96 sf = (ib,ca) /\
  (do xp <- emit_op ADD [p; Lit 0w]; x <- emit_op MLOAD [xp];
      d0 <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [d0; x] od)
    ca = ((),c1) /\
  (do yp <- emit_op ADD [p; Lit 32w]; y <- emit_op MLOAD [yp];
      d1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [d1; y] od)
    c1 = ((),c2) /\
  (do d2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [d2; scalar] od)
    c2 = ((),cpost) /\
  compile_alloc_buffer 64 cpost = (ob,sm) ==>
  ?tm cg tg gas.
    gas_shadow_state sm tm /\
    emit_op GAS [] sm = (gas,cg) /\ emit_op GAS [] tm = (gas,tg) /\
    cs_extends tf tm /\ cs_extends sm cg /\ cs_extends cg sb /\
    cs_extends tm tg /\ cs_extends tg tb
Proof
  strip_tac >>
  qpat_assum `compile_ecmul_point _ _ sf = _`
    (mp_tac o ONCE_REWRITE_RULE[ecmul_buffer_compiler]) >>
  qmatch_goalsub_abbrev_tac `comp_bind front tail` >>
  `front sf = ((ib,ob),sm)` by
    simp[Abbr `front`, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  `gas_shadow_compiles front front` by
    (irule ecmul_buffer_shadow >> qexistsl_tac [`p`,`scalar`] >> simp[Abbr `front`]) >>
  drule_all ecmul_shadow_cut >> disch_then (qx_choose_then `tm` strip_assume_tac) >>
  `comp_bind front tail tf = (res,tb)` by
    (simp[Abbr `front`, Abbr `tail`, GSYM ecmul_buffer_compiler]) >>
  simp[comp_bind_def] >> strip_tac >>
  `tail (ib,ob) tm = (res,tb)` by
    (qpat_assum `comp_bind front tail tf = _` mp_tac >>
     pure_once_rewrite_tac[comp_bind_def] >> simp[]) >>
  Cases_on `emit_op GAS [] sm` >> rename1 `emit_op GAS [] sm = (gas,cg)` >>
  `gas_shadow_compiles (emit_op GAS []) (emit_op GAS [])` by
    simp[gas_shadow_compiles_emit_op] >>
  drule_all ecmul_shadow_cut >> disch_then (qx_choose_then `tg` strip_assume_tac) >>
  qexistsl_tac [`tm`,`cg`,`tg`,`gas`] >> simp[] >>
  `!s. ci_mono s (SND (front s))` by
    (simp[Abbr `front`, comp_ignore_bind_def, comp_bind_assoc] >> gen_tac >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac >-
          simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op, ci_mono_emit_void] >>
          rpt gen_tac >> BETA_TAC) >> simp[ci_mono_comp_return]) >>
  `ci_mono tf tm` by (first_x_assum (qspec_then `tf` mp_tac) >> simp[]) >>
  `ci_mono sm cg /\ ci_mono tm tg` by
    (mp_tac (Q.SPECL [`GAS`,`[]`,`sm`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`GAS`,`[]`,`tm`] ci_mono_emit_op) >> simp[]) >>
  qabbrev_tac `post_gas = \g. do
    success <- emit_op STATICCALL
      [g; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
    emit_void ASSERT [success]; return ob.buf_operand od` >>
  `post_gas gas cg = (res,sb) /\ post_gas gas tg = (res,tb)` by
    (conj_tac
     >- (qpat_x_assum `tail (ib,ob) sm = _` mp_tac >>
         simp[Abbr `tail`, Abbr `post_gas`, comp_ignore_bind_def, comp_bind_def]) >>
     qpat_x_assum `tail (ib,ob) tm = _` mp_tac >>
     simp[Abbr `tail`, Abbr `post_gas`, comp_ignore_bind_def, comp_bind_def]) >>
  `!s. ci_mono s (SND (post_gas gas s))` by
    (simp[Abbr `post_gas`, comp_ignore_bind_def] >> gen_tac >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac >-
          simp[ci_mono_emit_op, ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_comp_return]) >>
  `ci_mono cg sb /\ ci_mono tg tb` by
    (conj_tac
     >- (qpat_x_assum `!s. ci_mono s (SND (post_gas gas s))`
           (qspec_then `cg` mp_tac) >> simp[]) >>
     qpat_x_assum `!s. ci_mono s (SND (post_gas gas s))`
       (qspec_then `tg` mp_tac) >> simp[]) >>
  fs[ci_mono_def]
QED

Theorem ecmul_generated_site[local]:
  emit_op GAS [] sm = (gas,cg) /\ emit_op GAS [] tm = (gas,tg) /\
  gas_shadow_state sm tm /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sm cg func /\ fn_has_code tm tg shadow_func ==>
  (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx
Proof
  strip_tac >>
  qabbrev_tac `u = (ARB:venom_state) with
    <|vs_halted := F; vs_current_bb := sm.cs_current_bb;
      vs_inst_idx := LENGTH sm.cs_current_insts|>` >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`] >>
  drule_all (Q.INST [`memory` |-> `T`] compile_generated_gas_origin_path) >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem ecmul_code_intervals[local]:
  ci_mono sf ca /\ ci_mono ca cpost /\ ci_mono cpost sm /\ ci_mono sm sb /\
  fn_has_code sf sb func ==>
  fn_has_code sf ca func /\ fn_has_code ca cpost func /\
  fn_has_code cpost sm func /\ fn_has_code sm sb func
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends ca sb /\ cs_extends cpost sb` by metis_tac[cs_extends_trans] >>
  drule_all (Q.SPECL [`sf`,`ca`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
  drule_all (Q.SPECL [`ca`,`cpost`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
  drule_all (Q.SPECL [`cpost`,`sm`,`sb`,`func`] fn_has_code_split) >> simp[]
QED

Theorem ecmul_launch_code_mods:
  compile_ecmul_point p scalar sf = (res,sb) /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sf sb func /\ fn_has_code shadow_sf shadow_sb shadow_func /\
  compile_ecmul_point p scalar shadow_sf = (res,shadow_sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ca c1 c2 cpost ob sm src dst gv cv.
    compile_alloc_buffer 96 sf = (ib,ca) /\
    (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v] od)
      ca = ((),c1) /\
    (do x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v] od)
      c1 = ((),c2) /\
    (do y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od)
      c2 = ((),cpost) /\
    (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v];
        x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v];
        y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od)
      ca = ((),cpost) /\
    compile_alloc_buffer 64 cpost = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    gas_shadow_state sb shadow_sb /\
    ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\ res = Var dst /\
    emitted_insts sf sm = emitted_insts sf ca ++ emitted_insts ca cpost ++
      emitted_insts cpost sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    cpost.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cpost /\
    sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks ca cpost /\ same_blocks sf sm /\ same_blocks sm sb /\
    ci_mono sf ca /\ ci_mono ca cpost /\ ci_mono cpost sm /\ ci_mono sm sb /\
    sf.cs_next_id < ca.cs_next_id /\
    cpost.cs_next_id = ca.cs_next_id + 10 /\ cpost.cs_next_var = ca.cs_next_var + 7 /\
    cpost.cs_next_id < sm.cs_next_id /\
    sb.cs_next_id = sm.cs_next_id + 3 /\ sb.cs_next_var = sm.cs_next_var + 2 /\
    fn_has_code sf ca func /\ fn_has_code ca cpost func /\
    fn_has_code cpost sm func /\ fn_has_code sm sb func /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w] [src]) (fn_insts func) /\
    MEM (mk_inst cpost.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv cpost /\
    local_ptrs_reserved cenv sm /\
    not_fresh_at ca src /\ not_fresh_at sm src /\ not_fresh_at sm dst /\
    ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
    src <> gv /\ dst <> gv /\ dst <> cv /\ gv <> cv /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id GAS [] [gv];
       mk_inst (sm.cs_next_id + 1) STATICCALL
         [Var gv; Lit 7w; Var src; Lit 96w; Var dst; Lit 64w] [cv];
       mk_inst (sm.cs_next_id + 2) ASSERT [Var cv] []] /\
    (!u. ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
         u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
      (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx /\
      ?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
           isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions))
Proof
  strip_tac >>
  qpat_assum `compile_ecmul_point _ _ sf = _`
    (mp_tac o MATCH_MP ecmul_compiler_stages) >>
  disch_then (qx_choosel_then [`ib`,`ca`,`c1`,`c2`,`cpost`,`ob`,`sm`] strip_assume_tac) >>
  `((do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v];
        x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v];
        y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od)
      ca = ((),cpost))` by
    (pure_once_rewrite_tac[ecmul_grouped_payload] >>
     simp[comp_ignore_bind_def, comp_bind_def]) >>
  `gas_shadow_state sb shadow_sb` by
    (mp_tac (Q.INST [`p` |-> `p`,`scalar` |-> `scalar`]
      gas_shadow_compiles_ecmul_point) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sf`,`shadow_sf`] mp_tac) >> simp[]) >>
  drule_all (Q.INST [`sf` |-> `sf`,`tf` |-> `shadow_sf`] ecmul_shadow_launch_cut) >>
  disch_then (qx_choosel_then [`tm`,`cg`,`tg`,`gas`] strip_assume_tac) >>
  drule_all ecmul_prefix_code >> strip_tac >>
  drule_all (Q.INST [`sf` |-> `sf`, `sb` |-> `sb`] ecmul_points_prefix) >>
  strip_tac >> gvs[] >>
  rename1 `ib.buf_operand = Var src` >> rename1 `ob.buf_operand = Var dst` >>
  qpat_assum `compile_alloc_buffer 96 sf = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL compile_alloc_buffer_parts)) >>
  qpat_assum `compile_alloc_buffer 64 cpost = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL compile_alloc_buffer_parts)) >>
  `ci_mono sf ca /\ ci_mono cpost sm` by
    (mp_tac (Q.SPECL [`96`,`sf`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`64`,`cpost`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono ca cpost` by
    (irule ecmul_mono_cut >> simp[] >> qexists `emitted_insts ca cpost` >> simp[]) >>
  qpat_assum `(do gas <- emit_op GAS []; _ od) sm = (res,sb)`
    (strip_assume_tac o MATCH_MP computed_suffix_shape) >>
  qpat_assum `(do gas <- emit_op GAS []; _ od) sm = (res,sb)`
    (assume_tac o MATCH_MP ecmul_suffix_blocks) >>
  `ci_mono sm sb` by
    (irule ecmul_mono_cut >> simp[] >> qexists `emitted_insts sm sb` >> simp[]) >>
  drule_all ecmul_code_intervals >> strip_tac >>
  `fn_has_code sm cg func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists `sb` >> simp[]) >>
  `fn_has_code tm tg shadow_func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`shadow_sb`,`shadow_sf`] >> simp[]) >>
  drule_all ecmul_generated_site >> strip_tac >>
  qexistsl_tac [`STRING #"%" (toString sm.cs_next_var)`,
                `STRING #"%" (toString (sm.cs_next_var+1))`] >>
  `~not_fresh_at sm (STRING #"%" (toString sm.cs_next_var)) /\
   ~not_fresh_at sm (STRING #"%" (toString (sm.cs_next_var+1)))` by
    simp[not_fresh_at_def] >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP (LENGTH sm.cs_current_insts) bb.bb_instructions)` by
    (mp_tac (Q.SPECL [`sm`,`sb`,`func`,`emitted_insts sm sb`] fn_has_code_code) >>
     `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
     simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[venomStateTheory.operand_11]
QED
