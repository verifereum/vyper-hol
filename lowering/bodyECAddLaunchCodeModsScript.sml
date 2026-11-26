(* Compiler cuts and origin of the generated gas read in the ECAdd packet. *)
Theory bodyECAddLaunchCodeMods
Ancestors
  bodyPtrPrecompileBuiltinsCompilerStages generatedGasOrigin
  gasShadowCompileContext stmtReasonLitFragMemory compileAllocaProvenance freshWrites
  exprLoweringProps loweringHalt loweringStateRelDefs compileEnv emitHelper
  gasShadowState fragExec exprSimPrecompiles list
Libs monadsyntax

Theorem ecadd_linear_mono[local]:
  same_blocks a b /\ b.cs_current_insts = a.cs_current_insts ++ code /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id ==>
  ci_mono a b
Proof
  simp[ci_mono_def, same_blocks_def, cs_extends_def] >> strip_tac >>
  qexists `[]` >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem ecadd_suffix_mono[local]:
  (do ok <- emit_op STATICCALL [g; Lit 6w; ip; Lit 128w; op; Lit 64w];
      emit_void ASSERT [ok]; return op od) s = (r,t) ==>
  ci_mono s t /\ same_blocks s t
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[ci_mono_def, same_blocks_def, cs_extends_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem ecadd_gas_cut[local]:
  gas_shadow_state sm shm /\
  (do g <- emit_op GAS [];
      ok <- emit_op STATICCALL [g; Lit 6w; ip; Lit 128w; op; Lit 64w];
      emit_void ASSERT [ok]; return op od) sm = (res,sb) /\
  (do g <- emit_op GAS [];
      ok <- emit_op STATICCALL [g; Lit 6w; ip; Lit 128w; op; Lit 64w];
      emit_void ASSERT [ok]; return op od) shm = (shres,shb) /\
  fn_has_code sm sb func /\ fn_has_code shm shb shfunc /\
  gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shctx
Proof
  strip_tac >>
  Cases_on `emit_op GAS [] sm` >> Cases_on `emit_op GAS [] shm` >>
  fs[Once comp_bind_def] >>
  imp_res_tac ecadd_suffix_mono >>
  `!opc ops st. ci_mono st (SND (emit_op opc ops st))` by
    simp[ci_mono_emit_op] >>
  first_x_assum (fn th =>
    qspecl_then [`GAS`, `[]`, `sm`] mp_tac th >>
    qspecl_then [`GAS`, `[]`, `shm`] mp_tac th) >>
  simp[] >> rpt strip_tac >>
  `fn_has_code sm r func /\ fn_has_code shm r' shfunc` by
    (conj_tac >> irule (cj 1 fn_has_code_split) >>
     first_assum (irule_at Any) >> fs[ci_mono_def]) >>
  drule_all compile_generated_gas_origin_path >> simp[]
QED

(* Paired compilers for each transfer return unit and preserve the cut relation. *)
Theorem ecadd_transfer_shadow[local]:
  gas_shadow_state s t /\
  (do x <- emit_op ADD [p; Lit a]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit z]; emit_void MSTORE [y; v] od) s = ((),s') /\
  (do x <- emit_op ADD [p; Lit a]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit z]; emit_void MSTORE [y; v] od) t = ((),t') ==>
  gas_shadow_state s' t'
Proof
  strip_tac >>
  qabbrev_tac `f = do x <- emit_op ADD [p; Lit a]; v <- emit_op MLOAD [x];
                       y <- emit_op ADD [b; Lit z]; emit_void MSTORE [y; v] od` >>
  `gas_shadow_compiles f f` by
    (simp[Abbr `f`] >>
     rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
          >- simp[gas_shadow_compiles_emit_op_same] >> gen_tac >> BETA_TAC) >>
     simp[gas_shadow_compiles_emit_void]) >>
  pop_assum (qspecl_then [`s`,`t`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[]
QED

Theorem ecadd_alloc_shadow[local]:
  gas_shadow_state s t /\ compile_alloc_buffer n s = (b,s') /\
  compile_alloc_buffer n t = (d,t') ==>
  b = d /\ gas_shadow_state s' t'
Proof
  strip_tac >>
  qspec_then `n` (qspecl_then [`s`,`t`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def])
    (GEN_ALL gas_shadow_compiles_alloc_buffer) >>
  simp[]
QED

Theorem ecadd_packet_mono[local]:
  (do g <- emit_op GAS [];
      ok <- emit_op STATICCALL [g; Lit 6w; ip; Lit 128w; op; Lit 64w];
      emit_void ASSERT [ok]; return op od) s = (r,t) ==>
  ci_mono s t /\ same_blocks s t
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[ci_mono_def, same_blocks_def, cs_extends_def,
       rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem ecadd_alloc_mono[local]:
  compile_alloc_buffer n s = (b,t) ==> ci_mono s t /\ same_blocks s t
Proof
  strip_tac >> drule_then strip_assume_tac compile_alloc_buffer_insts >>
  qspecl_then [`n`,`s`] mp_tac ci_mono_compile_alloc_buffer >> simp[same_blocks_def]
QED

Theorem ecadd_packet_code[local]:
  ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ fn_has_code a e f ==>
  fn_has_code a b f /\ fn_has_code b c f /\ fn_has_code c d f /\ fn_has_code d e f
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends c e` by (irule cs_extends_trans >> qexists `d` >> simp[]) >>
  `cs_extends b e` by (irule cs_extends_trans >> qexists `c` >> simp[]) >>
  `fn_has_code a b f /\ fn_has_code b e f` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code b c f /\ fn_has_code c e f` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code c d f /\ fn_has_code d e f` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

Theorem ecadd_emitted_member[local]:
  fn_has_code sf sb func ==> !i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)
Proof
  strip_tac >> rewrite_tac[emitted_insts_def] >> rpt strip_tac >>
  irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
  qexists `sf` >> simp[] >> metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

Theorem ecadd_launch_fresh[local]:
  gv = STRING #"%" (toString sm.cs_next_var) /\
  cv = STRING #"%" (toString (sm.cs_next_var + 1)) /\
  not_fresh_at sm src /\ not_fresh_at sm dst ==>
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  src <> gv /\ dst <> gv /\ src <> cv /\ dst <> cv
Proof
  strip_tac >>
  `~not_fresh_at sm gv /\ ~not_fresh_at sm cv` by
    (simp[not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem ecadd_launch_code_mods:
  compile_ecadd_points (Var p) (Var q) sf = (res,sb) /\
  compile_ecadd_points (Var p) (Var q) shf = (shres,shb) /\
  gas_shadow_state sf shf /\ gas_shadow_context ctx shctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code sf sb func /\ fn_has_code shf shb shfunc /\
  local_ptrs_reserved cenv sf ==>
  ?ib ca c1 c2 c3 cp ob sm shm src dst gv cv.
    compile_alloc_buffer 128 sf = (ib,ca) /\
    (do x <- emit_op ADD [Var p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y; v] od)
      ca = ((),c1) /\
    (do x <- emit_op ADD [Var p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y; v] od)
      c1 = ((),c2) /\
    (do x <- emit_op ADD [Var q; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y; v] od)
      c2 = ((),c3) /\
    (do x <- emit_op ADD [Var q; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [y; v] od)
      c3 = ((),cp) /\
    compile_alloc_buffer 64 cp = (ob,sm) /\
    gas_shadow_state sm shm /\ ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\
    res = Var dst /\ shres = res /\
    fn_has_code sf ca func /\ fn_has_code ca cp func /\
    fn_has_code cp sm func /\ fn_has_code sm sb func /\ fn_has_code shm shb shfunc /\
    ci_mono sf ca /\ ci_mono ca cp /\ ci_mono cp sm /\ ci_mono sm sb /\
    local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv cp /\
    local_ptrs_reserved cenv sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w] [src]) (fn_insts func) /\
    MEM (mk_inst cp.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    emitted_insts sf sm = emitted_insts sf ca ++ emitted_insts ca cp ++
                         emitted_insts cp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    gv = STRING #"%" (toString sm.cs_next_var) /\
    cv = STRING #"%" (toString (sm.cs_next_var + 1)) /\
    not_fresh_at ca src /\ not_fresh_at cp src /\
    not_fresh_at sm src /\ not_fresh_at sm dst /\
    ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
    src <> gv /\ dst <> gv /\ src <> cv /\ dst <> cv /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id GAS [] [gv];
       mk_inst (sm.cs_next_id+1) STATICCALL
         [Var gv; Lit 6w; Var src; Lit 128w; Var dst; Lit 64w] [cv];
       mk_inst (sm.cs_next_id+2) ASSERT [Var cv] []] /\
    (!u. ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
         u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
         (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shctx /\
         ?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
              isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions))
Proof
  strip_tac >>
  qpat_assum `compile_ecadd_points _ _ sf = _`
    (strip_assume_tac o MATCH_MP ecadd_compiler_stages) >>
  qpat_assum `compile_ecadd_points _ _ shf = _`
    (strip_assume_tac o MATCH_MP ecadd_compiler_stages) >>
  `ib = ib' /\ gas_shadow_state sa sa'` by (drule_all ecadd_alloc_shadow >> simp[]) >>
  fs[] >>
  `gas_shadow_state s1 s1'` by (drule_all ecadd_transfer_shadow >> simp[]) >>
  `gas_shadow_state s2 s2'` by (drule_all ecadd_transfer_shadow >> simp[]) >>
  `gas_shadow_state s3 s3'` by (drule_all ecadd_transfer_shadow >> simp[]) >>
  `gas_shadow_state sp sp'` by (drule_all ecadd_transfer_shadow >> simp[]) >>
  `ob = ob' /\ gas_shadow_state sm sm'` by (drule_all ecadd_alloc_shadow >> simp[]) >>
  fs[] >>
  imp_res_tac ecadd_alloc_mono >>
  imp_res_tac ecadd_packet_mono >>
  `ci_mono sa sp /\ ci_mono sa' sp'` by
    (conj_tac >> irule ecadd_linear_mono >> simp[] >> first_assum (irule_at Any)) >>
  `fn_has_code sf sa func /\ fn_has_code sa sp func /\
   fn_has_code sp sm func /\ fn_has_code sm sb func` by
    (irule ecadd_packet_code >> simp[]) >>
  `fn_has_code shf sa' shfunc /\ fn_has_code sa' sp' shfunc /\
   fn_has_code sp' sm' shfunc /\ fn_has_code sm' shb shfunc` by
    (irule ecadd_packet_code >> simp[]) >>
  qpat_assum `fn_has_code sf sb func` (assume_tac o MATCH_MP ecadd_emitted_member) >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  `?src dst. ib'.buf_operand = Var src /\ ob'.buf_operand = Var dst /\
     not_fresh_at sa src /\ not_fresh_at sm src /\ not_fresh_at sm dst /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
     local_ptrs_reserved cenv sm /\
     MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w] [src]) (fn_insts func) /\
     MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
     emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++ emitted_insts sp sm /\
     emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    (drule_all allocated_stage_frame >> strip_tac >>
     imp_res_tac compile_alloc_buffer_parts >> gvs[] >>
     qexistsl_tac [`STRING #"%" (toString sf.cs_next_var)`,
                   `STRING #"%" (toString sp.cs_next_var)`] >> simp[]) >>
  `not_fresh_at sp src` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  qpat_assum `comp_bind (emit_op GAS []) _ sm = _`
    (strip_assume_tac o MATCH_MP computed_suffix_shape) >>
  qpat_assum `comp_bind (emit_op GAS []) _ sm' = _`
    (strip_assume_tac o MATCH_MP computed_suffix_shape) >>
  `!u. ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shctx` by
    (rpt strip_tac >> drule_all ecadd_gas_cut >> simp[]) >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP (LENGTH sm.cs_current_insts) bb.bb_instructions)` by
    (`sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
     drule_all (Q.SPECL [`sm`,`sb`,`func`] fn_has_code_code) >> simp[]) >>
  qabbrev_tac `gv = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (sm.cs_next_var + 1))` >>
  `~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
   src <> gv /\ dst <> gv /\ src <> cv /\ dst <> cv` by
    (irule ecadd_launch_fresh >> simp[Abbr `gv`,Abbr `cv`]) >>
  qexistsl_tac [`sm'`,`src`,`dst`] >> gvs[Abbr `gv`,Abbr `cv`] >>
  first_assum ACCEPT_TAC
QED
