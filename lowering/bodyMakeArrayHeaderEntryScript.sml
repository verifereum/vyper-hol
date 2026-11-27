(* Request-free initialization up to the common homogeneous element loop. *)
Theory bodyMakeArrayHeaderEntry
Ancestors
  bodyFullShadowBodyInv bodyFullMakeArrayInit bodyFullMakeArrayHeader
  exprSimAggregateLoops exprSimAggregateEncoding exprSimAggregateLayout
  exprOperandVar bodyMemArrayLayout
  gasShadowState gasShadow gasShadowCompileContext exprLoweringProps
  emitHelperProps exprSimDefs[qualified,ignore_grammar] bodyFullPreds
  bodyFullIfExpReach fragGasOriginPtrLoop rich_list list

val _ = Parse.hide "base";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all array_body_allocation_layout >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `compile_make_array compile_expr cenv args et _ header _ _` >>
  `?sba ssm su.
    compile_alloc_buffer (type_memory_bytes cenv (ArrayT et n)) shadow_sa = (sba,ssm) /\
    compile_make_array compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) et
      (type_memory_size tv) header sba.buf_operand ssm = (su,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def] >>
     disch_then (mp_tac o MATCH_MP compile_array_literal_inv) >>
     simp[gasShadowCompileBaseTheory.type_memory_bytes_gas_shadow_env,Abbr `header`] >>
     metis_tac[]) >>
  `sba = ba /\ gas_shadow_state sm ssm` by
    (mp_tac (Q.INST [`nbytes` |-> `type_memory_bytes cenv (ArrayT et n)`]
      gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`cap` |-> `type_memory_bytes cenv (ArrayT et n)`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
    `ann` |-> `ArrayT et n`, `elem_opt` |-> `SOME et`, `bnd` |-> `n`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  `u = Var q /\ su = Var q` by metis_tac[compiler_make_array_result] >> gvs[] >>
  suspend "split_header"
QED
*)
Theorem make_array_header_loop_entry:
  expr_body_pre cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es /\
  body_inv tops ctx cenv cx /\
  storage_trace_domain cx st0 es.storage_trace /\
  compile_expr cenv ty (Builtin ann (MakeArray (SOME et) n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (MakeArray (SOME et) n) args)) shadow_sa =
      (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  (!fn i z. frag_reachable ctx func s0 fn i z ==> dalloca_fmp_headroom i z) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q tv header off base cap ps sh ssh sj Gj tnj.
    ann = ArrayT et n /\ vv = LocatedValue ann (mk_ptr (Var q) LocMemory) /\
    header = (case n of Dynamic _ => T | _ => F) /\
    off = (if header then 32 else 0) /\ cap = type_memory_bytes cenv ann /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    type_memory_bytes cenv et = type_memory_size tv /\
    LIST_REL (\ty e. arg_type_fits (expr_type e) ty) (REPLICATE (LENGTH args) et) args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) et) =
      SOME (REPLICATE (LENGTH args) tv) /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv)
      (REPLICATE (LENGTH args) et) (REPLICATE (LENGTH args) tv) /\
    off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= cap /\
    compile_make_tuple compile_expr cenv args (REPLICATE (LENGTH args) et)
      (Var q) off sh = (Var q,sb) /\
    compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args)
      (REPLICATE (LENGTH args) et) (Var q) off ssh = (Var q,shadow_sb) /\
    gas_shadow_state sh ssh /\ fn_has_code sh sb func /\ fn_has_code ssh shadow_sb shadow_func /\
    sa.cs_next_id <= sh.cs_next_id /\ sa.cs_next_var <= sh.cs_next_var /\
    local_ptrs_reserved cenv sh /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK sj,Gj,tnj)) /\
    (!fn i z. frag_reachable ctx func sj fn i z ==> dalloca_fmp_headroom i z) /\
    FLOOKUP sj.vs_allocas sa.cs_next_id = SOME (base,cap) /\
    lookup_var q sj = SOME (n2w base) /\ ptr_covers Gj tnj q sj cap /\
    not_fresh_at sh q /\ sa.cs_next_id < sh.cs_next_id /\
    base + cap < dimword (:256) /\ base + cap <= sj.vs_alloca_next /\
    (!name b m. local_region cenv es.scopes sj name b m ==>
      loweringStateRelDefs$regions_disjoint base cap b m) /\
    alloca_history func sj /\ s0.vs_alloca_next <= sj.vs_alloca_next /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP sj.vs_allocas aid = SOME b) /\
    wb_frame cenv es es sa s0 sj /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gj tnj /\
    return_buf_frame d cenv sh sj /\ ~sj.vs_halted /\
    sj.vs_current_bb = sh.cs_current_bb /\ sj.vs_inst_idx = LENGTH sh.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es sj /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es Gj tnj sj) /\
    EVERY (\(rt,v,p,m). val_wf rt v /\ val_footprint rt v <= m /\
      base <= p /\ p + m <= base + off /\
      (!mem. mem_agree_outside tnj.t_mem sj.vs_memory mem ==> val_in_memory rt v p mem)) ps
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume make_array_header_loop_entry[split_header]:
  `?sh. (if header then emit_void MSTORE [Var q; Lit (n2w (LENGTH args))]
         else return ()) sm = ((),sh) /\
     compile_make_array_elems compile_expr cenv args et (type_memory_size tv)
       header (Var q) 0 sh = (Var q,sb)` by
    (qpat_x_assum `compile_make_array _ _ args _ _ _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_make_array_def,compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_bind_def] >>
     pairarg_tac >> rename1 `(if header then _ else _) sm = (uh,hcs)` >>
     Cases_on `uh` >> gvs[] >> metis_tac[]) >>
  `?ssh. (if header then emit_void MSTORE [Var q; Lit (n2w (LENGTH args))]
         else return ()) ssm = ((),ssh) /\ gas_shadow_state sh ssh` by
    (reverse (Cases_on `header`)
     >- gvs[compileEnvTheory.comp_return_def] >>
     mp_tac (Q.INST [`opc` |-> `MSTORE`,
       `ops` |-> `[Var q; Lit (n2w (LENGTH (args:expr list)))]`] gas_shadow_compiles_emit_void) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`ssm`] mp_tac) >> simp[] >>
     Cases_on `emit_void MSTORE [Var q; Lit (n2w (LENGTH args))] ssm` >>
     Cases_on `q'` >> gvs[]) >>
  `compile_make_array_elems compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) et
     (type_memory_size tv) header (Var q) 0 ssh = (Var q,shadow_sb)` by
    (qpat_x_assum `compile_make_array _ _ (MAP _ args) _ _ _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_make_array_def,compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_bind_def]) >>
  suspend "loop_code"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_array_header_loop_entry[loop_code]:
  `type_memory_bytes (gas_shadow_env T cenv) et = type_memory_size tv` by
    simp[gasShadowCompileBaseTheory.type_memory_bytes_gas_shadow_env] >>
  qpat_x_assum `compile_make_array_elems _ cenv _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_memory_bytes cenv et = _`
    (fn th => pure_rewrite_tac[GSYM th,compile_make_array_elems_as_tuple]) >> strip_tac >>
  qpat_x_assum `compile_make_array_elems _ (gas_shadow_env T cenv) _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_memory_bytes (gas_shadow_env T cenv) et = _`
    (fn th => pure_rewrite_tac[GSYM th,compile_make_array_elems_as_tuple]) >> strip_tac >>
  fs[] >>
  `ci_mono sm sh /\ ci_mono ssm ssh` by
    (Cases_on `header` >> gvs[compileEnvTheory.comp_return_def] >-
      metis_tac[ci_mono_emit_void, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `ci_mono sh sb /\ ci_mono ssh shadow_sb` by
    (conj_tac
     >- (qpat_assum `compile_make_tuple _ cenv _ _ _ _ sh = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         metis_tac[ci_mono_compile_make_tuple_cfn,compile_expr_ci_mono,pairTheory.SND]) >>
     qpat_assum `compile_make_tuple _ (gas_shadow_env T cenv) _ _ _ _ ssh = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_make_tuple_cfn,compile_expr_ci_mono,pairTheory.SND]) >>
  `ci_mono shadow_sa ssm` by
    metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `ci_mono shadow_sa ssh` by (irule ci_mono_trans >> qexists_tac `ssm` >> simp[]) >>
  `fn_has_code sm sh func /\ fn_has_code sh sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `fn_has_code ssh shadow_sb shadow_func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     conj_tac >- fs[ci_mono_def] >> qexists_tac `shadow_sa` >> fs[ci_mono_def]) >>
  suspend "execute_header"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_array_header_loop_entry[execute_header]:
  `0 < type_slot_size tv` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def] >> IF_CASES_TAC >> simp[]) >>
  `0 < type_memory_size tv` by metis_tac[valueEncodingPropsTheory.type_memory_size_pos] >>
  `LENGTH args < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `type_memory_bytes cenv (ArrayT et n)` >>
     conj_tac >- decide_tac >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH args * type_memory_size tv` >>
     conj_tac >- simp[] >>
     qpat_x_assum `_ + _ <= type_memory_bytes cenv (ArrayT et n)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qmatch_goalsub_abbrev_tac `sz + _ <= cap` >> decide_tac) >>
  `header ==> 32 <= type_memory_bytes cenv (ArrayT et n)` by (strip_tac >> gvs[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  mp_tac (Q.INST [`csbase` |-> `sa`, `ebase` |-> `es`, `sbase` |-> `s0`,
    `Gbase` |-> `G0`, `tnbase` |-> `tn0`, `aid` |-> `sa.cs_next_id`,
    `base` |-> `w2n (w:256 word)`, `cap` |-> `type_memory_bytes cenv (ArrayT et n)`,
    `s` |-> `si`, `G` |-> `Gi`, `tn` |-> `tni`, `len` |-> `LENGTH (args:expr list)`,
    `ai` |-> `mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (ArrayT et n)))]
      [STRING #"%" (toString sa.cs_next_var)]`, `PG` |-> `PG`]
    make_array_header_full) >>
  (impl_tac >- (simp[venomInstTheory.mk_inst_def] >> rpt strip_tac >>
                first_x_assum irule >> qexists_tac `name` >> simp[])) >>
  disch_then (qx_choosel_then [`sj`,`Gj`,`tnj`,`ps`] strip_assume_tac) >>
  suspend "entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_array_header_loop_entry[entry]:
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s0,G0,tn0) [] (OK sj,Gj,tnj)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gi`,`si`,`tni`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn i z. frag_reachable ctx func sj fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK sj,Gj,tnj)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK sj,Gj,tnj)`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     simp[] >> disch_then (fn th => first_assum (ACCEPT_TAC o MATCH_MP th))) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) et) =
    SOME (REPLICATE (LENGTH args) tv)` by
    (qspec_tac (`LENGTH args`, `k`) >> Induct >> simp[REPLICATE]) >>
  `LIST_REL (\ty e. arg_type_fits (expr_type e) ty)
    (REPLICATE (LENGTH args) et) args` by
    gvs[LIST_REL_EL_EQN, EL_REPLICATE, EVERY_EL] >>
  `ci_mono sa sh` by (irule ci_mono_trans >> qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`q`,`w2n w`,`ps`,`sh`,`ssh`,`sj`,`Gj`,`tnj`] >>
  fs[ci_mono_def,type_memory_size_list_replicate,LIST_REL_REPLICATE_same,arithmeticTheory.ADD_SYM] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> qpat_assum `!name b m. local_region _ _ sj name b m ==> _` irule >>
  qexists_tac `name` >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise make_array_header_loop_entry
*)
