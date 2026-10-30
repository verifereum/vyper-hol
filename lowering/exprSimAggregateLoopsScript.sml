(*
 * The store loops of aggregate literals (#636)
 *
 * compile_make_tuple, compile_struct_lit and compile_make_array emit an
 * ADD, an unwrap and a store per child.  By induction on the children,
 * each loop evaluates them in order, fills its slice of the buffer, and
 * keeps the bytes outside it, the older allocations and the locals.
 *
 * TOP-LEVEL:
 *   aggregate_make_tuple_sim — compile_make_tuple
 *   aggregate_struct_fields_sim — compile_struct_lit, by the tuple loop
 *   aggregate_make_array_sim — compile_make_array, with or without a
 *     length word
 *
 * Helpers: aggregate_alloca_slice_excludes_local,
 *   compile_make_array_elems_as_tuple, and the per-step sims.
 *)
Theory exprSimAggregateLoops
Ancestors
  exprSimAggregateSource exprSimAggregateEncoding exprSimAggregateLayout exprLoweringProps
  localPtrsProps compileEnv valueEncoding valueEncodingProofs
  valueEncodingProps exprLowering vyperInterpreter vyperState
  exprSimHyps exprSim fragExec exprSimAggregateChildren exprSimOps
  vyperEvalExprPreservesScopesDom

Theorem aggregate_alloca_slice_excludes_local:
  stmt_state_rel func ce cx es r /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + n <= asz /\ local_region ce es.scopes r name lo sz ==>
  lo + sz <= b + off \/ b + off + n <= lo
Proof
  strip_tac >>
  `alloca_inv r /\ local_ptrs_rel func ce es.scopes r` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem aggregate_make_tuple_sim:
  !args ce cx env off sa out sb es res es' tvs func inst x b asz s0 ctx.
  compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb) /\
  eval_exprs cx args es = (res,es') /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_sim_pre ce cx env e st) /\ EVERY (expr_ok ce) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) ==>
  out = Var x /\
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func ce cx es s)
    (\r. ?vs. res = INL vs /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel func ce cx es' r /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >>
      simp[compile_make_tuple_def, comp_return_def, Once evaluate_def,
           return_def] >> rpt strip_tac >> gvs[] >>
      irule frag_exec_refl >> simp[val_in_memory_def]) >>
  rpt gen_tac >> strip_tac >>
  `out = Var x` by metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  gvs[] >>
  qpat_x_assum `compile_make_tuple _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_make_tuple_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func ce cx es s0`)
  >- simp[frag_exec_def] >>
  suspend "cons"
QED

Resume aggregate_make_tuple_sim[cons]:
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (expr_type h) su = ((),ss)` >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono ss sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `expr_sim_pre ce cx env h es` by metis_tac[] >>
  `expr_vv_sim ctx func ce cx (expr_type h) h es` by
    metis_tac[expr_ok_def, expr_vv_ok_def] >>
  drule aggregate_eval_exprs_cons >> strip_tac
  >- suspend "child_error"
  >- suspend "materialise_error" >>
  suspend "child_success"
QED

Resume aggregate_make_tuple_sim[child_error]:
  qpat_x_assum `!ce cx env off sa out sb es res es' tvs func inst x b asz s0 ctx. _` kall_tac >>
  `expr_res_ok (INR exc)` by
    (drule expr_sim_pre_res_ok >>
     disch_then (qspecl_then [`INR exc`, `es'`] mp_tac) >> simp[bind_def]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INR exc`, `es'`, `s0`] mp_tac) >>
  fs[expr_vv_res_ok_def, expr_res_ok_def] >> strip_tac >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[lambdify (oneline expr_exit_def)]
QED

Resume aggregate_make_tuple_sim[materialise_error]:
  qpat_x_assum `!ce cx env off sa out sb es res es' tvs func inst x b asz s0 ctx. _` kall_tac >>
  `expr_vv_res_ok (INL tv)` by metis_tac[aggregate_child_res_ok] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INL tv`, `es1`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >> simp[] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >>
  drule vv_post_materialises >> simp[]
QED

Resume aggregate_make_tuple_sim[child_success]:
  `expr_vv_res_ok (INL tv)` by metis_tac[aggregate_child_res_ok] >>
  `value_has_type h' v /\ val_wf h' v` by
    metis_tac[aggregate_materialised_child_typed, aggregate_materialised_child_wf] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INL tv`, `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  irule aggregate_child_add_then >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  simp[ci_mono_def] >>
  qexists_tac `n2w b` >>
  irule_at Any frag_exec_pre_exit >>
  qexistsl_tac [`s0`, `INL tv`] >> simp[] >>
  qpat_assum `frag_exec _ _ _ _ _ _` (irule_at Any o SRULE []) >>
  simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >> gvs[vv_post_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
      fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  rpt strip_tac >> suspend "after_add"
QED

Resume aggregate_make_tuple_sim[after_add]:
  `expr_sim_inv ce cx env es1` by
    (drule_all expr_sim_pre_eval_result >> simp[]) >>
  `type_memory_bytes ce (expr_type h) = type_memory_size h'` by
    metis_tac[exprSimAggregateLayoutTheory.expr_sim_inv_memory_size] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var d) r` >>
  `lookup_var d r = SOME (n2w (b+off))` by
    gvs[venomStateTheory.eval_operand_def, wordsTheory.word_add_n2w] >>
  `not_fresh_at sn d` by
    simp[Abbr `d`, not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved,
              ci_mono_def, cs_extends_trans] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  `stmt_state_rel func ce cx es1 r /\
   FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `off + type_memory_size h' <= asz /\ b+off+type_memory_size h' < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `!name lo sz. local_region ce es1.scopes r name lo sz ==>
      lo+sz <= b+off \/ b+off+type_memory_size h' <= lo` by
    (`not_local_ptr ce es1.scopes x` by simp[] >>
     rpt strip_tac >> drule_all aggregate_alloca_slice_excludes_local >> simp[]) >>
  irule frag_exec_seq_pointwise >>
  qexists_tac `\q. val_in_memory h' v (b+off) q.vs_memory /\
    stmt_state_rel func ce cx es1 q /\
    (!z a. not_fresh_at sn z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid p n a k. FLOOKUP r.vs_allocas aid = SOME (p,n) /\
      aid < sa.cs_next_id /\
      (!name lo sz. local_region ce es1.scopes r name lo sz ==>
        p+n <= lo \/ lo+sz <= p) /\
      p <= a /\ a+k <= p+n /\
      (a+k <= b+off \/ b+off+type_memory_size h' <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es1 r q` >>
  qexists_tac `ss` >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[ci_mono_def, cs_extends_trans] >>
      conj_tac >- fs[ci_mono_def] >>
      irule aggregate_unwrap_store_slice_sim >>
      qpat_assum `unwrap_value _ _ _ = _` (irule_at Any) >>
      qpat_assum `compile_store_memory _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexists_tac `n2w (b+off)` >>
      fs[ci_mono_def] >> rpt conj_tac
      >- (rpt strip_tac >> first_x_assum drule >> simp[arithmeticTheory.ADD_ASSOC])
      >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
          first_x_assum irule >>
          (reverse conj_tac >- fs[]) >>
          qexistsl_tac [`aid`, `p`, `n`] >>
          fs[] >> rpt strip_tac >> first_x_assum drule >> decide_tac)
      >> decide_tac) >>
  rpt strip_tac >> suspend "after_store"
QED

Resume aggregate_make_tuple_sim[after_store]:
  fs[] >>
  `cs_extends sa ss` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code ss sb func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce ss` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved, ci_mono_def] >>
  `not_fresh_at sn x /\ not_fresh_at ss x` by
    (fs[not_fresh_at_def, ci_mono_def] >> decide_tac) >>
  `lookup_var x r = SOME (n2w b)` by (fs[vv_post_def] >> metis_tac[]) >>
  `lookup_var x t' = SOME (n2w b) /\
   FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,asz)` by metis_tac[] >>
  qpat_x_assum `!ce':compile_env. _` drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then `func` mp_tac) >>
  disch_then (qspec_then `inst` mp_tac) >>
  disch_then (qspecl_then [`b`, `asz`, `t'`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[ci_mono_def, type_memory_size_def] >> decide_tac)) >>
  strip_tac >>
  qpat_x_assum `frag_exec _ ss sb _ _ _` (mp_then Any irule frag_exec_weaken) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> suspend "tuple_join") >>
  rpt strip_tac >> Cases_on `rr` >> gvs[]
QED

Resume aggregate_make_tuple_sim[tuple_join]:
  gvs[] >> rpt conj_tac
  >- suspend "head_encoding"
  >- suspend "vars_join"
  >- suspend "allocas_join"
  >- suspend "slice_join"
  >- suspend "exterior_join"
  >> suspend "locals_join"
QED

Resume aggregate_make_tuple_sim[head_encoding]:
  pure_once_rewrite_tac[val_in_memory_def] >>
  simp_tac std_ss [listTheory.list_case_def, LET_THM] >>
  conj_tac
  >- (irule (cj 1 val_in_memory_mem_agree_proof) >>
      simp[] >> qexists_tac `t'.vs_memory` >> simp[] >>
      qpat_x_assum `!p n. b <= p /\ _ ==> _` (qspecl_then [`b + off`, `type_memory_size h'`] mp_tac) >>
      fs[type_memory_size_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `tuple_in_memory vs t _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  simp_tac bool_ss []
QED

Resume aggregate_make_tuple_sim[vars_join]:
  rpt strip_tac >>
  `not_fresh_at sn z /\ not_fresh_at ss z` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac std_ss [vv_post_def] >> strip_tac >>
  metis_tac[]
QED

Resume aggregate_make_tuple_sim[allocas_join]:
  rpt strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac std_ss [vv_post_def] >> strip_tac >> metis_tac[]
QED

Resume aggregate_make_tuple_sim[slice_join]:
  rpt strip_tac >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      b + asz <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def]) >>
  `mem_bytes_at b asz r.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any irule vv_post_old_buffer) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!name lo sz. local_region ce es1.scopes r name lo sz ==>
      asz + b <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es1.scopes x` by simp[] >>
     `alloca_inv r /\ local_ptrs_rel func ce es1.scopes r` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at p n s.vs_memory = mem_bytes_at p n t'.vs_memory` by
    (qpat_assum `!p n. b <= p /\ _ ==> _` irule >>
     fs[type_memory_size_def] >> decide_tac) >>
  `mem_bytes_at p n t'.vs_memory = mem_bytes_at p n r.vs_memory` by
    (qpat_assum `!aid p n a k. _` irule >>
     reverse conj_tac >- (fs[type_memory_size_def] >> decide_tac) >>
     qexistsl_tac [`inst.inst_id`, `asz`, `b`] >> asm_rewrite_tac[] >> decide_tac) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `mem_bytes_at b asz _ = _`
       (mp_then Any mp_tac mem_bytes_at_agree_window) >>
     strip_tac >> sym_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Resume aggregate_make_tuple_sim[exterior_join]:
  rpt strip_tac >>
  `!name lo sz. local_region ce es1.scopes r name lo sz ==>
      p + n <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 name lo sz` by
       (drule_all vv_post_local_region_backward >> simp[]) >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`name`, `lo`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `!name lo sz. local_region ce es1.scopes t' name lo sz ==>
      p + n <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es1.scopes r name lo sz` by
       (irule local_region_frame >>
        conj_tac
        >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sn`, `es1.scopes`, `t'`] >> asm_rewrite_tac[]) >>
     qpat_x_assum `!name lo sz. local_region ce es1.scopes r name lo sz ==> p + n <= lo \/ _`
       (qspecl_then [`name`, `lo`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any irule vv_post_old_buffer) >>
     reverse conj_tac
     >- (qexists_tac `aid` >> asm_rewrite_tac[]) >>
     rpt strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`n'`, `b'`, `k`] mp_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `FLOOKUP r.vs_allocas aid = SOME (p,n)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac std_ss [vv_post_def] >> strip_tac >>
     qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` irule >>
     asm_rewrite_tac[]) >>
  `FLOOKUP t'.vs_allocas aid = SOME (p,n)` by
    (qpat_x_assum `!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> _` irule >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at p n t'.vs_memory = mem_bytes_at p n r.vs_memory` by
    (qpat_x_assum `!aid p n a k. _` irule >>
     reverse conj_tac >- decide_tac >>
     qexistsl_tac [`aid`, `n`, `p`] >>
     asm_rewrite_tac[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name lo sz. local_region ce es1.scopes r name lo sz ==> p + n <= lo \/ _`
           (qspecl_then [`name`, `lo`, `sz`] mp_tac) >>
         asm_rewrite_tac[] >> decide_tac) >> decide_tac) >>
  `mem_bytes_at p n s.vs_memory = mem_bytes_at p n t'.vs_memory` by
    (qpat_x_assum `!aid p n. _` irule >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name lo sz. local_region ce es1.scopes t' name lo sz ==> _`
           (qspecl_then [`name`, `lo`, `sz`] mp_tac) >>
         asm_rewrite_tac[] >> decide_tac) >>
     asm_rewrite_tac[] >> qexists_tac `aid` >> asm_rewrite_tac[] >>
     fs[ci_mono_def] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Resume aggregate_make_tuple_sim[locals_join]:
  `locals_kept ce es1 r s` by
    (irule locals_kept_trans >> qexistsl_tac [`es1`, `sn`, `t'`] >>
     asm_rewrite_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `r`] >>
  gvs[vv_post_def]
QED

Finalise aggregate_make_tuple_sim

Theorem aggregate_struct_fields_sim:
  !fields ce cx env ty off sa out sb es res es' tvs func inst x b asz s0 ctx.
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  eval_exprs cx (MAP SND fields) es = (res,es') /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_sim_pre ce cx env e st) /\ EVERY (expr_ok ce) (MAP SND fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) ==>
  out = Var x /\
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func ce cx es s)
    (\r. ?vs. res = INL vs /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel func ce cx es' r /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_make_tuple compile_expr ce (MAP SND fields) (Var x) off sa = (out,sb)` by
    metis_tac[compile_struct_lit_as_tuple] >>
  `LENGTH tvs = LENGTH fields` by
    (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  `!vs. res = INL vs ==> LENGTH (MAP FST fields) = LENGTH vs` by
    (rpt strip_tac >> gvs[] >> drule eval_exprs_length >> simp[]) >>
  drule_all aggregate_make_tuple_sim >>
  simp[fields_in_memory_tuple, listTheory.MAP_ZIP, SF CONJ_ss]
QED

Theorem compile_make_array_elems_as_tuple:
  !args idx.
  EVERY (\e. expr_type e = elem_ty) args ==>
  compile_make_array_elems cfn ce args elem_ty (type_memory_bytes ce elem_ty)
    header buf idx =
  compile_make_tuple cfn ce args buf
    ((if header then 32 else 0) + idx * type_memory_bytes ce elem_ty)
Proof
  Induct >> simp[compile_make_array_elems_def, compile_make_tuple_def] >>
  rpt strip_tac >> Cases_on `header` >>
  pure_rewrite_tac[COND_CLAUSES, arithmeticTheory.ADD_CLAUSES,
    arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES,
    GSYM arithmeticTheory.ADD_ASSOC] >> REFL_TAC
QED

Theorem aggregate_make_array_elems_sim:
  !args ce cx env elem_ty tv header idx off sa out sb es res es' func inst x b asz s0 ctx.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  eval_exprs cx args es = (res,es') /\ expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_sim_pre ce cx env e st) /\ EVERY (expr_ok ce) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) ==>
  out = Var x /\
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func ce cx es s)
    (\r. ?vs. res = INL vs /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel func ce cx es' r /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb)` by
    metis_tac[compile_make_array_elems_as_tuple] >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (irule OPT_MMAP_uniform_map >> goal_assum (drule_at Any) >> simp[]) >>
  `off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= asz` by
    metis_tac[type_memory_size_list_replicate] >>
  `!vs. res = INL vs ==> LENGTH args = LENGTH vs` by
    (rpt strip_tac >> gvs[] >> drule eval_exprs_length >> simp[]) >>
  `!vs p mem. res = INL vs ==>
    (tuple_in_memory vs (REPLICATE (LENGTH args) tv) p mem <=>
     elems_in_memory vs p tv mem)` by
    (rpt strip_tac >>
     `LENGTH args = LENGTH vs` by metis_tac[] >>
     pop_assum SUBST1_TAC >> simp[tuple_in_memory_replicate_elems]) >>
  drule_all aggregate_make_tuple_sim >>
  simp[type_memory_size_list_replicate, SF CONJ_ss]
QED

Theorem aggregate_make_array_start_sim:
  !args ce cx env elem_ty tv stride header sa out sb es res es' func inst x b asz s0 ctx.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty stride header (Var x) 0 sa = (out,sb) /\
  eval_exprs cx args es = (res,es') /\ expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_sim_pre ce cx env e st) /\ EVERY (expr_ok ce) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) ==>
  out = Var x /\
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func ce cx es s)
    (\r. ?vs. res = INL vs /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+(if header then 32 else 0) \/
         b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> irule aggregate_make_array_elems_sim >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`elem_ty`, `header`, `0`] >> gvs[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem aggregate_emit_mstore_sim:
  emit_void MSTORE [pop; value] sa = ((),sb) /\
  eval_operand pop s0 = SOME addr /\ eval_operand value s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\r. r = (mstore (w2n addr) w s0 with
      vs_inst_idx := LENGTH sb.cs_current_insts)) R
Proof
  strip_tac >> irule frag_exec_run_inst_seq >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  gvs[cs_extends_def, same_blocks_def, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def] >>
  rpt strip_tac >> disj1_tac >>
  drule_all exprSimLiteralBufferTheory.literal_emit_mstore_run >>
  strip_tac >> qexists_tac `mstore (w2n addr) w s0` >> gvs[]
QED

Theorem aggregate_make_array_sim:
  !args ce cx env elem_ty tv stride header sa out sb es res es' func inst x b asz s0 ctx.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  eval_exprs cx args es = (res,es') /\ expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_sim_pre ce cx env e st) /\ EVERY (expr_ok ce) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) ==>
  out = Var x /\
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func ce cx es s)
    (\r. ?vs. res = INL vs /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      mp_tac (Q.INST [`header` |-> `F`, `stride` |-> `type_memory_size tv`]
        (SPEC_ALL aggregate_make_array_start_sim)) >> simp[]) >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_make_array_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_void MSTORE _ sa = ((),sm)` >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `compile_make_tuple compile_expr ce args (Var x) 32 sm = (out,sb)` by
    (mp_tac (Q.INST [`idx` |-> `0`, `header` |-> `T`,
       `cfn` |-> `compile_expr`, `buf` |-> `Var x`]
       (SPEC_ALL compile_make_array_elems_as_tuple)) >> simp[] >>
     disch_then SUBST_ALL_TAC >> simp[]) >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `out = Var x` by metis_tac[exprOperandVarTheory.compiler_make_array_elems_result] >>
  gvs[] >>
  reverse (Cases_on `stmt_state_rel func ce cx es s0`)
  >- simp[frag_exec_def] >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa sb P Q R` >>
  qabbrev_tac `s1 = mstore b (n2w (LENGTH args)) s0 with
    vs_inst_idx := LENGTH sm.cs_current_insts` >>
  suspend "header_run"
QED

Resume aggregate_make_array_sim[header_run]:
  `b < dimword (:256)` by decide_tac >>
  `frag_exec ctx sa sm (\s. s = s0) (\r. r = s1) R` by
    (`eval_operand (Var x) s0 = SOME (n2w b) /\
      eval_operand (Lit (n2w (LENGTH args))) s0 = SOME (n2w (LENGTH args))` by
       simp[venomStateTheory.eval_operand_def] >>
     drule_all aggregate_emit_mstore_sim >> simp[Abbr `s1`]) >>
  irule frag_exec_seq_pointwise >> qexistsl_tac [`\r. r = s1`, `sm`] >>
  conj_tac >- (simp[] >> suspend "header_suffix") >>
  conj_tac >- fs[ci_mono_def] >>
  conj_tac >- fs[ci_mono_def] >>
  drule frag_exec_weaken >>
  disch_then irule >> simp[Abbr `P`]
QED

Resume aggregate_make_array_sim[header_suffix]:
  `stmt_state_rel func ce cx es s1` by
    (simp[Abbr `s1`, stmt_state_rel_inst_idx] >>
     irule exprSimLiteralBufferTheory.literal_mstore_state_rel >>
     simp[] >> qexistsl_tac [`b`, `asz`] >>
     reverse conj_tac >- decide_tac >> simp[] >> rpt strip_tac >>
     `not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       fs[stmt_state_rel_def, state_rel_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >> simp[regions_disjoint_def]) >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `not_fresh_at sm x /\ inst.inst_id < sm.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono,
      arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `lookup_var x s1 = SOME (n2w b) /\
   FLOOKUP s1.vs_allocas inst.inst_id = SOME (b,asz)` by
    fs[Abbr `s1`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s0` |-> `s1`, `header` |-> `T`,
    `stride` |-> `type_memory_size tv`, `out` |-> `Var x`]
    (SPEC_ALL aggregate_make_array_start_sim)) >>
  simp[] >> suspend "header_post"
QED

Resume aggregate_make_array_sim[header_post]:
  strip_tac >> drule frag_exec_weaken >> disch_then irule >> simp[] >>
  qx_gen_tac `r` >> strip_tac >>
  qpat_x_assum `EVERY _ args` kall_tac >>
  qpat_x_assum `evaluate_type _ _ = _` kall_tac >>
  qpat_x_assum `type_memory_bytes _ _ = _` kall_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` kall_tac >>
  qpat_x_assum `!e st. MEM e args /\ _ ==> _` kall_tac >>
  qpat_x_assum `EVERY _ args` kall_tac >>
  qpat_x_assum `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_make_tuple _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `frag_exec _ sm sb _ _ _` kall_tac >>
  qpat_x_assum `frag_exec _ sa sm _ _ _` kall_tac >>
  simp[Abbr `Q`] >> suspend "header_frames"
QED

Resume aggregate_make_array_sim[header_frames]:
  conj_tac
  >- (`mem_bytes_at b 32 r.vs_memory = mem_bytes_at b 32 s1.vs_memory` by
        (qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
         simp[] >> decide_tac) >>
      `mem_word_at b r.vs_memory = mem_word_at b s1.vs_memory` by
        metis_tac[mem_word_at_def, mem_bytes_at_def] >>
      simp[Abbr `s1`, mstore_mem_word_at_same]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[Abbr `s1`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      simp[Abbr `s1`, venomStateTheory.mstore_def]) >>
  conj_tac >- suspend "header_interior" >>
  conj_tac >- suspend "header_exterior" >>
  suspend "header_locals"
QED

Resume aggregate_make_array_sim[header_interior]:
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s1.vs_memory` by
    (qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     simp[] >> decide_tac) >>
  simp[] >> simp[Abbr `s1`] >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume aggregate_make_array_sim[header_exterior]:
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s1.vs_memory` by
    (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >>
     fs[Abbr `s1`, venomStateTheory.mstore_def, ci_mono_def,
        local_region_def, venomStateTheory.lookup_var_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[] >> simp[Abbr `s1`] >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume aggregate_make_array_sim[header_locals]:
  `locals_kept ce es s0 s1` by
    (irule locals_kept_regions >> rpt strip_tac >>
     simp[Abbr `s1`] >> irule mstore_mem_bytes_at_disjoint >>
     `not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       fs[stmt_state_rel_def, state_rel_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def] >> decide_tac) >>
  irule locals_kept_trans >> qexistsl_tac [`es`, `sa`, `s1`] >>
  simp[] >> rpt strip_tac >>
  gvs[Abbr `s1`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def]
QED

Finalise aggregate_make_array_sim
