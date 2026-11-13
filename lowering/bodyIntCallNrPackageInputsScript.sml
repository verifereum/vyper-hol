(* Flag-general projections of the frozen actual-package entry contract. *)
Theory bodyIntCallNrPackageInputs
Ancestors
  bodyIntCallSeamDefs bodyIntCallEntryInputs bodyIntCallInvokeEntry
  bodyIntCallRootFrame bodyIntCallResourceSpans compileEnv venomState
  venomMemDefs exprLoweringProps finite_map list words arithmetic

Theorem intcall_entry_package_inputs_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) ==>
  label = lbl /\
  (has_rb <=> nret = 0 /\
    cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  state_rel func ce cx (es1 with scopes := []) t /\
  internal_immutable_regions ce cx es1 t.vs_alloca_next /\
  internal_args_rel ce params penv (if has_rb then 1 else 0) argv
    t.vs_alloca_next t.vs_memory /\
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `_ /\ _ ==> st2 = _ /\ _` kall_tac >>
  qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _` kall_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _`
    (mk_asm "package") >>
  gvs[] >> asm_x "package" drule >> disch_then drule >>
  disch_then assume_tac >> first_x_assum drule >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_entry_package_separation_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) ==>
  (!i po psz.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
     ?aid off asz.
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
               inst.inst_id = aid) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
       off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
       w2n (EL ((if has_rb then 1 else 0) + i) argv) + psz <= off + asz) /\
  (has_rb ==> !i po psz.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
     regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
       (w2n (EL (1 + i) argv)) psz) /\
  (ce.ce_is_ctor ==> !i po psz nm tv iv io.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
     FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables ce.ce_module imms) nm =
       SOME (tv,iv) ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
  (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables ce.ce_module imms) nm =
       SOME (tv,iv) ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (HD argv)) (type_memory_size rtv))
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `_ /\ _ ==> st2 = _ /\ _` kall_tac >>
  qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _` kall_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _`
    (mk_asm "package") >>
  gvs[] >> asm_x "package" drule >> disch_then drule >>
  disch_then assume_tac >> first_x_assum drule >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_entry_buffer_allocation_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (0,rbs,pvs) /\
  cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT ==>
  w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next /\
  ?aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    off <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= off + asz
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _` kall_tac >>
  gvs[] >>
  `off < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def,
        alloca_room_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP _ _ = SOME _ ==> _` drule >>
     strip_tac >> decide_tac) >>
  goal_assum (drule_at (Pat `FLOOKUP t.vs_allocas _ = SOME _`)) >>
  simp[LESS_MOD] >> decide_tac
QED

Theorem intcall_entry_root_geometry_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  (!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) ==>
  (!a k. P a k ==> a + k <= t.vs_alloca_next) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (has_rb ==> w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next /\
    (!b z. staged b z ==> regions_disjoint (w2n (HD argv)) (type_memory_size rtv) b z) /\
    (!a k. P a k ==> regions_disjoint a k (w2n (HD argv)) (type_memory_size rtv)))
Proof
  strip_tac >> drule_all intcall_entry_package_separation_nr >> strip_tac >>
  drule_all intcall_entry_package_inputs_nr >> strip_tac >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (match_mp_tac (Q.INST [`caller` |-> `t`, `n` |-> `sa.cs_next_id`,
        `m` |-> `sb.cs_next_id`, `argbase` |-> `if has_rb then 1 else 0`]
        internal_parameter_windows_protected) >>
      simp[IgnAsm `has_rb <=> _`] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!i po psz. _ ==> ?aid off asz. _` drule_all >>
          strip_tac >> goal_assum (drule_at Any) >> gvs[ADD_COMM]) >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ _ ==> _`
        drule_all >> simp[]) >>
  strip_tac >>
  `nret = 0 /\ cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT`
    by metis_tac[] >>
  qpat_x_assum `nret = 0` SUBST_ALL_TAC >>
  drule_all intcall_entry_buffer_allocation_nr >> strip_tac >>
  conj_tac >- simp[] >> conj_tac
  >- metis_tac[internal_parameter_windows_buffer] >>
  rpt strip_tac >>
  irule protected_span_subregion >>
  qexistsl [`P`, `off`, `asz`] >> simp[ADD_COMM] >>
  fs[] >> metis_tac[]
QED
