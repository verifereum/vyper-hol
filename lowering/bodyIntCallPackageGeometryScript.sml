(* Frozen-entry geometry for the root frame's exact protected windows. *)
Theory bodyIntCallPackageGeometry
Ancestors
  bodyIntCallPackageInputs bodyIntCallSeamDefs bodyIntCallRootFrame
  bodyIntCallResourceSpans compileEnv venomState venomMemDefs
  exprLoweringProps finite_map list words arithmetic

Theorem intcall_entry_buffer_allocation:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
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

Theorem intcall_entry_root_geometry:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([] : expr list),ret,ss)) =
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
  strip_tac >> drule_all intcall_entry_package_separation >> strip_tac >>
  drule_all intcall_entry_package_inputs >> strip_tac >>
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
  drule_all intcall_entry_buffer_allocation >> strip_tac >>
  conj_tac >- simp[] >> conj_tac
  >- metis_tac[internal_parameter_windows_buffer] >>
  rpt strip_tac >>
  irule protected_span_subregion >>
  qexistsl [`P`, `off`, `asz`] >> simp[ADD_COMM] >>
  fs[] >> metis_tac[]
QED
