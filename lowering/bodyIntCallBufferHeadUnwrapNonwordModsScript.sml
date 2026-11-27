(* The nonword unwrap keeps the destination row at the original ALLOCA site. *)
Theory bodyIntCallBufferHeadUnwrapNonwordMods
Ancestors
  bodyIntCallBufferHeadCutsMods bodyIntCallBufferNonwordInputMods
  bodyAnnNonwordReadTypesMods bodyFullPostsMods exprSimMemorySource
  gasExplicitSites fragGasOriginPtr vyperStorageFootprint
  vyperInterpreter vyperState venomState compileEnv loweringPosts bodyPtrDefs
  loweringStateRelDefs words arithmetic

val _ = Parse.hide "base";

Theorem intcall_buffer_head_unwrap_nonword_mods:
  compile_expr cenv ty e si = (vv,ci) /\
  unwrap_value cenv vv ca = (opn,cu) /\
  fn_has_code ca cu func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv si /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods cenv cx env e esi /\
  eval_expr cx e (esi with gas_obs := gs) = (INL raw,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\ ~is_word_type dty /\
  intcall_buffer_head_alloc_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    mods cenv cx env st0 (si,esi,s,G,tn) (ci,mid,u,Gu,tu) (ca,mid,a,Ga,ta)
    e dty raw vv buf aid dst base cap v ==>
  ?z Gz tz. intcall_buffer_head_unwrap_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx st0 (si,esi,s,G,tn) (ca,mid,a,Ga,ta) (cu,mid,z,Gz,tz)
    e dty raw vv aid dst base cap v opn
Proof
  strip_tac >>
  qhdtm_x_assum `intcall_buffer_head_alloc_post_mods` mp_tac >>
  pure_rewrite_tac[intcall_buffer_head_alloc_post_mods_def] >> strip_tac >>
  qpat_x_assum `aid = ci.cs_next_id` SUBST_ALL_TAC >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  qpat_x_assum `intcall_buffer_head_edge_mods _ (ci,_,_,_,_) _` mp_tac >>
  pure_rewrite_tac[intcall_buffer_head_edge_mods_def] >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post_mods H ctx func cenv cx e esi si ca s mid raw vv a /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Ga ta a` by
    (gen_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> storage_well_formed_on _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok cenv e x Ga a` by simp[] >>
  `!w. eval_operand (vv_operand vv) a = SOME w ==>
    eval_operand (vv_operand vv) u = SOME w` by simp[] >>
  `!nm b n. local_region cenv mid.scopes u nm b n ==>
    local_region cenv mid.scopes a nm b n` by simp[] >>
  `!nm b n. local_region cenv mid.scopes a nm b n ==>
    base + MAX 32 (type_memory_bytes cenv dty) <= b \/ b+n <= base` by
    (pure_rewrite_tac[GSYM regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  drule intcall_buffer_nonword_input_mods >>
  disch_then (fn th => qpat_assum `unwrap_value _ _ _ = _`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_expr _ _ _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qhdtm_assum `ghost_kept_at`
    (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (mp_then (Pat `vv_post_mods`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers Ga ta dst a _`
    (mp_then (Pat `ptr_covers`) mp_tac th)) >>
  disch_then (fn th => qhdtm_assum `vv_at`
    (mp_then (Pat `vv_at`) mp_tac th)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`v'`,`z`,`Gz`,`tz`,`w`] (map_every assume_tac o CONJUNCTS)) >>
  `v' = v` by (qpat_x_assum `read_result cx raw mid = (INL v',mid)` mp_tac >> simp[]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  qpat_assum `!x. not_fresh_at ca x ==> lookup_var x z = _ /\ _`
    (drule_then strip_assume_tac) >>
  `base + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next` by decide_tac >>
  `w2n (n2w base : bytes32) = base` by
    (`base < dimword (:256)` by decide_tac >> simp[LESS_MOD]) >>
  qexistsl [`z`,`Gz`,`tz`] >>
  simp[intcall_buffer_head_unwrap_post_mods_def,intcall_buffer_head_edge_mods_def] >>
  conj_tac >-
   (qpat_x_assum `!aid b n. _ ==> mem_bytes_at b n z.vs_memory = _ /\ _` mp_tac >>
    simp[AC CONJ_COMM CONJ_ASSOC,AC ADD_COMM ADD_ASSOC]) >>
  qpat_x_assum `if is_bytestring_type dty then _ else _` mp_tac >>
  Cases_on `is_bytestring_type dty` >> simp[]
  >- (disch_then (qx_choosel_then [`src`,`len`,`stv`] (map_every assume_tac o CONJUNCTS)) >>
      qexistsl [`stv`,`src`,`w`,`len`] >> simp[]) >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  qexistsl [`stv`,`dtv`] >> simp[]
QED
