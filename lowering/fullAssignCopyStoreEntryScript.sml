(* The actual RHS buffer and equal-type store select one runtime endpoint. *)
Theory fullAssignCopyStoreEntry
Ancestors
  fullAssignCopyCompose fullStoreSlotsRun stmtLowering bodySim
  exprSimHypsDefs vyperTypeSystem vyperTyping bodyPtrDefs
  compileEnv fragExec

Theorem topcopy_assign_store_endpoint:
  ~cx.txn.is_static /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign target e) = SOME env' /\
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
  0 < type_memory_size tv /\
  slot + type_slot_size tv <= dimword(:256) /\
  value_has_type tv v /\
  expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ptr_buf_ok cenv e op G t /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  local_ptrs_reserved cenv sa /\
  compile_assign_value cenv (Lit (n2w slot))
    (if tr then LocTransient else LocStorage) op F sl
    (expr_type e) (expr_type e) (type_memory_bytes cenv (expr_type e)) sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?writes root sw Gf tf u ks.
    encode_value tv v = SOME writes /\ op = Var root /\
    lookup_var root t = SOME sw /\
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize t u =
      FOLDL (\q k. (if tr then tstore else sstore) (n2w slot+n2w k)
        (mload (w2n sw+32*k) t) q) t ks /\
    u.vs_memory=t.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (n2w slot+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u=lookup_var x t /\
      FLOOKUP Gf x=FLOOKUP G x /\ op_taint tf (Var x)=op_taint tn (Var x)) /\
    u.vs_allocas=t.vs_allocas /\ u.vs_alloca_next=t.vs_alloca_next /\
    u.vs_labels=t.vs_labels /\ u.vs_call_ctx=t.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts /\
    (!H cx env ee rootk region path delta.
      expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee t /\
      MEM (tr,rootk,region) (FST H) /\ regions_consistent (FST H) /\
      storage_locks_separated (FST H) (SND H) /\
      storage_subregion region path delta tv /\
      w2n (n2w slot:256 word) = w2n rootk + delta /\ 0 < type_slot_size tv /\
      well_formed_type_value tv ==>
      stmt_state_rel H ctx func cenv cx
        (set_storage cx ee tr (apply_writes (n2w slot) writes (get_storage cx ee tr)))
        (store_copy_normalize t u))
Proof
  strip_tac >>
  `assignable_type (get_tenv cx) (expr_type e)` by
    (fs[type_stmt_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]) >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  drule_all topcopy_store_entry_resources >>
  disch_then (qspec_then `n2w slot` strip_assume_tac) >> gvs[] >>
  `compile_store_slots cenv (Var root) (Lit (n2w slot)) (expr_type e) tr sm = ((),sb)` by
    (Cases_on `tr` >> fs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (fs[body_inv_def, expr_sim_inv_def] >> metis_tac[]) >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `w2n (n2w slot:256 word) + type_slot_size tv <= dimword(:256)` by
    (simp[] >> `slot MOD dimword(:256) <= slot` by
       (irule arithmeticTheory.MOD_LESS_EQ >> simp[]) >> decide_tac) >>
  `op_prov G (Lit (n2w slot)) = NONE /\
   (!x. Lit (n2w slot:256 word) = Var x ==> not_fresh_at sm x)` by
    simp[ptrDisciplineTheory.op_prov_def] >>
  `w2n w + type_memory_size tv < dimword(:256)` by decide_tac >>
  drule_all store_slots_encoded_endpoint >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM, wordsTheory.w2n_n2w]
QED
