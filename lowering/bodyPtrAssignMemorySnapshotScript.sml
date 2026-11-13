(* A nonbytes memory value is snapshotted at its physical layout. *)
Theory bodyPtrAssignMemorySnapshot
Ancestors
  assignBasePtrStaging bodyDeclMemoryCore exprSimProps loweringPosts
  exprLowering exprLoweringProps loweringHalt exprSimAlloc fragExec
  typedMemoryCopy compileEnv context loweringStateRelDefs bodyPtrDefs
  venomState venomInst valueEncoding valueEncodingDefs words list finite_map

Theorem snapshot_memory_nonbytes_counted_ptr:
  !cenv ty vv saved sa sb ctx fn cx es s G tn d D PG tv v src w va vb.
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    (vv = StackValue ty (Var src) \/
     ?pp. vv = LocatedValue ty pp /\ pp.ptr_location = LocMemory /\
       pp.ptr_operand = Var src) /\
    compile_snapshot_vv cenv T vv sa = (saved,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ val_wf tv v /\
    expr_val_at cenv cx ty va vb es v (Var src) s /\
    eval_operand (Var src) s = SOME w /\
    ptr_covers G tn src s (type_memory_size tv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?out t H tt.
      saved = LocatedValue ty (mk_ptr (Var out) LocMemory) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
      stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tt t /\
      ghost_kept cenv es sa G tn s H tt /\
      expr_val_own cenv cx ty sa sb es v (Var out) t /\
      pure_frame cenv fn es sa s t /\
      ptr_covers H tt out t (type_memory_size tv) /\
      (!m. mem_agree_outside tt.t_mem t.vs_memory m ==>
        ?a. eval_operand (Var out) t = SOME a /\
          val_in_memory tv v (w2n a) m) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_type vv = ty /\ !sc. unwrap_value cenv vv sc = (Var src,sc)` by
    (qpat_x_assum `vv = _ \/ _` strip_assume_tac >>
     gvs[vv_type_def, unwrap_value_def, comp_return_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_size tv) sa` >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  Cases_on `compile_copy_memory buf.buf_operand (Var src) (type_memory_size tv) sm` >>
  rename1 `compile_copy_memory _ _ _ sm = (ans,sc)` >> Cases_on `ans` >>
  `saved = LocatedValue ty (mk_ptr buf.buf_operand LocMemory) /\ sb = sc` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def, compile_materialize_vv_def,
       compile_store_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]) >>
  qpat_x_assum `sb = sc` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  drule body_scratch_alloc_operand >> strip_tac >>
  qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
  `buf.buf_operand = Var dst` by simp[Abbr `dst`] >>
  `not_local_ptr cenv es.scopes dst` by
    (simp[Abbr `dst`] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> dst` by
    (simp[Abbr `dst`, not_fresh_at_def] >> metis_tac[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> x <> dst) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> x <> dst) /\
   src <> dst` by metis_tac[] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  `compile_copy_memory (Var dst) (Var src) (type_memory_size tv) sm = ((),sb)` by fs[] >>
  mp_tac (Q.SPECL [`ctx`, `fn`, `d`, `cenv`, `cx`, `es`, `sa`, `sm`,
    `sb`, `buf`, `type_memory_size tv`, `s`, `PG`, `G`, `tn`, `D`, `sa`,
    `ty`, `va`, `vb`, `v`, `src`, `dst`, `tv`, `w`]
    assign_base_alloc_scratch_staging_ptr) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`u`,`a`,`Gi`,`ti`,`t`,`H`,`tt`]
    (map_every assume_tac o CONJUNCTS)) >> suspend "staged"
QED

Resume snapshot_memory_nonbytes_counted_ptr[staged]:
  `sa.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[ci_mono_def]) >>
  `!b len. regions_disjoint b len (w2n a) (type_memory_size tv) ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `typed_copy_state_frame _ _ _ u t` mp_tac >>
     simp[typed_copy_state_frame_def, typed_copy_frame_def] >> strip_tac >>
     first_x_assum irule >> fs[regions_disjoint_def]) >>
  `expr_val_own cenv cx ty sa sb es v (Var dst) t` by
    (rewrite_tac[expr_val_own_def] >> qx_gen_tac `rtv` >> strip_tac >>
     `rtv = tv` by fs[] >> qpat_x_assum `rtv = tv` SUBST_ALL_TAC >>
     qexists_tac `a` >> simp[] >> disj1_tac >>
     qexistsl_tac [`sa.cs_next_id`,`w2n a`,`type_memory_size tv`] >>
     fs[] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def]) >>
  `pure_frame cenv fn es sa s t` by
    (match_mp_tac (Q.SPECL [`cenv`,`fn`,`es`,`sa`,`s`,`t`,`sa.cs_next_id`,
       `[Lit (n2w (type_memory_size tv))]`,`[dst]`,`w2n (a:256 word)`,`type_memory_size tv`]
       pure_frame_fresh_alloca) >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [dst])
       (fn_insts fn)` by
       (simp[Abbr `dst`] >> drule_all buffer_alloc_code >> simp[]) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!b len. regions_disjoint _ _ _ _ ==> _` irule >>
     `local_region cenv es.scopes t n lb lsz` by fs[] >>
     qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!q. q <> Var dst ==> _` (qspec_then `Var x` mp_tac) >>
     qpat_x_assum `ghost_kept cenv es sa G tn s H tt` mp_tac >>
     simp[ghost_kept_def, eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`dst`,`t`,`H`,`tt`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> qexists_tac `a` >> simp[]
QED

Finalise snapshot_memory_nonbytes_counted_ptr
