(* Counted memory simulation of a declaration of a bytestring type: the
   local's ALLOCA, the right-hand side, and the copy of its value into the
   local, staged through a buffer of the right-hand side's lowered size when
   the value is in memory.  The bytestring part of stmtSimDeclMem's
   compile_annassign_memory_widen_stmt_frag. *)
Theory bodyDeclBytesMemory
Ancestors
  bodyDeclCopyMemory bodyDeclMemoryCompose bodyDeclMemoryCounted
  bodyDeclMemoryCore bodyMemoryPreds stmtSimDeclCompose stmtSimDeclSource
  stmtSimDeclStore stmtSimDeclMem stmtSimDecl exprSimMemDefs exprSimProps
  exprSimBufferStore bodyRhsRoomMemory bodyMemoryDefs fragGasMode fragGasPathMem fragGasPath
  gasSummary gasOutcome loweringPosts exprSimDefs stmtSimDefs stmtSimProps
  loweringSlice exprLoweringProps exprOperandVar localPtrsProps freshWrites
  valueTypingMemoryProps valueCopyBytes bodySim exprSimHypsDefs emitHelper emitHelperProps fragExec
  venomInst venomState exprLowering stmtLowering context compileEnv
  vyperInterpreter vyperState list rich_list finite_map
Libs
  monadsyntax

(* A bytestring type takes memory. *)
Theorem bytestring_tv_size_pos[local]:
  !t tenv tv.
    is_bytestring_type t /\ evaluate_type tenv t = SOME tv ==>
    0 < type_memory_size tv
Proof
  Cases >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  rw[vyperValueTheory.evaluate_type_def] >> simp[valueEncodingTheory.type_memory_size_def]
QED

(* The staged copy into a bytestring destination: a buffer of the source's
   own size, the copy of the source into it, and the store at the
   destination's type (compile_store_memory copies a bytestring the same
   way whatever the source's bound). *)
Theorem assign_memory_widen_body_code[local]:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty bytes sa = ((),sb) /\ fn_has_code sa sb func /\
  is_bytestring_type dty ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm =
      ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty dty sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func
Proof
  strip_tac >>
  `?buf sm sn.
     compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
     compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm =
       ((),sn) /\
     compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     metis_tac[pairTheory.PAIR]) >>
  `compile_store_memory ce buf.buf_operand dst dty dty sn = ((),sb)` by
    metis_tac[compile_store_memory_bytestring_src] >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[] >>
  `cs_extends sa sm` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
     strip_tac >> metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >>
     simp[cs_extends_def, same_blocks_def] >> strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (drule buffer_store_memory_shape >>
     simp[cs_extends_def, same_blocks_def] >> strip_tac >> simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

(* A bytestring value in memory, staged through a buffer of its lowered
   type's size and stored into a declared bytestring local.  The staging
   copy reads the lowered type's whole size from the source, so the source
   region must reach that far. *)
Theorem annassign_memory_assign_widen_body_path:
  !ctx func cenv cx es s id p sz w inst v tyv ltv sc rest a src ty lt sa sb
   sw d bytes.
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty lt bytes sa = ((), sb) /\
    is_bytestring_type ty /\ is_bytestring_type lt /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    evaluate_type (get_tenv cx) lt = SOME ltv /\
    value_has_type tyv v /\ value_has_type ltv v /\
    val_in_memory ltv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_bytes cenv lt = type_memory_size ltv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_size ltv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size ltv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v;
                        popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_memory_widen_body_code >> strip_tac >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func` by metis_tac[fn_has_code_split] >>
  `val_wf ltv v /\ val_wf tyv v` by simp[value_has_type_memory_wf] >>
  `val_footprint ltv v <= type_memory_bytes cenv lt` by
    (simp[] >> irule val_footprint_le >> simp[]) >>
  `type_memory_bytes cenv lt < dimword (:256)` by simp[] >>
  `w2n sw + type_memory_bytes cenv lt <= s.vs_alloca_next` by simp[] >>
  drule_all compile_scratch_prefix_body_path >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule_all body_scratch_prefix_shape >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (drule body_scratch_alloc_operand >> strip_tac >>
     drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
     strip_tac >>
     drule buffer_copy_memory_shape >> strip_tac >>
     qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
   w2n w + type_memory_size tyv <= t.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `val_in_memory tyv v (w2n w') t.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `w2n w' + val_store_size tyv v <= t.vs_alloca_next` by
    (`val_store_size tyv v = val_store_size ltv v` by
       metis_tac[bytestring_val_store_size_eq] >>
     `val_store_size ltv v <= type_memory_size ltv` by
       metis_tac[val_store_size_le] >>
     fs[]) >>
  `not_fresh_at sn p` by simp[] >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _`
    (mp_then (Pos hd) mp_tac annassign_memory_store_body_path) >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`, `t`, `id`, `sz`, `w`,
    `inst`, `v`, `tyv`, `sc`, `rest`, `a`, `w'`, `d`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `t2:venom_state` strip_assume_tac) >>
  qexists_tac `t2` >>
  `gas_path_mem ctx func s (0 + 0) (OK t2)` by
    (irule gas_path_mem_then >> qexists_tac `t` >> simp[]) >>
  fs[] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* The copy into a declared bytestring local after its right-hand side,
   from the state s the right-hand side's fragment ends in.  The value is
   laid out the same at every bytestring type it has; a value staged
   through a buffer is read at its lowered type's size, which the premise
   on a memory-located value bounds. *)
Theorem annassign_bytes_post_path_mem:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v tyv etv ltv
   vtyp sc rest a loc bytes d.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_store_bound cx (expr_type e) v op s /\
    (loc = SOME LocMemory ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size ltv <= s.vs_alloca_next) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
    local_ptrs_reserved cenv sa /\
    is_bytestring_type vtyp /\ is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_size ltv < dimword (:256) /\
    compile_assign_value cenv (Var p) LocMemory op F loc vtyp
      (lowered_value_type cenv e) bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv sb s /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es1 with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v;
                        popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sf t /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> drule_all (GEN_ALL compile_lower_value_var) >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `~is_word_type (expr_type e) /\ ~is_word_type vtyp` by
    metis_tac[is_bytestring_word_type] >>
  `val_wf tyv v` by simp[value_has_type_memory_wf] >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory etv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `val_in_memory tyv v (w2n sw) s.vs_memory /\
   val_in_memory ltv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_store_size tyv v = val_store_size etv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `0 < type_memory_size etv` by metis_tac[bytestring_tv_size_pos] >>
  `w2n sw + val_store_size tyv v <= s.vs_alloca_next` by
    (`0 < val_store_size etv v` by simp[val_store_size_pos] >>
     qpat_x_assum `expr_store_bound _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     disch_then (qspecl_then [`etv`, `sw`] mp_tac) >> gvs[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  Cases_on `loc = SOME LocMemory`
  >- (gvs[] >>
      drule annassign_memory_assign_widen_body_path >>
      disch_then (qspecl_then [`ctx`, `func`, `cx`, `es1`, `s`, `id`, `sz`,
        `w`, `inst`, `v`, `tyv`, `ltv`, `sc`, `rest`, `a`, `sw`, `d`] mp_tac) >>
      simp[]) >>
  `compile_store_memory cenv op (Var p) vtyp vtyp sb = ((),sf)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def] >>
     metis_tac[compile_store_memory_bytestring_src]) >>
  drule annassign_memory_store_body_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es1`, `s`, `id`, `sz`,
    `w`, `inst`, `v`, `tyv`, `sc`, `rest`, `a`, `sw`, `d`] mp_tac) >>
  simp[]
QED

(* x: T = e for a bytestring type T, where e has a bytestring type and is
   lowered at one (a literal at its own length, say), and is not the
   empty-value form.  e's values have T, e's type and e's lowered type; the
   local's buffer is T's size, which leaves the 64 bytes of a bytestring
   copy's rounding below 2 ** 256.  The right-hand side's fragment is as
   expr_sim_mem's, and when its value is in memory, the source region
   reaches the lowered type's size: compile_assign_value stages the value
   through a buffer of that size, copying the whole of it. *)
Theorem compile_annassign_bytes_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id vtyp e es tyv etv ltv.
    cenv.ce_alloca_locals /\
    is_bytestring_type vtyp /\ is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    type_memory_size ltv < dimword (:256) /\
    (!gs v es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL v, es1) ==>
       value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !sa sV sb vv op s0.
         compile_expr c (expr_type e) e sa = (vv, sV) /\
         unwrap_value c vv sV = (op, sb) /\
         fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
         local_ptrs_reserved c sa /\
         gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
         stmt_state_rel ctx func c cx es s0 /\
         alloca_history func s0 /\ ~s0.vs_halted /\
         s0.vs_current_bb = sa.cs_current_bb /\
         s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
         gas_outcome T (cx_tops cx) (ctx, func)
           (bind (eval_expr cx e) (read_result cx)) (es, s0)
           (\res ee t. ?v. res = INL v /\
             expr_post ctx func c cx e es sa sb s0 ee v op t /\
             expr_store_bound cx (expr_type e) v op t /\
             (vv_location vv = SOME LocMemory ==>
              !sw. eval_operand op t = SOME sw ==>
                   w2n sw + type_memory_size ltv <= t.vs_alloca_next) /\
             t.vs_current_bb = sb.cs_current_bb /\
             t.vs_inst_idx = LENGTH sb.cs_current_insts /\
             alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
           (\res ee r. expr_exit res r)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. declare_local _ _ _ _ = _ ==> !sa sV. _` drule >>
  strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  `~is_word_type vtyp /\ ~is_word_type (expr_type e)` by
    metis_tac[is_bytestring_word_type] >>
  `0 < type_memory_size tyv` by
    metis_tac[bytestring_memory_bytes_positive] >>
  `~(has_length_word vtyp /\ is_empty_value_expr e)` by metis_tac[] >>
  drule_all annassign_copy_parts_mem >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `!ty. type_memory_bytes c ty = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!e. lowered_value_type c e = _` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `cs_extends sA sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[compile_assign_memory_widen_appends, cs_appends_def] >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sb func` by
    (qspecl_then [`sA`, `sB`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sa sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    metis_tac[] >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by
    simp[] >>
  `type_memory_bytes cenv vtyp < dimword (:256)` by decide_tac >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  drule annassign_admissible_type >> strip_tac >>
  `tyv' = tyv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv' = tyv` SUBST_ALL_TAC >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  qpat_x_assum `!sa sV sb vv op s0. _`
    (qspecl_then [`sA`, `sV`, `sB`, `vv`, `op`, `salloc`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `~block_is_terminated sb` by
    (drule_at (Pos last) compile_assign_value_memory_widen_open >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sA x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     drule emit_inst_extends >> simp[]) >>
  irule annassign_rhs_outcome_mem >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  qexists_tac `tyv` >>
  qpat_assum `evaluate_type (get_tenv cx) vtyp = SOME tyv`
    (fn th => simp[PULL_EXISTS, th]) >>
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas st.cs_next_id =
     SOME (w2n w, type_memory_bytes cenv vtyp) /\
   salloc.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> metis_tac[]) >>
  `return_buf_frame d c sB t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`c`, `salloc`, `sA`] >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >> simp[] >>
     metis_tac[cj 2 compile_expr_grows]) >>
  `not_local_ptr c ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  qabbrev_tac `ai = mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv vtyp))] [p]` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   ai.inst_id = st.cs_next_id` by simp[Abbr `ai`, mk_inst_def] >>
  `lookup_scopes id (sc::rest) = NONE /\ not_local_ptr c (sc::rest) p` by
    metis_tac[] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size tyv)` by
    (qpat_x_assum `FLOOKUP t.vs_allocas st.cs_next_id = _` mp_tac >> simp[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_memory_bytes cenv vtyp = _` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  drule annassign_bytes_post_path_mem >>
  disch_then (qspecl_then [`sb`, `id`, `p`, `type_memory_size tyv`, `w`,
    `ai`, `tyv`, `etv`, `ltv`, `vtyp`, `sc`, `rest`, `T`, `vv_location vv`,
    `type_memory_size tyv`, `d`] mp_tac) >>
  impl_tac
  >- (simp[] >> fs[]) >>
  disch_then (qx_choose_then `tf:venom_state` strip_assume_tac) >>
  qabbrev_tac `ee' = ee with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` >>
  qexistsl_tac [`ee'`, `tf`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      simp[Abbr `ee'`]) >>
  `sA.cs_next_var <= sB.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
          lookup_var x tf = SOME w'` by
    (rpt strip_tac >>
     `not_fresh_at sA x` by metis_tac[] >>
     `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP tf.vs_allocas aid = SOME b` by metis_tac[] >>
  `s0.vs_alloca_next <= tf.vs_alloca_next` by decide_tac >>
  `cenv_top_ext cenv c ee'.scopes` by
    (simp[Abbr `ee'`] >> irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa`, `st`, `vtyp`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `return_buf_frame d c sb tf` by simp[] >>
  `stmt_state_rel ctx func c cx ee' tf` by
    (qunabbrev_tac `ee'` >>
     qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (ee with scopes := scs) _` >>
     `ee with <|scopes := scs; gas_obs := []|> =
      (ee with scopes := scs) with gas_obs := []`
       by simp[evaluation_state_component_equality] >>
     metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  simp[stmt_lands_def]
QED

(* The right-hand side of a bytestring declaration, lowered as by
   compile_annassign_bytes_stmt_frag_mem's premise.  Beyond expr_sim_mem's
   post, a value left in memory has its source region reach the lowered
   type's size, which the staging copy reads in full: vv_store_bound gives
   that room at the lowered type. *)
Theorem annassign_bytes_rhs_located_mem:
  !tops ctx func c cx env e es ltv etv.
    body_inv tops ctx c cx /\ expr_body_pre c cx env e es /\
    body_expr_mem_ok cx e /\
    is_bytestring_type (expr_type e) /\
    evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    type_memory_bytes c (expr_type e) = type_memory_size etv /\
    type_memory_size etv < 2 ** 64 /\
    0 < type_memory_size ltv /\
    type_memory_size ltv <= type_memory_size etv ==>
    !sa sV sb vv op s0.
      compile_expr c (expr_type e) e sa = (vv, sV) /\
      unwrap_value c vv sV = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved c sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func c cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func c cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          (vv_location vv = SOME LocMemory ==>
           !sw. eval_operand op t = SOME sw ==>
                w2n sw + type_memory_size ltv <= t.vs_alloca_next) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    metis_tac[bodyMemoryPredsTheory.body_expr_mem_ok_def] >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `c`, `cx`, `expr_type e`, `e`, `es`]
            expr_sim_mem_room) >>
  impl_tac >- (rpt strip_tac >> gvs[]) >>
  disch_then (qspecl_then [`sa`, `sV`, `sb`, `vv`, `op`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  irule gas_outcome_post_mono >>
  first_x_assum (irule_at (Pos last)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rpt strip_tac >> qpat_x_assum `vv_location _ = _ ==> _` drule >>
  disch_then drule >> strip_tac >> decide_tac
QED
