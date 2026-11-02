(* Layout-converting stores into memory locals, after expression evaluation. *)
Theory stmtSimMemoryWiden
Ancestors
  list finite_map exprSim exprSimHyps stmtSim stmtSimDeclMem
  stmtSimAssignMem stmtSimAssignTupleMem typedMemoryCopy
  stmtSimAssignStore fragExec stmtSimDeclStore localPtrsProps
  exprLoweringProps venomState venomMemDefs
  stmtLowering exprLowering compileEnv valueEncoding vyperTypeSystem
  vyperInterpreter vyperState
Libs
  monadsyntax wordsLib intLib

Theorem compile_assign_memory_typed_extends[local]:
  !cenv dst src loc dty sty info sz sa sb.
    compile_assign_value cenv dst LocMemory src F loc dty sty info sz sa = ((),sb) ==>
    cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  `exprLoweringProps$ci_mono sa
     (SND (compile_assign_value cenv dst LocMemory src F loc dty sty info sz sa))` suffices_by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  pop_assum kall_tac >>
  simp[compile_assign_value_def] >>
  Cases_on `loc = SOME LocMemory` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind,
              ho_match_mp_tac exprLoweringPropsTheory.ci_mono_ignore_bind,
              conj_tac, gen_tac]) >>
  simp[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
       exprLoweringPropsTheory.ci_mono_comp_return,
       exprLoweringPropsTheory.ci_mono_compile_copy_memory,
       exprLoweringPropsTheory.ci_mono_compile_store_memory]
QED

Theorem assign_local_memory_typed_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op, sB)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sB` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sB sf` by metis_tac[compile_assign_memory_typed_extends] >>
  `fn_has_code sa sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >> gvs[]
QED

Theorem declare_local_typed_memory_metadata:
  !cenv id vtyp sa c st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals ==>
    c.ce_struct_fields = cenv.ce_struct_fields /\
    (!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
    (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  simp[] >> conj_tac
  >- (`!env ty. env.ce_struct_fields = cenv.ce_struct_fields ==>
          type_memory_bytes env ty = type_memory_bytes cenv ty` suffices_by
        metis_tac[] >>
      ho_match_mp_tac type_memory_bytes_ind >>
      rw[type_memory_bytes_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[]) >>
  gen_tac >> simp[oneline lowered_value_type_def]
QED

Theorem annassign_memory_typed_lower_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sA = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac loweringSliceTheory.emit_inst_unit >>
  gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem annassign_memory_typed_code_parts:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
                cs_extends a b) ==>
    ?st sA sV sB vv op p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sV) /\
      unwrap_value c vv sV = (op, sB) /\
      lower_value compile_expr c (expr_type e) e sA = (op, sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
        (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes c elem_ty + 31) DIV 32,
                 type_memory_bytes c elem_ty) | _ => NONE)
        (type_memory_bytes c vtyp) sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all declare_local_typed_memory_metadata >> strip_tac >>
  `lowered_value_type c e = lowered_value_type cenv e` by metis_tac[] >>
  drule_all annassign_memory_typed_lower_parts >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `cs_extends sA sB /\ cs_extends sB sf` by
    metis_tac[compile_assign_memory_typed_extends] >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  qexistsl [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
            `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[]
QED

Theorem lowered_nonbytestring_type_eq[local]:
  !cenv e. ~is_bytestring_type (lowered_value_type cenv e) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, is_bytestring_type_def, LET_THM]
QED

Theorem compile_intcall_stack_operand_zero[local]:
  !cfn cenv ret_ty ty fid args default_ret sa vt op sb.
    compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret sa =
      (StackValue vt op, sb) ==>
    op = Lit 0w
Proof
  rpt gen_tac >>
  simp[compile_call_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `compile_multi_vvs cfn cenv args sa` >> simp[] >>
  rename1 `compile_multi_vvs _ _ _ _ = (avs,s1)` >>
  Cases_on `returns_count > 0`
  >- (simp[] >> Cases_on `compile_alloc_buffer (32 * returns_count) s1` >>
      simp[] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `return_buf_size > 0`
  >- (simp[] >> Cases_on `compile_alloc_buffer return_buf_size s1` >>
      simp[] >> rpt (pairarg_tac >> gvs[])) >>
  simp[] >> rpt (pairarg_tac >> gvs[])

QED

Theorem typed_memory_expr_source:
  !ctx func cenv cx e es sa sb s0 es1 v op s stv.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv ==>
    val_wf stv v /\
    expr_val_at cenv cx (lowered_value_type cenv e) sa sb es1 v op s /\
    ?w. eval_operand op s = SOME w /\
        val_in_memory stv v (w2n w) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule lowered_nonbytestring_type_eq >> strip_tac >>
  gvs[expr_post_def, expr_val_rel_def] >>
  metis_tac[expr_val_at_def]
QED

Theorem nonbytestring_full_footprint[local]:
  !tenv t tv v.
    evaluate_type tenv t = SOME tv /\ ~is_bytestring_type t ==>
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `t` >>
  simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `v` >>
  gvs[val_footprint_def, is_bytestring_type_def]
QED

(* Separation keeps both allocation and borrowed-local source ownership. *)
Theorem typed_source_decl_alloca_separate[local]:
  !cenv cx t sa sb es v op s tv func inst q dst dsz sw.
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    val_footprint tv v = type_memory_size tv /\
    0 < type_memory_size tv /\ 0 < dsz /\
    eval_operand op s = SOME sw /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv es.scopes s /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    inst.inst_id < sa.cs_next_id /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,dsz) ==>
    w2n sw + type_memory_size tv <= dst \/
    dst + dsz <= w2n sw
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (gvs[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.allocas_non_overlapping_def] >>
      `aid <> inst.inst_id` by decide_tac >>
      first_x_assum drule_all >> decide_tac) >>
  `regions_disjoint dst dsz b sz` by
    (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     metis_tac[]) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem typed_decl_post_separate[local]:
  !ctx func cenv cx e es sa sb s0 es1 v op s stv inst p dw dsz.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ 0 < dsz /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func ==>
    lookup_var p s = SOME dw /\
    ?sw. eval_operand op s = SOME sw /\
         (w2n sw + type_memory_size stv <= w2n dw \/
          w2n dw + dsz <= w2n sw)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytestring_full_footprint] >>
  gvs[expr_post_def] >>
  `lookup_var p s = SOME dw /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by metis_tac[] >>
  `alloca_inv s /\ local_ptrs_rel func cenv es1.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `expr_val_at _ _ (expr_type e) _ _ _ _ _ _` kall_tac >>
  drule_all typed_source_decl_alloca_separate >> simp[]
QED

Theorem typed_expr_source_end_lt[local]:
  !ctx func cenv cx es s t sa sb v op tv w.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    ~is_bytestring_type t /\ 0 < type_memory_size tv /\
    eval_operand op s = SOME w ==>
    w2n w + type_memory_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[nonbytestring_full_footprint] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
      venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def]
  >- (first_x_assum drule >> decide_tac) >>
  gvs[local_region_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem typed_alloca_end_lt[local]:
  !ctx func cenv cx es s aid b sz n.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ n <= sz ==>
    b + n < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
      venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem typed_decl_post_copy_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_store_memory_typed cenv (Var p) dty op
      (lowered_value_type cenv e) sb = ((),sf) /\
    fn_has_code sb sf func /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `0 < dsz` by decide_tac >>
  drule_all typed_decl_post_separate >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    (drule_all typed_alloca_end_lt >> simp[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all typed_expr_source_end_lt >> simp[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule compile_store_memory_typed_run >>
  disch_then (qspec_then `get_tenv cx` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >>
  disch_then irule >>
  gvs[expr_sim_inv_def] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, decide_tac, metis_tac[]]
QED

Theorem typed_decl_staged_code_parts[local]:
  !cenv dst src dty sty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      dty sty info bytes sa = ((),sb) /\
    0 < type_memory_bytes cenv sty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv sty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst dty sty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`, `tmp`] strip_assume_tac) >>
  rename1 `compile_copy_memory _ _ _ sm = ((),sn)` >>
  `emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
      sm = ((),sn)` by
    (Cases_on `type_memory_bytes cenv sty` >> gvs[contextTheory.compile_copy_memory_def]) >>
  `cs_extends sm sn` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends sn sb` by
    (`exprLoweringProps$ci_mono sn
       (SND (compile_store_memory cenv (Var tmp) dst dty sty sn))` suffices_by
       gvs[exprLoweringPropsTheory.ci_mono_def] >>
     simp[exprLoweringPropsTheory.ci_mono_compile_store_memory]) >>
  `cs_extends sx sn /\ cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sa sx func /\ fn_has_code sx sn func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sx sm func /\ fn_has_code sm sn func` by metis_tac[fn_has_code_split] >>
  `sm.cs_next_var = sn.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `sm.cs_next_var = sx.cs_next_var` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_inst_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  qexistsl [`sm`, `sn`, `tmp`] >> gvs[] >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> simp[]
QED

Theorem typed_decl_stage_owned_run[local]:
  !ctx func cenv cx es sb sf s op dty sty info bytes stv v sw p dw aid dsz.
    compile_assign_value cenv (Var p) LocMemory op F (SOME LocMemory)
      dty sty info bytes sb = ((),sf) /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    eval_operand op s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,dsz) /\
    val_in_memory stv v (w2n sw) s.vs_memory /\ val_wf stv v /\
    val_footprint stv v <= type_memory_size stv /\
    fn_has_code sb sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn tmp u uw taid.
      taid = sb.cs_next_id /\
      compile_store_memory cenv (Var tmp) (Var p) dty sty sn = ((),sf) /\
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      fn_has_code sn sf func /\ not_fresh_at sn tmp /\
      stmt_state_rel ctx func cenv cx es u /\
      lookup_var tmp u = SOME uw /\ lookup_var p u = SOME dw /\
      FLOOKUP u.vs_allocas taid = SOME (w2n uw,type_memory_size stv) /\
      FLOOKUP u.vs_allocas aid = SOME (w2n dw,dsz) /\
      val_in_memory stv v (w2n uw) u.vs_memory /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      (!fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_bytes cenv sty` by simp[] >>
  drule_all typed_decl_staged_code_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
    (irule loweringHaltTheory.emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes tmp` by
    (gvs[compileEnvTheory.local_ptrs_reserved_def,
         compileEnvTheory.not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var tmp /\ p <> tmp` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  `type_memory_bytes cenv sty < dimword (:256) /\
   val_footprint stv v <= type_memory_bytes cenv sty` by metis_tac[] >>
  drule_all alloc_copy_memory_owned_run >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> tmp` by (strip_tac >> gvs[]) >> simp[]) >>
  qexistsl [`sn`, `tmp`, `u`, `uw`, `sx.cs_next_id`] >>
  simp[] >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  metis_tac[]
QED

Theorem typed_owned_allocas_copy_run[local]:
  !ctx func cenv cx env es0 es s sa sf src p sw dw aid bid stv dtv v sty dty dsz.
    stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es0 /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    FLOOKUP s.vs_allocas aid = SOME (w2n sw,type_memory_size stv) /\
    FLOOKUP s.vs_allocas bid = SOME (w2n dw,dsz) /\ aid <> bid /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    type_memory_size dtv <= dsz /\
    compile_store_memory_typed cenv (Var p) dty src sty sa = ((),sf) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    fn_has_code sa sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (irule typed_alloca_end_lt >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    (irule typed_alloca_end_lt >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
         venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def] >>
     first_x_assum drule_all >> decide_tac) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule compile_store_memory_typed_run >>
  disch_then (qspec_then `get_tenv cx` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >>
  disch_then irule >> gvs[expr_sim_inv_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]
QED

Theorem typed_same_layout_store_run[local]:
  !ctx func cenv tenv s sa sf src dst sw dw tv ty v.
    compile_store_memory cenv src dst ty ty sa = ((),sf) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule valueCopyTheory.compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `tv`, `v`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `frag_exec ctx sa sf (\u. u = s)
    (\u. val_in_memory tv v (w2n dw) u.vs_memory /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH u.vs_memory) (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     gvs[exprLoweringPropsTheory.same_blocks_def, venomStateTheory.lookup_var_def] >>
     conj_tac
     >- (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
         simp[venomStateTheory.venom_state_component_equality]) >>
     first_assum ACCEPT_TAC) >>
  drule stmtSimDeclTheory.frag_exec_no_exit_run >>
  disch_then (qspecl_then [`func`, `s`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists `u` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem typed_decl_staged_convert_run[local]:
  !ctx func cenv cx env es0 es sb sf s op dty sty info bytes stv dtv v sw p dw aid dsz.
    compile_assign_value cenv (Var p) LocMemory op F (SOME LocMemory)
      dty sty info bytes sb = ((),sf) /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es0 /\
    acyclic_struct_metadata cenv.ce_struct_fields /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    eval_operand op s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,dsz) /\ aid < sb.cs_next_id /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    val_footprint stv v <= type_memory_size stv /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    fn_has_code sb sf func /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn u t.
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      stmt_state_rel ctx func cenv cx es u /\
      lookup_var p u = SOME dw /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf stv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule_all typed_decl_stage_owned_run >>
  disch_then (qx_choosel_then [`sn`, `tmp`, `u`, `uw`, `taid`] strip_assume_tac) >>
  `not_fresh_at sn p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
  `eval_operand (Var tmp) u = SOME uw` by simp[venomStateTheory.eval_operand_def] >>
  `taid <> aid` by decide_tac >>
  `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sn x` by simp[] >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func u = r)` by
    (Cases_on `dty = sty`
     >- (qpat_x_assum `dty = sty` SUBST_ALL_TAC >>
         `stv = dtv` by
           (qpat_x_assum `evaluate_type _ _ = SOME stv` mp_tac >>
            qpat_x_assum `evaluate_type _ _ = SOME dtv` mp_tac >> simp[]) >>
         qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
         `eval_operand (Var p) u = SOME dw` by simp[venomStateTheory.eval_operand_def] >>
         drule_all typed_same_layout_store_run >> simp[]) >>
     `compile_store_memory_typed cenv (Var p) dty (Var tmp) sty sn = ((),sf)` by
       gvs[contextTheory.compile_store_memory_def] >>
     drule_all typed_owned_allocas_copy_run >> simp[]) >>
  qexistsl [`sn`, `u`, `t`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func u = r /\ _ ==> _` drule >>
  simp[]
QED
Theorem typed_decl_post_assign_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty loc info bytes.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_id < sa.cs_next_id /\ inst.inst_id < sb.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?sn u t.
      cs_extends sb sn /\ sb.cs_next_var <= sn.cs_next_var /\
      stmt_state_rel ctx func cenv cx es1 u /\ lookup_var p u = SOME dw /\
      (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
      (!a entry. FLOOKUP s.vs_allocas a = SOME entry ==>
                 FLOOKUP u.vs_allocas a = SOME entry) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := u.vs_inst_idx|>) = u /\
      (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_memory_expr_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   lookup_var p s = SOME dw /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[nonbytestring_full_footprint, arithmeticTheory.LESS_EQ_REFL] >>
  Cases_on `loc = SOME LocMemory`
  >- (qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
      drule_all typed_decl_staged_convert_run >> simp[]) >>
  `compile_store_memory cenv op (Var p) dty (lowered_value_type cenv e) sb = ((),sf)` by
    gvs[compile_assign_value_def] >>
  qexistsl [`sb`, `s`] >> simp[compileEnvTheory.cs_extends_refl] >>
  Cases_on `dty = lowered_value_type cenv e`
  >- suspend "same" >>
  suspend "different"
QED

Resume typed_decl_post_assign_run[same]:
  qpat_x_assum `dty = lowered_value_type cenv e` SUBST_ALL_TAC >>
  `stv = dtv` by
    (qpat_x_assum `evaluate_type _ _ = SOME stv` mp_tac >>
     qpat_x_assum `evaluate_type _ _ = SOME dtv` mp_tac >> simp[]) >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `!x. Var p = Var x ==> not_fresh_at sb x` by simp[] >>
  `eval_operand (Var p) s = SOME dw` by simp[venomStateTheory.eval_operand_def] >>
  drule_all typed_same_layout_store_run >> simp[]
QED

Resume typed_decl_post_assign_run[different]:
  `compile_store_memory_typed cenv (Var p) dty op
     (lowered_value_type cenv e) sb = ((),sf)` by
    gvs[contextTheory.compile_store_memory_def] >>
  drule_all typed_decl_post_copy_run >> simp[]
QED

Finalise typed_decl_post_assign_run

Theorem typed_decl_store_frame[local]:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                              vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule loweringSliceTheory.immutables_rel_mem_agree >> qexists `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem typed_decl_store_post_run[local]:
  !ctx func cenv cx env e es sa sb sf s0 es1 v op s stv dtv
   inst p dw dsz dty loc info bytes sc rest id a.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    expr_sim_inv cenv cx env es /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,dsz) /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_id < sa.cs_next_id /\ inst.inst_id < sb.cs_next_id /\
    not_local_ptr cenv es1.scopes p /\ fn_inst_ids_distinct func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= dsz /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ local_ptrs_reserved cenv sb /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ not_fresh_at sb p /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
            (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_decl_post_assign_run >>
  disch_then (qx_choosel_then [`sn`, `u`, `t`] strip_assume_tac) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,dsz)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sb` >> simp[]) >>
  `not_fresh_at sn p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `stmt_state_rel ctx func cenv cx
      (es1 with scopes :=
        (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t` by
    (drule_all typed_decl_store_frame >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `_ = u` mp_tac >> simp[venom_state_component_equality]) >>
  qexists `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
      simp[]) >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!fuel r. _` irule >> simp[] >>
  qexists `fuel` >> simp[]
QED

Theorem annassign_memory_typed_read_success_run[local]:
  !ctx func cenv cx env id dty e es es' stv dtv sa sb sf op p sz s0 dw inst loc info bytes.
    eval_stmt cx (AnnAssign id dty e) es = (INL (),es') /\
    expr_sim_inv cenv cx env es /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv <= sz /\
    type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1. (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type dtv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\ cs_extends sa sb /\
    compile_assign_value cenv (Var p) LocMemory op F loc dty
      (lowered_value_type cenv e) info bytes sb = ((),sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME dw /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
    inst.inst_id < sa.cs_next_id ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule loweringSliceTheory.eval_stmt_annassign_read_value >> strip_tac >>
  rename1 `(do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1)` >>
  `value_has_type stv v /\ value_has_type dtv v` by metis_tac[] >>
  `not_local_ptr cenv es1.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `tyv = dtv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv = dtv` SUBST_ALL_TAC >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
  `not_fresh_at sb p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `inst.inst_id < sb.cs_next_id` by decide_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  drule_all typed_decl_store_post_run >>
  disch_then (qspec_then `T` mp_tac) >> strip_tac >>
  qexists `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx func s0 = _` mp_tac >>
  qpat_x_assum `!fuel r. _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED


Theorem unstaged_overlap_value_types[local]:
  let u = BaseT (UintT 256);
      sty = TupleT [TupleT [BaseT (BytesT (Dynamic 1));u];u];
      dty = TupleT [TupleT [BaseT (BytesT (Dynamic 33));u];u];
      v = ArrayV (TupleV [ArrayV (TupleV [BytesV [];IntV 7]);IntV 9])
  in type_widens_to FEMPTY sty dty /\
     value_has_type
       (TupleTV [TupleTV [BaseTV (BytesT (Dynamic 1));BaseTV (UintT 256)];
                 BaseTV (UintT 256)]) v /\
     value_has_type
       (TupleTV [TupleTV [BaseTV (BytesT (Dynamic 33));BaseTV (UintT 256)];
                 BaseTV (UintT 256)]) v
Proof
  EVAL_TAC
QED

Theorem unstaged_overlap_input_memory[local]:
  !s0.
  let s = mstore 96 9w (mstore 64 7w (s0 with vs_memory := []));
      tv = TupleTV [TupleTV [BaseTV (BytesT (Dynamic 1));BaseTV (UintT 256)];
                    BaseTV (UintT 256)];
      v = ArrayV (TupleV [ArrayV (TupleV [BytesV [];IntV 7]);IntV 9])
  in val_in_memory tv v 0 s.vs_memory /\ mload 96 s = 9w
Proof
  gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``val_in_memory``, ``mload``]) >>
  EVAL_TAC
QED

(* A probe of an adapter, not a counterexample to expression simulation. *)
Theorem unstaged_overlap_probe[local]:
  let u = BaseT (UintT 256);
      sty = TupleT [TupleT [BaseT (BytesT (Dynamic 1));u];u];
      dty = TupleT [TupleT [BaseT (BytesT (Dynamic 33));u];u];
      ce = (ARB:compile_env) with ce_struct_fields := FEMPTY;
      st = initial_compile_state "entry";
      out = SND (compile_assign_value ce (Lit 0w) LocMemory (Lit 0w)
                    F NONE dty sty NONE 160 st);
      bb = <|bb_label := "entry";
             bb_instructions := out.cs_current_insts ++
               [mk_inst 999 STOP [] []]|>;
      s = mstore 96 9w (mstore 64 7w
            ((ARB:venom_state) with <|vs_vars := FEMPTY; vs_memory := [];
              vs_inst_idx := 0; vs_halted := F|>))
  in case run_block 100 ARB bb s of
       Halt s' => mload 128 s' = 7w
     | _ => F
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_block``, ``mload``]) >>
  rewrite_tac[venomExecSemanticsTheory.run_block_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``mload``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_defs] >>
  EVAL_TAC
QED

Theorem compile_annassign_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' stv dtv.
    eval_stmt cx (AnnAssign id dty e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\ cenv.ce_alloca_locals /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type dtv v) /\
    (!st0 c st1. declare_local cenv id dty st0 = (c,st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (AnnAssign id dty e)) es res es'
Proof
  cheat
QED

Theorem compile_assign_local_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' p sz stv dtv.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME dty /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1 entry.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (Assign (BaseTarget (NameTarget id)) e)) es res es'
Proof
  cheat
QED

