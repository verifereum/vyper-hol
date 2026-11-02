(* Layout-converting stores into memory locals, after expression evaluation. *)
Theory stmtSimMemoryWiden
Ancestors
  list finite_map exprSim exprSimHyps stmtSim stmtSimDeclMem
  stmtSimAssignMem stmtSimAssignTupleMem typedMemoryCopy
  stmtSimAssignStore fragExec
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

