(*
 * Tuple unpacking into locals with memory-backed elements: the code's
 * stages and the run of a successful assignment (#637).
 *
 * TOP-LEVEL:
 *   assign_tuple_locals_memory_code_parts — the code split at its stages
 *   assign_tuple_locals_memory_suffix_path — a successful assignment's run
 *)
Theory tupleAssignMemory
Ancestors
  loweringPosts
  fragGasMode
  exprSimDefs loweringPosts tupleAssignParts tupleAssignPrefix
  tupleTypedLoad tupleStageProps stmtSimAssignTuple tupleLocalStoreProps
  tupleLocalStoreRun stmtSimReturn stmtSimDeclMem valueCopyBytes valueCopy
    exprOperandVar exprLoweringProps stmtLowering compileEnv
  exprLowering emitHelperProps fragExec loweringSlice freshWrites
  list rich_list finite_map valueEncoding vyperTyping vyperValue vyperTypeABI
  vyperInterpreter vyperState venomState venomInst
Libs
  monadsyntax

(* The code of x1, ..., xn = e with memory-backed elements, split at its
   stages, with the growth facts of each. *)
Theorem assign_tuple_locals_memory_code_parts:
  !cenv lctx ty ids e tys sa sf c func.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
      ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
        cenv.ce_var_type (EL i ids) = SOME vt /\
        (is_word_type vt = is_word_type (EL i tys)) /\
        (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sc op su staged sl elems ss.
      compile_expr cenv (TupleT tys) e sa = (vv, sc) /\
      unwrap_value cenv vv sc = (op, su) /\
      (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
          EXISTS (\t. ~is_word_type t) tys /\
          0 < SUM (MAP (type_memory_bytes cenv) tys) then
         do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
            ptr <- comp_return buf.buf_operand;
            emit_void MCOPY [ptr; op;
              Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
            comp_return ptr od
       else comp_return op) su = (staged, sl) /\
      compile_tuple_load_all cenv staged tys 0 sl = (elems, ss) /\
      compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
        elems ss = ((), sf) /\
      cs_extends sa sc /\ cs_extends sc su /\ cs_extends su sl /\
      cs_extends sl ss /\ cs_extends ss sf /\
      fn_has_code sa sc func /\ fn_has_code sc su func /\
      fn_has_code su sl func /\ fn_has_code sl ss func /\
      fn_has_code ss sf func /\
      sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
      sl.cs_next_var <= ss.cs_next_var /\ ss.cs_next_var <= sf.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_targets_code_parts >> simp[]
QED

Theorem compile_store_memory_compatible_run:
  !cenv src dst dty sty sa sb s tenv dtv stv v sw dw.
    compile_store_memory cenv src dst dty sty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type dty /\
    evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb) /\
   val_in_memory dtv v (w2n sw) s.vs_memory` by
    (Cases_on `dty = sty` >- gvs[] >>
     gvs[] >> conj_tac
     >- metis_tac[compile_store_memory_bytestring_src] >>
     drule_all bytestring_val_in_memory_transfer >> simp[]) >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `dtv`, `v`, `sw`, `dw`] mp_tac) >>
  simp[]
QED

Theorem assign_tuple_locals_memory_suffix_path:
  !ctx func cx cenv ids es1 es' tys tvs vs sa su sl ss sf op staged elems sv flag.
    ids <> [] /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (!i. i < LENGTH ids ==> ?p sz vt.
      FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type (EL i ids) = SOME vt /\
      if is_word_type (EL i tys) then is_word_type vt else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
          type_memory_bytes cenv vt = type_memory_size vtv /\
          0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    (!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
      if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i vs)) /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es1 = (INL (),es') /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
    expr_val_at cenv cx (TupleT tys) sa su es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) elems ss = ((),sf) /\
    su.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= ss.cs_next_var /\
    cs_extends su sl /\ cs_extends sl ss /\ cs_extends ss sf /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    stmt_state_rel ctx func cenv cx es1 sv /\ ~sv.vs_halted /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x w. not_fresh_at su x /\ lookup_var x sv = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP sv.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      gas_marked_path F ctx func sv 0 (OK t) /\
      (!c0 e0 sa0 s0.
        alloca_frame c0 e0 sa0 s0 cenv es1 sv /\
        sa0.cs_next_id <= su.cs_next_id /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
          FLOOKUP sv.vs_allocas aid = SOME entry) ==>
        alloca_frame c0 e0 sa0 s0 cenv es' t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >>
  suspend "source"
QED

Resume assign_tuple_locals_memory_suffix_path[source]:
  drule assign_tuple_target_list_length >> strip_tac >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `LENGTH ids = LENGTH vs /\ LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length, LENGTH_MAP] >>
  suspend "code"
QED

Resume assign_tuple_locals_memory_suffix_path[code]:
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (irule tuple_element_sizes >> reverse conj_tac
     >- (qexists `get_tenv cx` >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl [`get_tenv cx`, `tys`] >>
     simp[SF CONJ_ss] >>
     rpt gen_tac >> strip_tac >>
     Cases_on `is_word_type (EL i tys)` >- simp[] >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> metis_tac[]) >>
  drule_all tuple_assignment_prefix_path >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "store"
QED

Resume assign_tuple_locals_memory_suffix_path[store]:
  `LENGTH ids = LENGTH tys /\ LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH ids ==> ?v. eval_operand (EL i elems) t = SOME v /\
     if is_word_type (EL i tys) then
       v = typed_val_to_w256 (EL i tvs) (EL i vs)
     else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH ids ==> ?p dsz vt.
     FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) dsz) /\
     cenv.ce_var_type (EL i ids) = SOME vt /\
     (is_word_type vt = is_word_type (EL i tys)) /\
     (~is_word_type (EL i tys) ==>
       (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
       type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
       ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
         type_memory_bytes cenv vt = type_memory_size vtv /\
         0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> ?p sz vt. _` (qspec_then `i` mp_tac) >>
     simp[] >> disch_then (qx_choosel_then [`p`, `dsz`, `vt`]
       (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qexistsl [`p`, `dsz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> asm_rewrite_tac[] >>
     metis_tac[is_bytestring_word_type]) >>
  suspend "store_ready"
QED

Resume assign_tuple_locals_memory_suffix_path[store_ready]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`!i. i < LENGTH ids ==> ?p sz vt. _ /\ _ /\ if _ then _ else _`,
     `value_has_type _ _`, `evaluate_type _ (TupleT tys) = _`,
     `compile_tuple_load_all _ _ _ _ _ = _`,
     `0 < type_memory_size_list tvs`, `tys <> []`] >>
  `!i. i < LENGTH tys ==>
     evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
     (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (rpt gen_tac >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
       (qpat_assum `LIST_REL (\t tv. evaluate_type _ t = SOME tv) _ _`
          (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        disch_then (qspec_then `i` mp_tac o CONJUNCT2) >> simp[]) >>
     simp[] >> strip_tac >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`ids`, `T`] tupleLocalStoreRunTheory.tuple_store_mixed_locals_path)) >>
  disch_then ((MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ es' _ /\ _`
    (qx_choose_then `sfv` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  suspend "compose"
QED

Resume assign_tuple_locals_memory_suffix_path[compose]:
  conj_tac >- (first_x_assum irule >> simp[]) >>
  qexists `sfv` >> asm_rewrite_tac [] >>
  conj_tac >- suspend "vars" >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (`gas_marked_path F ctx func sv (0 + 0) (OK sfv)` by
        (irule gas_marked_path_then >> qexists `t` >> asm_rewrite_tac []) >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  qexistsl [`cenv`, `es1`, `su`] >> asm_rewrite_tac[]
QED
Resume assign_tuple_locals_memory_suffix_path[vars]:
  rpt strip_tac >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists `sl` >> simp[]) >>
  metis_tac[]
QED

Finalise assign_tuple_locals_memory_suffix_path

Finalise assign_tuple_locals_memory_suffix_path
