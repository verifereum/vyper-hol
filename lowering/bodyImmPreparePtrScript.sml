(* Scalar preparation of the immutable element address. *)
Theory bodyImmPreparePtr
Ancestors
  bodyPtrBopScalarSeq whitelistForIterImmLoop forPtrScope stmtSimForArrayLoop
  exprSimCopy exprSimPtrTopLevelImmutablePost
  ptrDiscipline venomState venomInst venomExecSemantics fragExec
  finite_map words list arithmetic pred_set vyperState

Theorem immutable_address_prefix_ptr:
  lookup_var idx s = SOME (n2w k) /\ ov <> tot /\
  ov NOTIN R /\ tot NOTIN R /\ ep NOTIN R /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  let code =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]];
      u = update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
       (if dyn then update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)
        else update_var ov (n2w (k * stride)) s)
  in
  ?H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    op_prov H (Var ep) = NONE /\ op_taint tm (Var ep) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tm.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `A = {Var idx; Lit (n2w stride); Lit 32w; Lit (n2w off)}` >>
  qabbrev_tac `B = Var ep INSERT
    (if dyn then Var tot INSERT (Var ov INSERT A) else Var ov INSERT A)` >>
  `bop_scalar_seq R A
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) B` by
    (Cases_on `dyn` >> simp[Abbr `B`, Abbr `A`, bop_scalar_seq_def, mk_inst_def]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) s =
    OK (update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
       (if dyn then update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)
        else update_var ov (n2w (k * stride)) s))` by
    (irule immutable_address_prefix_run >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >> simp[] >>
  `Var ep IN B` by simp[Abbr `B`] >>
  conj_tac >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    SIMP_TAC bool_ss [LENGTH_APPEND, LENGTH, ONE, ADD_CLAUSES, ADD_COMM]) >> metis_tac[]
QED

(* Scope adapter for the checked immutable copy contract.  The source relation
   is in the outer environment; only the destination loop local is added. *)
Theorem immutable_copy_scope_ptr_from_copy:
  (!ce src q bytes ty cs ct tyv cxx cxxctx fn ee ss vv aa bb dd GG tt
      sc rest name cap inst assign PG D.
    compile_iter_elem_copy ce src (Var q) bytes LocCode F ty ty cs = ((),ct) /\
    bytes = type_memory_size tyv /\ 0 < bytes /\ ~ce.ce_is_ctor /\
    evaluate_type (get_tenv cxx) ty = SOME tyv /\
    stmt_state_rel cxxctx fn ce cxx ee ss /\ fn_inst_ids_distinct fn /\
    ghost_inv dd ce cxx ee GG tt ss /\
    ee.scopes = sc :: rest /\ lookup_scopes name ee.scopes = NONE /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap) /\
    not_local_ptr ce ee.scopes q /\ lookup_var q ss = SOME bb /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (w2n bb,cap) /\
    bytes <= cap /\ w2n bb + cap < dimword (:256) /\
    immutable_holds ce cxx ty (Value vv) aa ee ss /\
    copy_old_operand cs src /\ eval_operand src ss = SOME aa /\ op_taint tt src = {} /\
    ptr_covers GG tt q ss cap /\ local_ptrs_reserved ce cs /\
    (!r sz. ce.ce_return_buf = SOME (PtrVar (Var r) sz) \/
       ce.ce_return_pc = SOME (PtrVar (Var r) sz) ==> not_fresh_at cs r) /\
    ~ctx_has_dalloca cxxctx ==>
    ?t H tm.
      copy_runtime_frame cs ss ct t /\
      (!k. inst_seq_ptr D 0 cxxctx fn PG GG tt (emitted_insts cs ct)
        (ss with vs_inst_idx := k) H tm) /\
      stmt_state_rel cxxctx fn ce cxx
        (ee with scopes := (sc |+ (name,
          <|assignable := assign; type := tyv; value := vv; popped := []|>)) :: rest) t /\
      ghost_inv dd ce cxx
        (ee with scopes := (sc |+ (name,
          <|assignable := assign; type := tyv; value := vv; popped := []|>)) :: rest) H tm t /\
      ptr_covers H tm q t cap /\ val_wf tyv vv /\
      val_in_memory tyv vv (w2n bb) t.vs_memory /\ val_footprint tyv vv <= bytes /\
      immutable_copy_ghost_frame cs ss GG tt ct t H tm 0 bytes bb) /\
  compile_iter_elem_copy cenv src (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\ ~bc.ce_is_ctor /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv d cenv cx es G tn s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ lookup_var p s = SOME dst /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  stride <= sz /\ w2n dst + sz < dimword (:256) /\
  immutable_holds cenv cx et (Value v) a es s /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  ptr_covers G tn p s sz /\ local_ptrs_reserved bc sa /\
  (!q cap. bc.ce_return_buf = SOME (PtrVar (Var q) cap) \/
     bc.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at sa q) /\
  ~ctx_has_dalloca ctx ==>
  ?t H tm.
    copy_runtime_frame sa s sb0 t /\
    (!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb0)
      (s with vs_inst_idx := k) H tm) /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    ghost_inv d bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) H tm t /\
    ptr_covers H tm p t sz /\ val_wf tv v /\
    val_in_memory tv v (w2n dst) t.vs_memory /\ val_footprint tv v <= stride /\
    immutable_copy_ghost_frame sa s G tn sb0 t H tm 0 stride dst
Proof
  strip_tac >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s` by
    (irule array_empty_scope_rel_transport >> qexists `cenv` >> simp[]) >>
  `ghost_inv d bc cx (es with scopes := FEMPTY :: es.scopes) G tn s` by
    (irule ghost_inv_push_top_ext >> metis_tac[]) >>
  `immutable_holds bc cx et (Value v) a
    (es with scopes := FEMPTY :: es.scopes) s` by
    (irule immutable_value_holds_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists `FEMPTY :: es.scopes` >> simp[]) >>
  `compile_iter_elem_copy bc src (Var p) stride LocCode F et et sa = ((),sb0)` by
    (drule immutable_iter_copy_top_ext >> disch_then (fn th => fs[GSYM th])) >>
  first_x_assum (drule_at (Pat `compile_iter_elem_copy bc _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ bc _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ bc _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `immutable_holds bc _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP bc.ce_vars _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var p s = SOME _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts func)`)) >>
  simp[lookup_scopes_def] >>
  disch_then (qspecl_then [`F`, `PG`, `D`] mp_tac) >>
  simp[] >> disch_then irule >> metis_tac[]
QED
