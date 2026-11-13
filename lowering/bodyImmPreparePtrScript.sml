(* Scalar preparation of the immutable element address. *)
Theory bodyImmPreparePtr
Ancestors
  bodyPtrEnvBuiltinsScalar allocaHistory allocaHistoryFragment bodyPtrDefs bodyPtrBopScalarSeq whitelistForIterImmLoop forPtrScope stmtSimForArrayLoop
  exprSimCopy exprSimPtrTopLevelImmutablePost exprLoweringProps stmtSimProps
  exprSimPtrProps whitelistForIterImmFrag stmtSimDeclCompose stmtLoweringMono
  fragGasSeqPtr compileEnv loweringStateRelDefs emitHelper context loweringPosts
  whitelistForIterImmCopy exprSimPtrTopLevelImmutableCopy fragGasPathPtr
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
  ?H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (OK (((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
        (if dyn then update_var tot (n2w (32 + k * stride))
           (update_var ov (n2w (k * stride)) s)
         else update_var ov (n2w (k * stride)) s)) with
        vs_inst_idx := s.vs_inst_idx + LENGTH
          ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
           (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
           [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])))) /\
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
    SIMP_TAC bool_ss [LENGTH_APPEND, LENGTH, ONE, ADD_CLAUSES, ADD_COMM] >>
    `!a b. SUC (SUC (a + b)) = a + 2 + b` by decide_tac >>
    asm_rewrite_tac[]) >> metis_tac[]
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

(* The scalar address calculation preserves the outer semantic and ghost
   resources, and exposes an old-register frame at the allocation cutoff. *)
Theorem immutable_address_entry_ptr:
  lookup_var idx s = SOME (n2w k) /\ ov <> tot /\
  ~not_fresh_at cut ov /\ ~not_fresh_at cut tot /\ ~not_fresh_at cut ep /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\ local_ptrs_reserved cenv cut /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x) /\
  immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s ==>
  ?H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (OK (((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
        (if dyn then update_var tot (n2w (32 + k * stride))
           (update_var ov (n2w (k * stride)) s)
         else update_var ov (n2w (k * stride)) s)) with
        vs_inst_idx := s.vs_inst_idx + LENGTH
          ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
           (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
           [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])))) /\
    op_prov H (Var ep) = NONE /\ op_taint tm (Var ep) = {} /\
    stmt_state_rel ctx func cenv cx es
      ((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
        (if dyn then update_var tot (n2w (32 + k * stride))
           (update_var ov (n2w (k * stride)) s)
         else update_var ov (n2w (k * stride)) s)) with
        vs_inst_idx := s.vs_inst_idx + LENGTH
          ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
           (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
           [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])) /\
    ghost_inv d cenv cx es H tm
      ((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
        (if dyn then update_var tot (n2w (32 + k * stride))
           (update_var ov (n2w (k * stride)) s)
         else update_var ov (n2w (k * stride)) s)) with
        vs_inst_idx := s.vs_inst_idx + LENGTH
          ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
           (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
           [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])) /\
    immutable_holds cenv cx et (Value v)
      (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es
      ((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
        (if dyn then update_var tot (n2w (32 + k * stride))
           (update_var ov (n2w (k * stride)) s)
         else update_var ov (n2w (k * stride)) s)) with
        vs_inst_idx := s.vs_inst_idx + LENGTH
          ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
           (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
           [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at cut x ==>
      lookup_var x
        ((update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
          (if dyn then update_var tot (n2w (32 + k * stride))
             (update_var ov (n2w (k * stride)) s)
           else update_var ov (n2w (k * stride)) s)) with
          vs_inst_idx := s.vs_inst_idx + LENGTH
            ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
             (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
             [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])) =
        lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ov NOTIN {x | not_fresh_at cut x} /\
   tot NOTIN {x | not_fresh_at cut x} /\ ep NOTIN {x | not_fresh_at cut x}` by simp[] >>
  drule_all immutable_address_prefix_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`H`, `tm`] >> simp[] >>
  conj_tac >- suspend "rel" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "holds" >>
  rpt strip_tac >>
  `x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
  Cases_on `dyn` >>
  gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def]
QED

Resume immutable_address_entry_ptr[rel]:
  simp[stmt_state_rel_inst_idx] >> Cases_on `dyn` >> simp[] >>
  rpt (irule stmt_state_rel_update_var >> simp[])
QED
Resume immutable_address_entry_ptr[ghost]:
  irule exprSimPtrPropsTheory.ghost_inv_fresh_frame >>
  qexistsl [`G`, `es`, `s`, `cut`, `tn`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     `x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
     Cases_on `dyn` >> gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def]) >>
  Cases_on `dyn` >> simp[update_var_def] >> metis_tac[]
QED
Resume immutable_address_entry_ptr[holds]:
  irule immutable_value_holds_transport >>
  qexistsl [`cenv`, `es`, `s`, `es.scopes`] >>
  simp[cenv_top_ext_refl] >> Cases_on `dyn` >> gvs[update_var_def]
QED
Finalise immutable_address_entry_ptr

(* Normalized compiler boundary for one immutable element preparation. *)
Theorem immutable_body_entry_ptr_from_copy:
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
  dyn = (case bd of Dynamic _ => T | Fixed _ => F) /\
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
  ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
  ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
  h = st1.cs_next_id + (if dyn then 9 else 6) /\
  nv = STRING #"%" (toString sj.cs_next_var) /\
  toto = Var (STRING #"%" (toString (st1.cs_next_var + (if dyn then 6 else 3)))) /\
  declare_local cenv id et st1 = (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
  sa.cs_current_bb = bod /\
  sa.cs_current_insts =
    [mk_inst h MUL [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
    (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov]
      [STRING #"%" (toString (st1.cs_next_var + 6))]] else []) ++
    [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit (n2w off); toto] [ep]] /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_id = h + (if dyn then 3 else 2) /\
  sa.cs_next_label = st1.cs_next_label + 5 /\
  compile_iter_elem_copy cenv (Var ep) (Var p)
    (elem_size_in_location cenv LocCode et) LocCode F et et sa = ((),sb0) /\
  same_blocks sa sb0 /\ sb0.cs_current_bb = bod /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
  cs_extends st st1 /\ fn_has_code sa sb0 func /\
  (?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions) /\
  cenv.ce_alloca_locals /\ ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  FLOOKUP cenv.ce_vars id = NONE /\ local_ptrs_reserved cenv st1 /\
  fn_inst_ids_distinct func /\ evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\ 0 < type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ copy_old_operand st1 lvo /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  MEM (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
    (fn_insts func) /\ k < LENGTH vs /\
  array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst (type_memory_bytes cenv et)
    (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
    bod st k es s /\
  ghost_inv d cenv cx es G tn s /\ ptr_covers G tn p s (type_memory_bytes cenv et) /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
  op_prov G lvo = NONE /\ op_taint tn lvo = {} /\ alloca_history func s /\
  (!ei t j. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ j < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL j vs))
      (n2w off + n2w ((if dyn then 32 else 0) + j * type_memory_size tv)) ei t) ==>
  ?t H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb0.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) t /\
    ghost_inv d bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) H tm t /\
    ret_pc_ok bc sb0 t /\ ptr_covers H tm p t (type_memory_bytes cenv et) /\
    lookup_var p t = SOME dst /\ lookup_var idx t = SOME (n2w k) /\
    FLOOKUP H idx = NONE /\ op_taint tm (Var idx) = {} /\
    eval_operand lvo t = SOME (n2w (LENGTH vs)) /\
    op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    FLOOKUP t.vs_allocas
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p]).inst_id =
      SOME (w2n dst,type_memory_bytes cenv et) /\ alloca_history func t /\
    st.cs_next_var <= (sa with cs_next_var := st1.cs_next_var + 2).cs_next_var /\
    (sa with cs_next_var := st1.cs_next_var + 2).cs_next_var <= sb0.cs_next_var /\
    not_fresh_at (sa with cs_next_var := st1.cs_next_var + 2) p /\
    not_fresh_at (sa with cs_next_var := st1.cs_next_var + 2) idx /\
    (!x. lvo = Var x ==> not_fresh_at (sa with cs_next_var := st1.cs_next_var + 2) x) /\
    (!x. not_fresh_at (sa with cs_next_var := st1.cs_next_var + 2) x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `cut = sa with cs_next_var := st1.cs_next_var + 2` >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `st.cs_next_var <= st1.cs_next_var` by
    (qpat_x_assum `(if dyn then _ else _) st = (lvo,st1)` mp_tac >>
     qpat_x_assum `~cenv.ce_is_ctor` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> Cases_on `dyn` >>
     simp[contextTheory.compile_imm_load_word_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def] >> rpt strip_tac >> gvs[]) >>
  `st.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb0.cs_next_var /\
   not_fresh_at cut p /\ not_fresh_at cut idx /\
   ~not_fresh_at cut ov /\ ~not_fresh_at cut tot /\ ~not_fresh_at cut ep /\
   ov <> tot` by
    (Cases_on `dyn` >> gvs[Abbr `cut`, Abbr `tot`, not_fresh_at_def]) >>
  `!x. not_fresh_at cut x ==> not_fresh_at sa x` by
    (simp[not_fresh_at_def, Abbr `cut`] >> rpt strip_tac >>
     Cases_on `dyn` >> gvs[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `local_ptrs_reserved cenv cut` by
    (irule local_ptrs_reserved_next_var >> qexists `st1` >> simp[Abbr `cut`]) >>
  drule_all immutable_allocation_ready >> strip_tac >>
  `bc.ce_return_buf = cenv.ce_return_buf /\ bc.ce_is_ctor = cenv.ce_is_ctor` by
    (drule_all declare_local_ptr >> strip_tac >>
     qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = _`
       (fn th => mp_tac (AP_TERM ``\c. (c.ce_return_buf,c.ce_is_ctor)`` th)) >> simp[]) >>
  qhdtm_assum `array_loop_inv` mp_tac >>
  pure_rewrite_tac[array_loop_inv_def] >> strip_tac >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x` by
    (rpt strip_tac >>
     `not_fresh_at st x` by metis_tac[ret_pc_ok_def] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
   not_local_ptr cenv es.scopes ep` by
    (rpt conj_tac >> simp[Abbr `tot`] >>
     irule local_ptrs_reserved_fresh >> qexists `st1` >> simp[]) >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule cenv_top_ext_declare_local >>
     qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  `not_local_ptr bc (FEMPTY :: es.scopes) p` by
    (irule local_ptrs_reserved_not_live >>
     conj_tac >- (qexistsl [`id`, `type_memory_bytes cenv et`] >> simp[lookup_scopes_def]) >>
     qexists `sa` >> simp[]) >>
  `w2n dst + type_memory_bytes cenv et < dimword (:256)` by
    (drule immutable_entry_allocation_bound >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  `immutable_holds cenv cx et (Value (EL k vs))
    (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) es s` by
    (qpat_assum `!ei t j. _ ==> immutable_holds _ _ _ _ _ _ _` drule_all >> simp[]) >>
  `toto = Var (if dyn then tot else ov)` by
    (Cases_on `dyn` >> simp[Abbr `tot`]) >>
  `isPREFIX sa.cs_current_insts bb.bb_instructions` by
    (fs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `isPREFIX
    ([mk_inst h MUL [Var idx; Lit (n2w (type_memory_size tv))] [ov]] ++
     (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[DROP_0] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all immutable_address_entry_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  `!x. not_fresh_at cut x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_allocas = s.vs_allocas /\
   u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted` by
    (Cases_on `dyn` >> simp[Abbr `u`, update_var_def]) >>
  `ptr_covers H tm p u (type_memory_bytes cenv et)` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  `lookup_var p u = SOME dst` by metis_tac[] >>
  `FLOOKUP u.vs_allocas
    (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p]).inst_id =
      SOME (w2n dst,type_memory_bytes cenv et)` by metis_tac[] >>
  `copy_old_operand sa (Var ep)` by
    (Cases_on `dyn` >> simp[copy_old_operand_def, not_fresh_at_def]) >>
  `eval_operand (Var ep) u = SOME
    (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv))` by
    (Cases_on `dyn` >> simp[Abbr `u`, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     bc.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by metis_tac[] >>
  drule immutable_copy_scope_ptr_from_copy >>
  disch_then (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ H tm u`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `FLOOKUP bc.ce_vars id = SOME _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts func)`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var p u = SOME _`)) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  (impl_tac >- (simp[mk_inst_def] >> metis_tac[])) >>
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE])
     (emitted_insts sa sb0)` by
    (drule immutable_iter_copy_opcodes >> strip_tac >>
     `code = emitted_insts sa sb0` by metis_tac[APPEND_11] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb0) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb0)) = 0` by
    (qpat_assum `EVERY _ (emitted_insts sa sb0)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL] >>
     strip_tac >> conj_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> disch_then strip_assume_tac >>
     simp[is_terminator_def]) >>
  `isPREFIX (emitted_insts sa sb0) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (`bb.bb_instructions = sa.cs_current_insts ++ emitted_insts sa sb0 ++
        DROP (LENGTH sb0.cs_current_insts) bb.bb_instructions` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND, DROP_PREFIX, APPEND_ASSOC] >>
     qpat_assum `u.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `bb.bb_instructions = _`
       (fn th => once_rewrite_tac[th]) >>
     metis_tac[GSYM APPEND_ASSOC, DROP_PREFIX, rich_listTheory.IS_PREFIX_APPEND]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  `run_inst_seq (emitted_insts sa sb0) u = OK t` by fs[copy_runtime_frame_def] >>
  `inst_seq_ptr D 0 ctx func PG H tm (emitted_insts sa sb0) u H' tm'` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `u.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  qpat_assum `LENGTH (FILTER _ (emitted_insts sa sb0)) = 0`
    (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  qabbrev_tac `v = t with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sa sb0)` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 H' tm' (OK v)` by
    (SIMP_TAC bool_ss [Abbr `v`, NoAsms] >>
     qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ H tm u _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  drule_all immutable_iter_copy_state_frame >> strip_tac >>
  `!x. not_fresh_at cut x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H' x = FLOOKUP G x /\ op_taint tm' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[] >>
     `copy_old_operand sa (Var x)` by simp[copy_old_operand_def] >>
     drule_all immutable_copy_ghost_frame_operand >>
     simp[eval_operand_def] >> strip_tac >>
     fs[immutable_copy_ghost_frame_def] >> metis_tac[]) >>
  `t.vs_current_bb = u.vs_current_bb /\ t.vs_halted = u.vs_halted /\
   t.vs_allocas = u.vs_allocas /\ t.vs_labels = u.vs_labels` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _|> = u`
       (fn th => map_every (fn f => mp_tac (AP_TERM f th))
         [``\z. z.vs_current_bb``, ``\z. z.vs_halted``, ``\z. z.vs_allocas``, ``\z. z.vs_labels``]) >> simp[]) >>
  `lookup_var p t = SOME dst /\ lookup_var idx t = SOME (n2w k)` by metis_tac[] >>
  `eval_operand lvo t = SOME (n2w (LENGTH vs)) /\
   op_prov H' lvo = NONE /\ op_taint tm' lvo = {}` by
    (`copy_old_operand sa lvo` by
       (qpat_assum `copy_old_operand st1 lvo` mp_tac >>
        qpat_assum `sa.cs_next_var = _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >>
        `st1.cs_next_var <= n` by (Cases_on `dyn` >> gvs[] >> decide_tac) >> metis_tac[]) >>
     `copy_old_operand cut lvo` by
       (simp[Abbr `cut`, NoAsms, copy_old_operand_def] >>
        qpat_assum `copy_old_operand st1 lvo` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[copy_old_operand_def, not_fresh_at_def] >>
        rpt strip_tac >> `st1.cs_next_var <= n` by decide_tac >> metis_tac[]) >>
     `t.vs_labels = s.vs_labels` by (Cases_on `dyn` >> fs[Abbr `u`, update_var_def]) >>
     qpat_assum `t.vs_labels = s.vs_labels` mp_tac >>
     qpat_assum `!x. not_fresh_at cut x ==> _` mp_tac >>
     qpat_assum `copy_old_operand cut lvo` mp_tac >>
     qpat_assum `eval_operand lvo s = _` mp_tac >>
     qpat_assum `op_prov G lvo = _` mp_tac >>
     qpat_assum `op_taint tn lvo = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `lvo` >> simp[copy_old_operand_def,
       op_prov_def, op_taint_def, eval_operand_def] >> metis_tac[]) >>
  `ret_pc_ok bc sb0 t` by
    (irule ret_pc_ok_frame >> qexistsl [`cenv`, `s`, `st`] >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at cut x` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `run_inst_seq sa.cs_current_insts s = OK
    (update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv))
      (if dyn then update_var tot (n2w (32 + k * type_memory_size tv))
         (update_var ov (n2w (k * type_memory_size tv)) s)
       else update_var ov (n2w (k * type_memory_size tv)) s))` by
    (qpat_assum `sa.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `elem_size_in_location cenv LocCode et = _`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `toto = Var (if dyn then tot else ov)`
       (fn th => pure_rewrite_tac[th]) >>
     irule immutable_address_prefix_run >> simp[]) >>
  `run_inst_seq sa.cs_current_insts s = OK (u with vs_inst_idx := s.vs_inst_idx)` by
    (Cases_on `dyn` >> fs[Abbr `u`, update_var_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) sa.cs_current_insts` by
    (qpat_assum `sa.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `dyn` >> simp[mk_inst_def, is_terminator_def]) >>
  `DROP s.vs_inst_idx bb.bb_instructions = sa.cs_current_insts ++
      DROP (LENGTH sa.cs_current_insts) bb.bb_instructions` by
    (qpat_assum `isPREFIX sa.cs_current_insts bb.bb_instructions` mp_tac >>
     qpat_assum `s.vs_inst_idx = 0` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> rpt strip_tac >>
     gvs[DROP_PREFIX]) >>
  `alloca_inv s /\ alloca_inv u` by metis_tac[stmt_state_rel_def] >>
  `alloca_history func u` by
    (qpat_assum `run_inst_seq sa.cs_current_insts s = OK (u with vs_inst_idx := _)` mp_tac >>
     qpat_assum `alloca_history func s` mp_tac >>
     qpat_assum `alloca_inv s` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `DROP s.vs_inst_idx bb.bb_instructions = sa.cs_current_insts ++ _` mp_tac >>
     qpat_assum `EVERY _ sa.cs_current_insts` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     qpat_assum `s.vs_inst_idx = 0` mp_tac >>
     qpat_assum `u.vs_inst_idx = LENGTH sa.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_all alloca_history_run_inst_seq >> simp[] >>
     strip_tac >> irule alloca_history_frame >>
     qexists `u with vs_inst_idx := LENGTH sa.cs_current_insts` >> simp[]) >>
  `DROP u.vs_inst_idx bb.bb_instructions = emitted_insts sa sb0 ++
     DROP (u.vs_inst_idx + LENGTH (emitted_insts sa sb0)) bb.bb_instructions` by
    (qpat_assum `isPREFIX (emitted_insts sa sb0) (DROP u.vs_inst_idx bb.bb_instructions)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> rpt strip_tac >>
     metis_tac[rich_listTheory.DROP_DROP_T, DROP_PREFIX]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb0)` by
    (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >> simp[]) >>
  `alloca_history func v` by
    (SIMP_TAC bool_ss [Abbr `v`, NoAsms] >>
     qpat_assum `run_inst_seq (emitted_insts sa sb0) u = OK t` mp_tac >>
     qpat_assum `alloca_history func u` mp_tac >>
     qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `DROP u.vs_inst_idx bb.bb_instructions = emitted_insts sa sb0 ++ _` mp_tac >>
     qpat_assum `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb0)` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_all alloca_history_run_inst_seq >> simp[]) >>
  qexistsl [`v`, `H'`, `tm'`] >>
  simp[Abbr `v`, stmt_state_rel_inst_idx, lookup_var_def] >>
  conj_tac >-
    (qpat_assum `ret_pc_ok bc sb0 t` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ret_pc_ok_def, lookup_var_def]) >>
  qpat_assum `lookup_var p t = SOME dst` mp_tac >>
  qpat_assum `lookup_var idx t = SOME (n2w k)` mp_tac >>
  simp[lookup_var_def, mk_inst_def] >>
  conj_tac >-
    (qpat_assum `lookup_var p t = SOME dst` mp_tac >>
     qpat_assum `p = _` mp_tac >> rpt (pop_assum kall_tac) >> simp[lookup_var_def]) >>
  conj_tac >-
    (qpat_assum `lookup_var idx t = SOME (n2w k)` mp_tac >>
     qpat_assum `idx = _` mp_tac >> rpt (pop_assum kall_tac) >> simp[lookup_var_def]) >>
  conj_tac >-
    (qpat_assum `FLOOKUP s.vs_allocas (mk_inst _ _ _ _).inst_id = _` mp_tac >>
     qpat_assum `type_memory_bytes cenv et = type_memory_size tv` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[mk_inst_def]) >>
  conj_tac >-
    (qpat_assum `copy_old_operand st1 lvo` mp_tac >>
     simp[Abbr `cut`, NoAsms] >>
     rpt (pop_assum kall_tac) >>
     simp[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >>
     `st1.cs_next_var <= n` by decide_tac >> metis_tac[]) >>
  qpat_assum `!x. not_fresh_at cut x ==> lookup_var x t = _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[lookup_var_def]
QED
