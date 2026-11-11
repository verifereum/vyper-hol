(* Typed tuple loads retain a supplied owned-or-borrowed snapshot. *)
Theory assignTupleSnapshotLoadsPtr
Ancestors
  assignTuplePtrLoads tuplePlacePrefixCert bodyPtrDefs stmtLowering
  compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueTypingMemoryProps vyperAST
  exprLoweringProps exprSimProps fragExec fragGasPathPtr
  venomState venomExecSemantics words finite_map context

Theorem compile_tuple_load_all_snapshot_path_ptr:
  !cenv bop tys sa elems sb cx tvs vals s w G tn ctx func d es PG D
    lo hi hi' ats.
  compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
  (!p. bop = Var p ==> not_fresh_at sa p) /\
  eval_operand bop s = SOME w /\
  (?p b cap. bop = Var p /\ op_taint tn bop = {} /\
    FLOOKUP G p = SOME (b,cap) /\ b <= w2n w /\
    w2n w + type_memory_size_list tvs <= b+cap) /\
  w2n w + type_memory_size_list tvs < dimword (:256) /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vals /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       tuple_in_memory vals tvs (w2n w) m) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  tuple_place_snapshot cenv cx es lo hi ats tys tvs w s /\ hi <= hi' ==>
  LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) elems /\
  local_ptrs_reserved cenv sb /\
  ?p b cap t G' tn'. bop = Var p /\ FLOOKUP G p = SOME (b,cap) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q)) /\
    tuple_in_memory vals tvs (w2n w) t.vs_memory /\
    (!n base sz. local_region cenv es.scopes t n base sz <=>
                 local_region cenv es.scopes s n base sz) /\
    (!i. i < LENGTH tys ==>
      ptr_val_ok cx (EL i tys) (EL i vals) (EL i elems) G' tn' t /\
      (?u. eval_operand (EL i elems) t = SOME u /\
        (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vals)
         else w2n u = w2n w+SUM (MAP type_memory_size (TAKE i tvs)))) /\
      (~is_word_type (EL i tys) ==>
        ?q. EL i elems = Var q /\ FLOOKUP G' q = SOME (b,cap))) /\
    tuple_place_snapshot cenv cx es lo hi' ats tys tvs w t
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`) compile_tuple_load_all_typed_path_ptr >>
  disch_then (drule_at (Pat `values_have_types _ _`)) >>
  disch_then (drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `tuple_place_snapshot cenv cx es lo hi' ats tys tvs w t` by
    metis_tac[tuple_place_snapshot_transport] >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED
