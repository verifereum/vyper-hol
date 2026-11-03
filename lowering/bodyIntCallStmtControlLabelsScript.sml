(* Control-flow boundaries for statement compiler history and reservations. *)
Theory bodyIntCallStmtControlLabels
Ancestors
  bodyIntCallStmtHelperLabels bodyIntCallLabelReservations
  bodyIntCallLabelFrame bodyIntCallContextLabels compileEnv emitHelper pred_set
  stmtLowering list

Theorem compiler_label_reservation_weaken:
  compiler_label_reservation origin pending st /\ pending' SUBSET pending ==>
  compiler_label_reservation origin pending' st
Proof
  simp[compiler_label_reservation_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem compiler_block_tail_termination_read:
  (!b. compiler_block_tail (k b)) ==>
  compiler_block_tail
    (comp_bind comp_get (\st. k (block_is_terminated st)))
Proof
  simp[compiler_block_tail_def, comp_bind_def, comp_get_def,
       block_is_terminated_def]
QED

Theorem compiler_label_hoare_termination_read:
  (!b. compiler_label_hoare P (k b) Q) ==>
  compiler_label_hoare P
    (comp_bind comp_get (\st. k (block_is_terminated st))) Q
Proof
  simp[compiler_label_hoare_def, comp_bind_def, comp_get_def] >> metis_tac[]
QED

Theorem compiler_block_tail_jmp_if_not_terminated:
  compiler_block_tail (emit_jmp_if_not_terminated lbl)
Proof
  rewrite_tac[emit_jmp_if_not_terminated_def] >>
  ho_match_mp_tac compiler_block_tail_termination_read >> gen_tac >> BETA_TAC >>
  Cases_on `b` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_jmp_if_not_terminated:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (emit_jmp_if_not_terminated lbl)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[emit_jmp_if_not_terminated_def] >>
  ho_match_mp_tac compiler_label_hoare_termination_read >> gen_tac >> BETA_TAC >>
  Cases_on `b` >> simp[compiler_label_hoare_context_primitives] >>
  simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_if_branches:
  compiler_block_tail yes /\ compiler_block_tail no ==>
  compiler_block_tail
    (do new_block tl; yes;
        st <- comp_get;
        emit_jmp_if_not_terminated xl;
        new_block el; no;
        st' <- comp_get;
        emit_jmp_if_not_terminated xl;
        if ~block_is_terminated st \/ ~block_is_terminated st' then
          do new_block xl; return () od
        else return ()
     od)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_termination_read >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_jmp_if_not_terminated] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_termination_read >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_jmp_if_not_terminated] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_cond >> conj_tac
  >- (irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_if_branches:
  tl <> el /\ tl <> xl /\ el <> xl /\
  tl NOTIN pending /\ el NOTIN pending /\ xl NOTIN pending /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p) yes
      (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p) no
      (\r out. compiler_label_reservation orig p out)) ==>
  compiler_label_hoare
    (compiler_label_reservation origin (xl INSERT el INSERT tl INSERT pending))
    (do new_block tl; yes;
        st <- comp_get;
        emit_jmp_if_not_terminated xl;
        new_block el; no;
        st' <- comp_get;
        emit_jmp_if_not_terminated xl;
        if ~block_is_terminated st \/ ~block_is_terminated st' then
          do new_block xl; return () od
        else return ()
     od)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `(xl INSERT el INSERT tl INSERT pending) DELETE tl = el INSERT xl INSERT pending` by ASM_SET_TAC[] >>
  `(el INSERT xl INSERT pending) DELETE el = xl INSERT pending` by ASM_SET_TAC[] >>
  `(xl INSERT pending) DELETE xl = pending` by ASM_SET_TAC[] >>
  rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_termination_read >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_jmp_if_not_terminated] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_termination_read >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_jmp_if_not_terminated] >> gen_tac >> BETA_TAC >>
  IF_CASES_TAC
  >- (irule compiler_label_hoare_new_block_bind >> simp[] >>
      simp[compiler_label_hoare_def, comp_return_def]) >>
  simp[compiler_label_hoare_def, comp_return_def] >> rpt strip_tac >>
  irule compiler_label_reservation_weaken >>
  qexists_tac `xl INSERT pending` >> simp[]
QED

Theorem compiler_block_tail_stmt_if:
  compiler_block_tail (lower_value compile_expr ce (BaseT BoolT) e) /\
  compiler_block_tail (compile_stmts ce lc ty yes) /\
  compiler_block_tail (compile_stmts ce lc ty no) ==>
  compiler_block_tail (compile_stmt ce lc ty (If e yes no))
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, comp_ignore_bind_def,
    tuple_comp_return_bind] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  pure_rewrite_tac[GSYM comp_ignore_bind_def] >>
  irule compiler_block_tail_if_branches >> simp[]
QED

Theorem compiler_label_hoare_stmt_if:
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (lower_value compile_expr ce (BaseT BoolT) e)
    (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (compile_stmts ce lc ty yes)
    (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (compile_stmts ce lc ty no)
    (\r out. compiler_label_reservation orig p out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lc ty (If e yes no))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, comp_ignore_bind_def,
    tuple_comp_return_bind] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> rpt strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> rpt strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> rpt strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  pure_rewrite_tac[GSYM comp_ignore_bind_def] >>
  irule compiler_label_hoare_if_branches >> gvs[]
QED


(* Once the entry has materialized the counter/end operands, the remaining
   blocks have the same topology for range and array iteration. *)
Theorem compiler_block_tail_loop_blocks:
  compiler_block_tail test_action /\ compiler_block_tail body_action /\
  compiler_block_tail incr_action ==>
  compiler_block_tail
    (do new_block co; test_action;
        new_block bl; body_action;
        new_block ic; incr_action;
        new_block ex; return () od)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_loop_blocks:
  ALL_DISTINCT [co; bl; ic; ex] /\ DISJOINT {co; bl; ic; ex} pending /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p) test_action
    (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p) body_action
    (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p) incr_action
    (\r out. compiler_label_reservation orig p out)) ==>
  compiler_label_hoare
    (compiler_label_reservation origin
      (ex INSERT ic INSERT bl INSERT co INSERT pending))
    (do new_block co; test_action;
        new_block bl; body_action;
        new_block ic; incr_action;
        new_block ex; return () od)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[ALL_DISTINCT, DISJOINT_DEF, EXTENSION] >> strip_tac >>
  `(ex INSERT ic INSERT bl INSERT co INSERT pending) DELETE co =
    ex INSERT ic INSERT bl INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT bl INSERT pending) DELETE bl =
    ex INSERT ic INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT pending) DELETE ic = ex INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT pending) DELETE ex = pending` by ASM_SET_TAC[] >>
  rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_range_operands:
  compiler_block_tail
    (case (a,b) of (Lit x,Lit y) => comp_return (Lit (y-x))
     | _ => emit_op SUB [b;a]) /\
  compiler_block_tail
    (case (a,b) of (Lit x,Lit y) => comp_return ()
     | _ => compile_range_bound_checks a b rounds bound signed)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[compiler_block_tail_primitives, compiler_block_tail_range_bound_checks]
QED

Theorem compiler_block_tail_range_store:
  compiler_block_tail
    (case FLOOKUP ce.ce_vars id of
       SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off); v]
     | SOME (PtrVar op _) => emit_void MSTORE [op; v]
     | _ => emit_void INVALID [])
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_stmt_range:
  compiler_block_tail (lower_value compile_expr ce fty start_e) /\
  compiler_block_tail (lower_value compile_expr ce fty end_e) /\
  (!bce ex ic. compiler_block_tail (compile_stmts bce (InLoop ex ic) ty ss)) ==>
  compiler_block_tail (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound ss))
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_declare_local,
               compiler_block_tail_emit_local_alloca, compiler_block_tail_range_operands,
               compiler_block_tail_range_store, compiler_block_tail_jmp_if_not_terminated] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_stmt_range_return_pc:
  compiler_block_tail (lower_value compile_expr ce fty start_e) /\
  compiler_block_tail (lower_value compile_expr ce fty end_e) /\
  (!bce ex ic. bce.ce_return_pc = ce.ce_return_pc ==>
    compiler_block_tail (compile_stmts bce (InLoop ex ic) ty ss)) ==>
  compiler_block_tail (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound ss))
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  ntac 2 (irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
          gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_declare_local_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_emit_local_alloca,
               compiler_block_tail_range_operands, compiler_block_tail_range_store,
               compiler_block_tail_jmp_if_not_terminated] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_range_operands:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (case (a,b) of (Lit x,Lit y) => comp_return (Lit (y-x))
     | _ => emit_op SUB [b;a])
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (case (a,b) of (Lit x,Lit y) => comp_return ()
     | _ => compile_range_bound_checks a b rounds bound signed)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_range_bound_checks] >>
  simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_label_hoare_range_store:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (case FLOOKUP ce.ce_vars id of
       SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off); v]
     | SOME (PtrVar op _) => emit_void MSTORE [op; v]
     | _ => emit_void INVALID [])
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_stmt_range:
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (lower_value compile_expr ce fty start_e)
    (\r out. compiler_label_reservation orig p out)) /\
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (lower_value compile_expr ce fty end_e)
    (\r out. compiler_label_reservation orig p out)) /\
  (!bce ex ic orig p. bce.ce_return_pc = ce.ce_return_pc ==>
    compiler_label_hoare (compiler_label_reservation orig p)
      (compile_stmts bce (InLoop ex ic) ty ss)
      (\r out. compiler_label_reservation orig p out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound ss))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  ntac 2 (irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
          gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_declare_local_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_emit_local_alloca] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `en` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `co` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `bl` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `ic` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `ex` >> strip_tac >> BETA_TAC >>
  `(ex INSERT ic INSERT bl INSERT co INSERT en INSERT pending) DELETE en =
    ex INSERT ic INSERT bl INSERT co INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT bl INSERT co INSERT pending) DELETE co =
    ex INSERT ic INSERT bl INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT bl INSERT pending) DELETE bl = ic INSERT ex INSERT pending` by ASM_SET_TAC[] >>
  `(ic INSERT ex INSERT pending) DELETE ic = ex INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT pending) DELETE ex = pending` by ASM_SET_TAC[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, SRULE [] compiler_label_hoare_range_operands] >>
       gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_range_store, compiler_label_hoare_jmp_if_not_terminated] >>
       gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_iter_store:
  compiler_block_tail
    (case FLOOKUP bce.ce_vars id of
       SOME (MemLoc off _) => compile_iter_elem_copy ce elem_ptr (Lit (n2w off)) sz loc slot ty ety
     | SOME (PtrVar op _) => compile_iter_elem_copy ce elem_ptr op sz loc slot ty ety
     | _ => emit_void INVALID [])
Proof
  Cases_on `FLOOKUP bce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `SOME dest` >> Cases_on `dest` >>
  simp[compiler_block_tail_primitives, compiler_block_tail_iter_elem_copy]
QED

Theorem compiler_label_hoare_iter_store:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (case FLOOKUP bce.ce_vars id of
       SOME (MemLoc off _) => compile_iter_elem_copy ce elem_ptr (Lit (n2w off)) sz loc slot ty ety
     | SOME (PtrVar op _) => compile_iter_elem_copy ce elem_ptr op sz loc slot ty ety
     | _ => emit_void INVALID [])
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `FLOOKUP bce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `SOME dest` >> Cases_on `dest` >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_iter_elem_copy]
QED

Theorem compiler_block_tail_iter_bound:
  compiler_block_tail
    (if dyn /\ bound > 0 then
       do invalid <- emit_op GT [len; Lit (n2w bound)];
          valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
     else return ())
Proof
  IF_CASES_TAC >> simp[compiler_block_tail_primitives] >>
  rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_iter_bound:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (if dyn /\ bound > 0 then
       do invalid <- emit_op GT [len; Lit (n2w bound)];
          valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
     else return ())
    (\r out. compiler_label_reservation origin pending out)
Proof
  IF_CASES_TAC
  >- (rewrite_tac[comp_ignore_bind_def] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
  simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_stmt_array:
  compiler_block_tail (compile_expr ce (expr_type arr) arr) /\
  (!bce ex ic. bce.ce_return_pc = ce.ce_return_pc ==>
    compiler_block_tail (compile_stmts bce (InLoop ex ic) ty ss)) ==>
  compiler_block_tail (compile_stmt ce lc ty (For id fty (Array arr) bound ss))
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, LET_THM, comp_ignore_bind_def,
    tuple_comp_return_bind] >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_cond >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_declare_local_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_emit_local_alloca,
               compiler_block_tail_iter_bound, compiler_block_tail_iter_store,
               compiler_block_tail_jmp_if_not_terminated, compiler_block_tail_cond] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_cond[local]:
  compiler_label_hoare P m Q /\ compiler_label_hoare P n Q ==>
  compiler_label_hoare P (if b then m else n) Q
Proof Cases_on `b` >> simp[]
QED

Theorem compiler_label_hoare_return_preserves[local]:
  compiler_label_hoare P (comp_return v) (\r out. P out)
Proof simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_label_hoare_stmt_array:
  (!orig p. compiler_label_hoare (compiler_label_reservation orig p)
    (compile_expr ce (expr_type arr) arr)
    (\r out. compiler_label_reservation orig p out)) /\
  (!bce ex ic orig p. bce.ce_return_pc = ce.ce_return_pc ==>
    compiler_label_hoare (compiler_label_reservation orig p)
      (compile_stmts bce (InLoop ex ic) ty ss)
      (\r out. compiler_label_reservation orig p out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lc ty (For id fty (Array arr) bound ss))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_stmt_def, LET_THM, comp_ignore_bind_def,
    tuple_comp_return_bind] >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_cond, compiler_label_hoare_context_primitives,
          compiler_label_hoare_return_preserves] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_declare_local_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_emit_local_alloca, compiler_label_hoare_iter_bound] >>
       gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `en` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `co` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `bl` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `ic` >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_fresh_bind >> qx_gen_tac `ex` >> strip_tac >> BETA_TAC >>
  `(ex INSERT ic INSERT bl INSERT co INSERT en INSERT pending) DELETE en =
    ex INSERT ic INSERT bl INSERT co INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT bl INSERT co INSERT pending) DELETE co =
    ex INSERT ic INSERT bl INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT ic INSERT bl INSERT pending) DELETE bl = ic INSERT ex INSERT pending` by ASM_SET_TAC[] >>
  `(ic INSERT ex INSERT pending) DELETE ic = ex INSERT pending` by ASM_SET_TAC[] >>
  `(ex INSERT pending) DELETE ex = pending` by ASM_SET_TAC[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_iter_store, compiler_label_hoare_jmp_if_not_terminated,
               compiler_label_hoare_context_primitives, compiler_label_hoare_cond,
               compiler_label_hoare_return_preserves] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  simp[compiler_label_hoare_def, comp_return_def]
QED
