Theory bodyPtrPopStatementBoundary
Ancestors bodyPtrPopMutualBoundary bodyPtrPopCompilerBoundary
  supportedStmts stmtLowering vyperAST list

(* This rephrases the generated compiler induction without its incidental
   let-bound variables. Environments for loop bodies and declaration tails
   remain universally quantified. It asserts no producer preservation. *)
Theorem pop_statement_boundary_induction:
  !P Q.
  (!(ce:compile_env) lc (ty:type) s.
    (case s of
       If c yes no => Q ce lc ty yes /\ Q ce lc ty no
     | For id fty it n loop_body => !ce' exit incr. Q ce' (InLoop exit incr) ty loop_body
     | _ => T) ==> P ce lc ty s) /\
  (!ce lc ty. Q ce lc ty []) /\
  (!ce lc ty s ss.
    (!cs ce'. ~block_is_terminated cs ==> P ce' lc ty s) /\
    (!cs ce'. ~block_is_terminated cs ==> Q ce' lc ty ss) ==> Q ce lc ty (s::ss)) ==>
  (!ce lc ty s. P ce lc ty s) /\ (!ce lc ty ss. Q ce lc ty ss)
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac compile_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  FIRST_PROVE [first_assum MATCH_ACCEPT_TAC,
    (qpat_x_assum `!ce lc ty s ss. _` irule >> metis_tac[]),
    (qpat_x_assum `!ce lc ty s. _` irule >> simp[] >> metis_tac[])]
QED
