(* Seam 2 joint induction, For family: iteration over an array, split by
   iterator form: a fixed local, a dynamic local, an immutable, or a
   general expression. *)
Theory bodyIntCallFamStmtForArray
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArrayFixed
  bodyIntCallFamStmtForDynArray bodyIntCallFamStmtForImm
  bodyIntCallFamStmtForMemIterable supportedStmts vyperAST

(* A local Name iterator that is not an array of the loop type is not
   supported. *)
Theorem intcall_stmts_producer_for_unsupported_name[local]:
  (?ty name. arr = Name ty name) /\
  ~(?m name. arr = Name (ArrayT fty (Fixed m)) name) /\
  ~(?c name. arr = Name (ArrayT fty (Dynamic c)) name) ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  rpt strip_tac >> gvs[] >>
  simp[intcall_stmts_producer_def, supported_stmts_list] >>
  rpt strip_tac >>
  gvs[supported_stmt_def, supported_iterator_def, AllCaseEqs()] >>
  Cases_on `ty` >> gvs[] >> rename1 `ArrayT _ bd` >> Cases_on `bd` >> gvs[]
QED

Theorem intcall_stmts_producer_for_array:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  strip_tac >>
  Cases_on `?m name. arr = Name (ArrayT fty (Fixed m)) name`
  >- (irule intcall_stmts_producer_for_fixed_array >> simp[]) >>
  Cases_on `?c name. arr = Name (ArrayT fty (Dynamic c)) name`
  >- (irule intcall_stmts_producer_for_dynarray_name >> simp[]) >>
  Cases_on `?ty name. arr = Name ty name`
  >- (irule intcall_stmts_producer_for_unsupported_name >> fs[]) >>
  Cases_on `?ty nid. arr = TopLevelName ty nid`
  >- (gvs[] >> irule intcall_stmts_producer_for_immutable_array >> simp[]) >>
  irule intcall_stmts_producer_for_memory_iterable >> fs[]
QED
