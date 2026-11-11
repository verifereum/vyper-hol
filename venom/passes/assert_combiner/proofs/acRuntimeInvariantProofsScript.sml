Theory acRuntimeInvariantProofs
Ancestors
  acRuntimeInvariantDefs acChainProofs acBaseProofs assertCombinerDefs
  venomWf venomWfProps venomExecProofs venomExecProps venomExecSemantics
  venomState venomInst dfgDefs dfgAnalysisProps finite_map list

(* Only the queried chain must belong to the local invariant. Arbitrary
   initial variable bindings need not correspond to executed definitions. *)
Theorem ac_dfg_iszero_bridge_query:
  !dfg visited op s pred P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg visited op = SOME pred /\
    IS_SOME (eval_operand op s) /\
    (!v di. op = Var v /\ dfg_get_def dfg v = SOME di ==> P di) /\
    (!di src v dj. P di /\ di.inst_opcode = ASSIGN /\
       di.inst_operands = [src] /\ src = Var v /\
       dfg_get_def dfg v = SOME dj ==> P dj) ==>
    ?p. eval_operand pred s = SOME p /\
        eval_operand op s = SOME (bool_to_word (p = 0w))
Proof
  recInduct ac_get_iszero_operand_ind >> rpt strip_tac >>
  qpat_x_assum `ac_get_iszero_operand _ _ _ = _` mp_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  Cases_on `op` >> simp[] >>
  Cases_on `dfg_get_def dfg s'` >> simp[] >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  Cases_on `x.inst_opcode = ISZERO` >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac >>
  Cases_on `x.inst_opcode = ASSIGN` >> gvs[]
  >- (fs[ac_dfg_inv_local_def, eval_operand_def] >> metis_tac[]) >>
  `P x` by metis_tac[] >>
  `lookup_var s' s = eval_operand h s` by
    (fs[ac_dfg_inv_local_def, eval_operand_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`s`, `P`] mp_tac) >>
  impl_tac
  >- (simp[] >> fs[eval_operand_def] >> metis_tac[]) >>
  strip_tac >> gvs[eval_operand_def]
QED

Theorem ac_cursor_iszero_bridge:
  wf_function fn /\ wf_ssa fn /\ ac_cursor_inv fn bb idx s /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  MEM op (EL idx bb.bb_instructions).inst_operands /\
  ac_get_iszero_operand (dfg_build_function fn) visited op = SOME pred /\
  IS_SOME (eval_operand op s) ==>
  ?p. eval_operand pred s = SOME p /\
      eval_operand op s = SOME (bool_to_word (p = 0w))
Proof
  rpt strip_tac >> irule ac_dfg_iszero_bridge_query >>
  simp[] >>
  qexistsl [`ac_def_before fn bb idx`, `dfg_build_function fn`, `visited`] >>
  fs[ac_cursor_inv_def] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[] >> irule ac_query_use_before >> metis_tac[]) >>
  rpt strip_tac >>
  `?db j. MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = di` by
    (fs[ac_def_before_def] >> metis_tac[EL_MEM, MEM_EL]) >>
  irule ac_query_before_closed >> simp[] >>
  qexistsl [`db`, `j`, `v`] >> simp[]
QED

(* Totality is cursor-local: a safe gap may compute inputs needed later. *)
Theorem ac_cursor_safe_step_ok:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb idx s /\ idx < LENGTH bb.bb_instructions /\
  ac_is_safe_between (EL idx bb.bb_instructions) /\
  (!l. MEM (Label l) (EL idx bb.bb_instructions).inst_operands ==>
       l IN FDOM s.vs_labels) ==>
  ?s'. step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s'
Proof
  rpt strip_tac >> irule safe_between_wf_step_ok >> simp[] >>
  reverse conj_tac
  >- (fs[fn_inst_wf_def, ac_cursor_inv_def] >> metis_tac[EL_MEM]) >>
  Cases >> simp[eval_operand_def]
  >- (strip_tac >> irule ac_cursor_use_defined >>
      fs[ac_is_safe_between_def] >> metis_tac[]) >>
  simp[FLOOKUP_DEF]
QED
