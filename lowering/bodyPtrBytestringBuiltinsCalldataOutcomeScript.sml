Theory bodyPtrBytestringBuiltinsCalldataOutcome
Ancestors
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsSliceEndpoint
  exprSimSource exprSimWordArgs exprSimDefs exprSimHypsDefs
  vyperTyping valueEncoding words integer compileEnv vyperValue loweringSlice
  allocationPtr bodyMemoryDefs exprSimBuffer venomExecSemantics venomInst
  ptrDiscipline venomState finite_map exprLoweringProps venomMemDefs

(* The marked operand evidence fixes both the source integer and its actual
   runtime word; no independent existential execution is introduced. *)
Theorem calldata_slice_operand_endpoint:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  ?a. v = IntV (&a) /\ a < 2 ** 256 /\
    eval_operand op t = SOME (n2w a) /\ expr_sim_inv cenv cx env ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all operand_eval_evidence_semantics >> strip_tac >>
  `?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256` by
    (fs[is_word_type_def, evaluate_type_def] >> Cases_on `v` >>
     gvs[is_word_type_def, evaluate_type_def, value_has_type_def]) >>
  gvs[] >> qexists_tac `Num i` >> simp[] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule expr_post_word_operand >>
  simp[is_word_type_def, evaluate_type_def, word_value_def, val_to_w256_def,
    integer_wordTheory.i2w_def]
QED

(* Reused allocation sites introduce no new bytes; a genuinely new site starts
   at the frontier.  Both cases are needed for loop/re-entry executions. *)
Theorem alloca_new_bytes_above_frontier:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u /\
  i < s.vs_alloca_next ==>
  i NOTIN new_site_bytes s u
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_new_site_bytes >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  simp[new_site_bytes_def, update_var_def, pred_setTheory.EXTENSION,
    FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem alloca_new_bytes_protected_regions:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u ==>
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    off <= i /\ i < off + sz ==> i NOTIN new_site_bytes s u) /\
  (!name off sz i. local_region cenv es.scopes s name off sz /\
    off <= i /\ i < off + sz ==> i NOTIN new_site_bytes s u)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_then strip_assume_tac >>
      irule alloca_new_bytes_above_frontier >>
      reverse conj_tac >- metis_tac[] >>
      fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      qpat_x_assum `!aid base sz. _ ==> base + sz <= _` drule >> decide_tac) >>
  rpt gen_tac >> disch_then strip_assume_tac >>
  drule_all body_local_region_frontier >> strip_tac >>
  irule alloca_new_bytes_above_frontier >>
  reverse conj_tac >- metis_tac[] >> decide_tac
QED

Theorem alloca_slice_suffix_ghost_kept:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_mem SUBSET (tn.t_mem UNION new_site_bytes s u) ==>
  ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >> drule_all alloca_new_bytes_protected_regions >> strip_tac >>
  irule external_slice_allocated_ghost_kept >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `new_site_bytes s u` >> simp[] >> metis_tac[]
QED
