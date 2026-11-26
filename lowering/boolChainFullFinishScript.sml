(* Assign the selected Boolean to the result slot reserved at the origin. *)
Theory boolChainFullFinish
Ancestors
  boolChainFullControl boolChainWordPost exprSimWordArgs exprSimMemDefs
  vyperStorageFootprint vyperInterpreter vyperValue vyperState
  bodyPtrDefs compileEnv venomExecSemantics venomState valueEncoding loweringSlice

Theorem bool_chain_full_finish:
  emit_inst ASSIGN [src] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  eval_operand src u = SOME (val_to_w256 (BoolV b)) /\
  ptr_val_ok cx (BaseT BoolT) (BoolV b) src G tn u /\
  expr_type root = BaseT BoolT /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  local_ptrs_reserved cenv sa0 /\ ~not_fresh_at sa0 rv /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa0 x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa0 x) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  exit.cs_current_bb = xl /\ exit.cs_current_insts = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx root es0 sa0 sc s0 ee (BoolV b) op u /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn u) ==>
  ?z Gz tf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,Gz,tf) /\
    expr_post H ctx func cenv cx root es0 sa0 exit s0 ee (BoolV b) (Var rv) z /\
    z.vs_current_bb = exit.cs_current_bb /\ z.vs_inst_idx = LENGTH exit.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tf z /\
    ptr_val_ok cx (BaseT BoolT) (BoolV b) (Var rv) Gz tf z /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gz tf
Proof
  strip_tac >> `is_word_type (BaseT BoolT)` by simp[is_word_type_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn u` by
    (rpt strip_tac >> res_tac) >>
  drule_all bool_word_assign_exit_full >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tf`] >> gen_tac >> strip_tac >> res_tac >>
  `expr_post H ctx func cenv cx root es0 sa0 exit s0 ee (BoolV b) (Var rv) z` by
    (`z = jump_to xl (update_var rv (val_to_w256 (BoolV b)) u with vs_inst_idx := 0)` by
       simp[jump_to_def] >>
     pop_assum SUBST1_TAC >> irule word_post_fresh_assign_exit >>
     simp[is_word_type_def, word_value_def] >> conj_tac
     >- (qexists_tac `src` >> simp[]) >>
     qexistsl_tac [`root`,`op`,`sc`] >> simp[]) >>
  simp[] >> gvs[jump_to_def, update_var_def]
QED
