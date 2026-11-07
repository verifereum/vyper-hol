(* Diagnostic replay of E0054; not an additional semantic boundary. *)
Theory rawCallFinishScopeProbe
Ancestors rawCallFinishTotalPtr rawCallFinishStepPtr rawCallFinishCodePtr
  rawCallFinishSuffixPtr exprLoweringProps exprSimOperands bodyPtrDefs
  fragGasPathPtr compileEnv
  operandOutcomePtr oracleCallStepPtr rawCallBufferPtr rawCallDataHeaderPtr
  rawCallHeaderFramePtr rawCallKeywordPrefixPtr rawCallOperandPrefixPtr
  rawCallPrefixPtr rawCallShapePtr typedOperandsPtr wordOperandsPtr
  rawCallAllocationProofPtr rawCallMemoryFramePtr rawCallOracleProofPtr
  rawCallResultLayoutPtr rawCallResultProofPtr rawCallSourceActionPtr
  rawCallSourceDomainPtr rawCallFinishBridgePtr

(* Check saved exports, including those loaded from disk/checkpoints. *)
val audited_theories =
  ["operandOutcomePtr", "oracleCallStepPtr", "rawCallBufferPtr",
   "rawCallDataHeaderPtr", "rawCallHeaderFramePtr", "rawCallKeywordPrefixPtr",
   "rawCallOperandPrefixPtr", "rawCallPrefixPtr", "rawCallShapePtr",
   "typedOperandsPtr", "wordOperandsPtr", "rawCallAllocationProofPtr",
   "rawCallMemoryFramePtr", "rawCallOracleProofPtr", "rawCallResultLayoutPtr",
   "rawCallResultProofPtr", "rawCallSourceActionPtr", "rawCallSourceDomainPtr",
   "rawCallFinishBridgePtr", "rawCallFinishCodePtr", "rawCallFinishStepPtr",
   "rawCallFinishSuffixPtr", "rawCallFinishTotalPtr"];
val () = List.app (fn thy =>
  (List.app (fn (n,th) =>
     if null (hyp th) then ()
     else raise Fail ("kernel hypotheses in " ^ thy ^ "." ^ n))
     (DB.thms thy);
   print ("KERNEL CLOSURE AUDIT PASS " ^ thy ^ "\n"))) audited_theories;

(* Preserved failing replay: VALID localizes the first invalid prefix below.
Theorem scalar_scope_probe:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 F ov op sa = (result,sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME 0w /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  is_word_type ty /\ type_memory_bytes cenv (lowered_value_type cenv e) = 0 ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ptr_val_ok cx ty (BoolV outcome.co_success) result H un t /\ ptr_buf_ok cenv e result H t /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
    ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
    ghost_kept cenv es sa G tn s H un /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  VALID (strip_tac >> drule_all raw_call_nonrevert_code_groups >> strip_tac) >>
  VALID (fs[compileEnvTheory.comp_return_def]) >>
  VALID (drule_all raw_call_case_emit_facts >> strip_tac) >>
  VALID (fs[]) >>
  VALID (mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`protected` |-> `sa`, `d` |-> `dep`, `rz_op` |-> `Lit 0w`, `rz` |-> `0w`, `ro` |-> `0w`, `sc` |-> `sb`]) >>
    (impl_tac >- (simp[venomStateTheory.eval_operand_def, compileEnvTheory.regions_disjoint_def] >>
      metis_tac[fresh_not_local_ptr])) >> strip_tac) >>
  FAIL_TAC "after checked elimination"
QED
*)

(* Only the checked-edge prefix is certified here, not scalar finish totality. *)
Theorem scalar_checked_elimination_probe:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 F ov op sa = (result,sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME 0w /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?H un u. gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un u
Proof
  VALID (strip_tac >> drule_all raw_call_nonrevert_code_groups >> strip_tac) >>
  VALID (fs[compileEnvTheory.comp_return_def]) >>
  VALID (drule_all raw_call_case_emit_facts >> strip_tac) >>
  VALID (fs[]) >>
  VALID (mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`protected` |-> `sa`, `d` |-> `dep`, `rz_op` |-> `Lit 0w`, `rz` |-> `0w`, `ro` |-> `0w`, `sc` |-> `sb`]) >>
    (impl_tac >- (simp[venomStateTheory.eval_operand_def, compileEnvTheory.regions_disjoint_def] >>
      metis_tac[fresh_not_local_ptr])) >> strip_tac) >>
  metis_tac[]
QED

val () = if null (hyp scalar_checked_elimination_probe) then ()
  else raise Fail "checked elimination probe has kernel hypotheses";
