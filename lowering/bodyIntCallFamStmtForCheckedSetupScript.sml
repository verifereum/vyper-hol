(* Checked range setup without an execution-history requirement. *)
Theory bodyIntCallFamStmtForCheckedSetup
Ancestors
  bodyIntCallFamStmtForSetupGeneral bodyIntCallFamStmtForSetup
  bodyIntCallJointContract fragGasMode venomExecSemantics venomState
  compileEnv finite_map venomInst intCallFrame list

Theorem intcall_for_checked_start_no_history:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := start_lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label lbl] []]|> /\
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i ASSIGN [op1] [cv];
       mk_inst (i+1) SUB [op2;op1] [rv];
       mk_inst (i+2) cmp [op1;op2] [g1];
       mk_inst (i+3) ISZERO [Var g1] [z1];
       mk_inst (i+4) ASSERT [Var z1] [];
       mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
       mk_inst (i+6) ISZERO [Var g2] [z2];
       mk_inst (i+7) ASSERT [Var z2] [];
       mk_inst (i+8) ADD [op1;Var rv] [ev];
       mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  MEM cmp [SGT;GT] /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  eval_operand op1 s0 = SOME a /\ eval_operand op2 s0 = SOME b /\
  ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  local_ptrs_reserved ce sa /\
  MEM aa (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  not_local_ptr ce es.scopes p /\
  (!x. not_fresh_at sa x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) ==>
  (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
      w2n (b-a) > w2n (n2w bound : bytes32)) ==>
    ?t. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (Abort Revert_abort t)) /\
  (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
   ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
  ?cc w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
    (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0) /\
    (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p` by (fs[] >> metis_tac[]) >>
  drule_all intcall_for_alloca_start_no_history >> strip_tac >>
  `eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b` by
    (conj_tac >> Cases_on `op1` >> Cases_on `op2` >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
   (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev])` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_all intcall_for_checked_entry >> strip_tac >>
  conj_tac
  >- (disch_tac >> qpat_x_assum `_ \/ _ ==> ?t. _` drule >> strip_tac >>
      qexists_tac `t` >> drule_all gas_marked_path_then >> simp[]) >>
  strip_tac >> qpat_x_assum `_ /\ _ ==> ?cc. _` drule_all >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`cc`, `w`] >> simp[] >> fs[ALL_DISTINCT] >> metis_tac[]
QED
