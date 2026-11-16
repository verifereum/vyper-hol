Theory bodyFullForArrayDynamicScalar
Ancestors
  instSeqPtrLo fragGasSeqPtr forPtrCheckedScalar ptrDiscipline ptrSafeRun venomExecSemantics
  venomState venomInst finite_map pred_set words list codegenRel contextCodegenRel

Theorem for_array_bound_gt_cons:
  lookup_var lv s = SOME (n2w len) /\ len <= c /\ c < dimword (:256) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx ==>
  (inst_seq_ptr D 0 ctx func PG G tn
    (mk_inst eid GT [Var lv; Lit (n2w c)] [g] :: code) s Gf tf <=>
   inst_seq_ptr D 0 ctx func PG (DRESTRICT G (COMPL {g}))
    (tn with t_var := tn.t_var |+ (g,{})) code
    ((update_var g 0w s) with vs_inst_idx := SUC s.vs_inst_idx) Gf tf)
Proof
  strip_tac >> irule for_checked_scalar_seq_cons >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
       eval_operand_def,bool_to_word_def] >>
  `len < dimword (:256)` by decide_tac >>
  simp[WORD_LO,word_lo_n2w]
QED

Theorem for_array_iszero_cons:
  lookup_var g s = SOME 0w /\
  FLOOKUP G g = NONE /\ op_taint tn (Var g) = {} /\
  ~ctx_has_dalloca ctx ==>
  (inst_seq_ptr D 0 ctx func PG G tn
    (mk_inst eid ISZERO [Var g] [vld] :: code) s Gf tf <=>
   inst_seq_ptr D 0 ctx func PG (DRESTRICT G (COMPL {vld}))
    (tn with t_var := tn.t_var |+ (vld,{})) code
    ((update_var vld 1w s) with vs_inst_idx := SUC s.vs_inst_idx) Gf tf)
Proof
  strip_tac >> irule for_checked_scalar_seq_cons >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure1_def,
       eval_operand_def,bool_to_word_def]
QED

Theorem for_array_assert_one_cons:
  lookup_var v s = SOME 1w /\ op_taint tn (Var v) = {} /\
  FLOOKUP G v = NONE /\ ~ctx_has_dalloca ctx ==>
  (inst_seq_ptr D 0 ctx func PG G tn
    (mk_inst e ASSERT [Var v] [] :: code) s Gf tf <=>
   inst_seq_ptr D 0 ctx func PG G tn code
    (s with vs_inst_idx := SUC s.vs_inst_idx) Gf tf)
Proof
  strip_tac >>
  `step_inst_base (mk_inst e ASSERT [Var v] []) s = OK s` by
    simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst e ASSERT [Var v] []) s` by
    (irule stmtAppendStorageRunPtrTheory.append_scalar_inst_check >> simp[]) >>
  simp[Once inst_seq_ptr_def,
       stmtAppendStorageRunPtrTheory.scalar_void_prov,
       stmtAppendStorageRunPtrTheory.scalar_assert_taint]
QED

(* The checked dynamic bound has one scalar ghost endpoint for every mask. *)
Theorem for_array_dynamic_scalar_sequence_full:
  ALL_DISTINCT [lv;idx;g;vld] /\
  lookup_var lv s = SOME (n2w len) /\ len <= c /\ c < dimword (:256) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?Gf tf. (!D. inst_seq_ptr D lo ctx func PG G tn
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] s Gf tf) /\
    FLOOKUP Gf idx = NONE /\ FLOOKUP Gf lv = NONE /\
    op_taint tf (Var idx) = {} /\ op_taint tf (Var lv) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. ~MEM x [idx;g;vld] ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> `len < dimword (:256)` by decide_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {g})) (COMPL {vld})`,
    `tn with t_var := tn.t_var |+ (idx,{}) |+ (g,{}) |+ (vld,{})`] >>
  reverse conj_tac
  >- gvs[ALL_DISTINCT,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
  gen_tac >> irule inst_seq_ptr_zero_to_lo >>
  simp[] >> qexists_tac `D` >> simp[] >>
  simp[Once (for_checked_scalar_seq_cons |> Q.INST [`w` |-> `0w`]),
       step_inst_base_opcode_eqs,mk_inst_def,exec_pure1_def,
       eval_operand_def,op_taint_def,op_prov_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_bound_gt_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_iszero_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_assert_one_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  simp[inst_seq_ptr_def,INTER_ASSOC]
QED
