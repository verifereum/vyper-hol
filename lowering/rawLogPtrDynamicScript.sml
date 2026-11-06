(* Covered bytes prefixes and the dynamic RawLog suffix. *)
Theory rawLogPtrDynamic
Ancestors
  rawLogPtrInst bodyPtrHashBuiltinsKeccakBytesRun
  typedCopyPtr bodyPtrDefs fragGasSeqPtr ptrDiscipline venomState venomInst
  venomExecSemantics words finite_map pred_set contextCodegenRel codegenRel
  valueEncodingProps exprSimHash list context compileEnv emitHelper
  exprLoweringProps rich_list ASCIInumbers emitHelperProps

(* The common length/payload-address prefix does not depend on its consumer. *)
Theorem bytes_mload_add_inst_seq_ptr:
  !D ctx fn PG G tn s il ia x l p b base cap n.
    ALL_DISTINCT [x;l;p] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32 <= base+cap /\
    b+32 < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst il MLOAD [Var x] [l]; mk_inst ia ADD [Var x;Lit 32w] [p]] s
      (DRESTRICT G (COMPL {l}) |+ (p,(base,cap)))
      (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `ptr_covers G tn x s 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `mload b s = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s = OK (update_var l (n2w n) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume bytes_mload_add_inst_seq_ptr[add]:
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s1 =
    OK (update_var p (n2w b + 32w) s1)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[inst_seq_ptr_def, hash_add_ghost, Abbr `G1`, Abbr `tn1`] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  gvs[ALL_DISTINCT]
QED

Finalise bytes_mload_add_inst_seq_ptr

Theorem bytes_mload_add_emitted_ptr:
  !D ctx fn PG G tn s x sa len_op sl data_op sb b base cap n.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x; Lit 32w] sl = (data_op,sb) /\
  not_fresh_at sa x /\ eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32 <= base+cap /\
  b+32 < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    op_taint tn' len_op = {} /\ op_prov G' len_op = NONE /\
    op_taint tn' data_op = {} /\ op_prov G' data_op = SOME (base,cap) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `l = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `p = STRING #"%" (toString (sa.cs_next_var+1))` >>
  `ALL_DISTINCT [x;l;p]` by
    (gvs[ALL_DISTINCT, Abbr `l`, Abbr `p`, not_fresh_at_def, toString_inj] >>
     metis_tac[]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qexistsl_tac [`DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap))`,
    `tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})`] >>
  conj_tac
  >- (simp[emitted_insts_def] >>
      CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
      simp[DROP_LENGTH_APPEND] >>
      irule bytes_mload_add_inst_seq_ptr >> simp[] >>
      qexistsl_tac [`b`, `n`] >> simp[]) >>
  fs[ALL_DISTINCT] >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `z <> l /\ z <> p` by
    (gvs[Abbr `l`, Abbr `p`, not_fresh_at_def] >> metis_tac[]) >>
  simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
