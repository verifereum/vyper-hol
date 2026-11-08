(* Literal-folding offsets checked on the same endpoint as the ordinary run. *)
Theory immutableOffsetPtr
Ancestors
  exprSimCopy context compileEnv emitHelper emitHelperProps exprLoweringProps
  stmtAppendStorageRunPtr fragGasSeqPtr ptrDiscipline venomExecSemantics
  venomInst venomState finite_map words list bodyPtrDefs ghostPcTransportPtr

Theorem immutable_offset_add_step[local]:
  eval_operand op s = SOME a ==>
  step_inst_base (mk_inst id ADD [op; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)
Proof
  strip_tac >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def]
QED

Theorem immutable_offset_add_checked[local]:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [op; Lit (n2w off)] [out]] s
    (step_prov PG G (mk_inst id ADD [op; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [op; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    simp[immutable_offset_add_step] >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule append_scalar_inst_check >>
      simp[update_var_def] >> rpt strip_tac >> gvs[] >>
      simp[op_taint_def]) >>
  sym_tac >> irule scalar_add_taint >> simp[update_var_def]
QED

Theorem immutable_offset_add_uniform[local]:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [op; Lit (n2w off)] [out]] (s with vs_inst_idx := k)
    (step_prov PG G (mk_inst id ADD [op; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    immutable_offset_add_checked) >>
  simp[step_prov_def, out_prov_def]
QED

Theorem immutable_offset_add_provenance[local]:
  op_prov (step_prov PG G (mk_inst id ADD [op; Lit k] [out]) t) (Var out) =
    op_prov G op
Proof
  Cases_on `op` >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP G s` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem compile_lit_byte_offset_checked:
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\
    eval_operand r t = SOME (a + n2w off) /\
    copy_old_operand sb r /\ t.vs_memory = s.vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_taint tf r = {} /\ op_prov Gf r = op_prov G op /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all copy_runtime_offset >> strip_tac >>
  qexists_tac `s'` >> simp[] >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl [`G`,`tn`] >> simp[emitted_insts_def, inst_seq_ptr_def]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl [`G`,`tn`] >>
      simp[emitted_insts_def, inst_seq_ptr_def, op_taint_def]) >>
  gvs[compile_lit_byte_offset_def, eval_operand_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mk_inst id ADD ops [out]` >>
  qexistsl [`step_prov PG G (mk_inst id ADD ops [out])
               (update_var out (a + n2w off) s)`,
            `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[Abbr `ops`, immutable_offset_add_uniform, eval_operand_def,
       immutable_offset_add_provenance, op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> out` by (gvs[Abbr `out`, not_fresh_at_def] >> metis_tac[]) >>
  simp[scalar_step_old_prov]
QED

Theorem compile_lit_byte_offset_covered:
  !sa sb p off r s a G tn total n ctx D fn PG.
  compile_lit_byte_offset (Var p) off sa = (r,sb) /\
  not_fresh_at sa p /\ lookup_var p s = SOME a /\
  ptr_covers G tn p s total /\ off < total /\ off + n <= total /\
  w2n a + off < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?q t Gf tf.
    r = Var q /\ copy_runtime_frame sa s sb t /\
    lookup_var q t = SOME (a + n2w off) /\
    not_fresh_at sb q /\ t.vs_memory = s.vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    ptr_covers Gf tf q t n /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `copy_old_operand sa (Var p) /\ eval_operand (Var p) s = SOME a /\
   op_taint tn (Var p) = {}` by
    (gvs[copy_old_operand_def, eval_operand_def, ptr_covers_def]) >>
  drule_all compile_lit_byte_offset_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `?q. r = Var q` by
    (Cases_on `off = 0` >>
     gvs[compile_lit_byte_offset_def, comp_return_def] >>
     drule emitted_insts_emit_op >> metis_tac[]) >>
  gvs[eval_operand_def, copy_old_operand_def] >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[] >>
  gvs[ptr_covers_def, op_prov_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED
