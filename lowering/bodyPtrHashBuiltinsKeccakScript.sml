(* Counted pointer-checked keccak suffix instruction interface. *)
Theory bodyPtrHashBuiltinsKeccak
Ancestors
  bodyPtrHashBuiltinsBoundary exprSimHash fragGasSeqPtr bodyPtrDefs
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  instIdxIndep words contextCodegenRel codegenRel finite_map

Theorem hash_sha3_inst_ok:
  !D ctx fn G tn s id p len out w n b sz fuel bs.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    FLOOKUP G p = SOME (b,sz) /\
    b <= w2n w /\ w2n w + w2n n <= b + sz /\
    op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w + w2n n ==> i NOTIN tn.t_mem) /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  rpt strip_tac >>
  `access_ok 0 G fn (mk_inst id SHA3 [Var p; len] [out]) s` by
    (irule hash_sha3_access >> metis_tac[]) >>
  `taint_ok fn tn (mk_inst id SHA3 [Var p; len] [out]) s` by
    (irule hash_sha3_taint >> metis_tac[]) >>
  drule_all step_SHA3_bytes >> strip_tac >>
  simp[ptr_inst_ok_def, allocas_from_def, mk_inst_def,
       step_inst_non_invoke] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Theorem hash_sha3_counted_edge:
  !D ctx fn PG G tn s bb id p len out w n b sz bs.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id SHA3 [Var p; len] [out]) /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    FLOOKUP G p = SOME (b,sz) /\
    b <= w2n w /\ w2n w + w2n n <= b + sz /\
    op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w + w2n n ==> i NOTIN tn.t_mem) /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    ~ctx_has_dalloca ctx ==>
    ?t. step_inst_base (mk_inst id SHA3 [Var p; len] [out]) s = OK t /\
      gas_path_ptr_edge D 0 ctx fn PG G tn s 0
        (step_prov PG G (mk_inst id SHA3 [Var p; len] [out]) t)
        (step_taint (mk_inst id SHA3 [Var p; len] [out]) s t tn)
        (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> drule_all step_SHA3_bytes >> strip_tac >>
  qexists `update_var out (word_of_bytes T 0w (Keccak_256_w64 bs)) s` >>
  conj_tac >- simp[] >>
  simp[mk_inst_def] >>
  irule (Q.INST [`i` |-> `mk_inst id SHA3 [Var p; len] [out]`]
    straight_line_ptr_edge |> SRULE [mk_inst_def]) >>
  simp[GSYM mk_inst_def, is_terminator_def] >>
  irule hash_sha3_inst_ok >> metis_tac[]
QED

Theorem hash_sha3_ghost:
  !PG G tn s id src len out v.
    step_prov PG G (mk_inst id SHA3 [src;len] [out]) (update_var out v s) =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id SHA3 [src;len] [out]) s (update_var out v s) tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand src s` >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       imm_taint_def, taint_component_equality]
QED
