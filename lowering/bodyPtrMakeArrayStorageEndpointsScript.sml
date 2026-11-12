(* A common relational frame hides the concrete instruction ghost maps, so
   stage composition need not duplicate long register/static conjunctions.
   Memory and memory-taint observations are deliberately separate: MSTORE
   obeys this frame as well as the non-writing stages. *)
Theory bodyPtrMakeArrayStorageEndpoints
Ancestors
  wordLoadStorePtr bodyPtrMakeArrayStorageBody bodyPtrMakeArrayCopyStep
  pred_set finite_map words bodyPtrDefs
  exprSimStorageCopy venomState ptrDiscipline

Definition storage_body_frame_def:
  storage_body_frame writes G tn s H tm t <=>
    copy_static t = copy_static s /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x NOTIN writes ==>
      lookup_var x t = lookup_var x s /\
      op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x))
End

Theorem storage_body_frame_refl:
  storage_body_frame writes G tn s G tn s
Proof
  simp[storage_body_frame_def]
QED

Theorem storage_body_frame_mono:
  storage_body_frame writes G tn s H tm t /\ writes SUBSET V ==>
  storage_body_frame V G tn s H tm t
Proof
  simp[storage_body_frame_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem storage_body_frame_trans:
  storage_body_frame writes G tn s H tm t /\
  storage_body_frame V H tm t J tu u ==>
  storage_body_frame (writes UNION V) G tn s J tu u
Proof
  simp[storage_body_frame_def] >> metis_tac[]
QED

Theorem storage_body_frame_covers:
  storage_body_frame writes G tn s H tm t /\ p NOTIN writes /\ ptr_covers G tn p s n ==>
  ptr_covers H tm p t n
Proof
  simp[storage_body_frame_def, ptr_covers_def, op_prov_def] >> metis_tac[]
QED

Theorem storage_body_source_endpoint:
  (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from 0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src; Var cv] [av]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst lid (if loc = LocStorage then SLOAD else TLOAD) [Var av] [vv]) /\
  eval_operand src s = SOME a /\ lookup_var cv s = SOME (n2w k) /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_frame {av;vv} G tn s H tm t /\
    lookup_var vv t = SOME (copy_runtime_word loc s (a+n2w k)) /\
    op_prov H (Var vv) = NONE /\
    op_taint tm (Var vv) = key_taint
      (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w k) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    ~t.vs_halted /\ t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `s1 = (update_var av (a+n2w k) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_taint (mk_inst id ADD [src;Var cv] [av]) s
      (update_var av (a+n2w k) s) tn = (tn with t_var := tn.t_var |+ (av,{}))` by
    (simp[step_taint_def, set_var_taint_def, venomInstTheory.mk_inst_def,
      out_taint_def, mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      new_site_bytes_def, update_var_def, FLOOKUP_DEF,
      pred_setTheory.EXTENSION, range_bytes_def, taint_component_equality,
      SF CONJ_ss]) >>
  qexistsl_tac [
    `(update_var vv (copy_runtime_word loc s (a+n2w k)) s1) with
      vs_inst_idx := SUC s1.vs_inst_idx`,
    `DRESTRICT (step_prov PG G (mk_inst id ADD [src; Var cv] [av])
      (update_var av (a+n2w k) s)) (COMPL {vv})`,
    `tn with t_var := (tn.t_var |+ (av,{})) |+ (vv,
      key_taint (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w k))`] >>
  conj_tac >-
    (`step_inst_base (mk_inst lid (if loc = LocStorage then SLOAD else TLOAD)
        [Var av] [vv]) s1 =
      OK (update_var vv (copy_runtime_word loc s (a+n2w k)) s1)` by
       (Cases_on `loc = LocStorage` >>
        simp[Abbr `s1`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          copy_runtime_word_def, sload_def, tload_def, contract_storage_def,
          contract_transient_def]) >>
     mp_tac (Q.INST [`opc` |-> `if loc = LocStorage then SLOAD else TLOAD`,
       `H` |-> `step_prov PG G (mk_inst id ADD [src;Var cv] [av])
         (update_var av (a+n2w k) s)`,
       `tm` |-> `tn with t_var := tn.t_var |+ (av,{})`,
       `w` |-> `copy_runtime_word loc s (a+n2w k)`] storage_body_source_load) >>
     simp[Abbr `s1`] >> Cases_on `loc = LocStorage` >> simp[]) >>
  simp[storage_body_frame_def, Abbr `s1`, copy_static_def,
    update_var_def, lookup_var_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `out` |-> `av`, `vv` |-> `x`,
    `left` |-> `src`, `right` |-> `Var cv`,
    `w` |-> `a+n2w k`] storage_body_arith_loaded_frame) >>
  simp[op_prov_def, update_var_def]
QED

Theorem storage_body_destination_stage:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst mid MUL [Var cv; Lit 32w] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst aid ADD [Var dst; Var ov] [dv]) /\
  lookup_var cv s = SOME (n2w k) /\ lookup_var dst s = SOME (n2w b) /\
  op_taint tn (Var cv) = {} /\ ptr_covers G tn dst s (32*n) /\
  k < n /\ b+32*n < dimword(:256) /\ ov <> dst /\ dv <> dst ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_frame {ov;dv} G tn s H tm t /\
    ptr_covers H tm dv t 32 /\ lookup_var dv t = SOME (n2w (b+32*k)) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    ~t.vs_halted /\ t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem
Proof
  strip_tac >> `b < dimword(:256)` by decide_tac >>
  mp_tac (Q.INST [
    `a` |-> `n2w b`,
    `s1` |-> `(update_var ov (n2w (k*32)) s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `G1` |-> `DRESTRICT G (COMPL {ov})`,
    `tn1` |-> `tn with t_var := tn.t_var |+ (ov,{})`]
    storage_body_destination_endpoint) >>
  simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> strip_tac >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  gvs[storage_body_frame_def, word_add_n2w] >> metis_tac[]
QED

Theorem storage_body_counter_stage:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst aid ADD [Var cv; Lit 1w] [nv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst sid ASSIGN [Var nv] [cv]) /\
  lookup_var cv s = SOME (n2w k) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_frame {nv;cv} G tn s H tm t /\
    lookup_var cv t = SOME (n2w (k+1)) /\
    op_prov H (Var cv) = NONE /\ op_taint tm (Var cv) = {} /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    ~t.vs_halted /\ t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem
Proof
  strip_tac >>
  qabbrev_tac `s1 = (update_var nv (n2w (k+1)) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  qexistsl_tac [
    `(update_var cv (n2w (k+1)) s1) with vs_inst_idx := SUC s1.vs_inst_idx`,
    `DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})`,
    `tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{})`] >>
  conj_tac >- (mp_tac (Q.INST [`s1` |-> `s1`] storage_body_counter_path) >>
    simp[Abbr `s1`]) >>
  simp[storage_body_frame_def, Abbr `s1`, copy_static_def, update_var_def,
    lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem storage_body_store_stage:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dv;value] []) /\
  lookup_var dv s = SOME (n2w (b+32*k)) /\ eval_operand value s = SOME w /\
  ptr_covers G tn dv s 32 /\ b+32*k < dimword(:256) /\
  (!j. j IN op_taint tn value ==> j < 32) ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_frame {} G tn s H tm t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx /\
    ~t.vs_halted /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!loc a n sbase keys.
      copy_prefix loc a b n sbase k s /\ k < n /\
      w = copy_runtime_word loc sbase (a+n2w k) /\
      (!i j. i < k /\ j < 32 /\ b+32*i+j IN tn.t_mem ==>
        j IN key_taint keys (a+n2w i)) /\
      op_taint tn value SUBSET key_taint keys (a+n2w k) ==>
      copy_prefix loc a b n sbase (k+1) t /\
      (!i j. i < k+1 /\ j < 32 /\ b+32*i+j IN tm.t_mem ==>
        j IN key_taint keys (a+n2w i))) /\
    mem_agree_outside {i | b+32*k <= i /\ i < b+32*k+32}
      t.vs_memory s.vs_memory /\
    (!i. i < b+32*k \/ b+32*k+32 <= i ==>
      (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tn`, `id`, `PG`, `G`] strip_assume_tac) >>
  `w2n (n2w (b+32*k):256 word) = b+32*k` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  gs[] >>
  qabbrev_tac `tm = step_taint (mk_inst id MSTORE [Var dv;value] []) s
    (mstore (b+32*k) w s) tn` >>
  qexistsl_tac [`(mstore (b+32*k) w s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `G`, `tm`] >>
  conj_tac >- (mp_tac (Q.INST [`dst` |-> `dv`, `a` |-> `n2w (b+32*k)`]
    mstore_raw_ptr_path) >> simp[Abbr `tm`]) >>
  conj_tac >- (simp[storage_body_frame_def, Abbr `tm`, op_taint_def] >>
    simp[copy_static_def, mstore_def, lookup_var_def]) >>
  conj_tac >- simp[mstore_def] >> conj_tac >- simp[] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- simp[venomMemPropsTheory.LENGTH_mstore_eq] >>
  conj_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`sm` |-> `mstore (b+32*k) w s`, `tnm` |-> `tm`]
       storage_body_store_prefix) >> simp[Abbr `tm`] >> strip_tac >> simp[]) >>
  conj_tac >- (qspecl_then [`s`, `b+32*k`, `w`] mp_tac
    wordLoadStorePtrTheory.mstore_memory_frame >> simp[]) >>
  rpt strip_tac >>
  mp_tac (Q.INST [`dst` |-> `dv`, `a` |-> `n2w (b+32*k)`]
    mstore_raw_outside_taint) >> simp[Abbr `tm`]
QED
