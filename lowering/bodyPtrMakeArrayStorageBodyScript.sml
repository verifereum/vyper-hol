(* Straight-line stages of the actual external copy-loop body. *)
Theory bodyPtrMakeArrayStorageBody
Ancestors
  bodyPtrMakeArrayStorageControl bodyPtrMakeArrayAdd bodyPtrMakeArrayCopyStep
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map words codegenRel fragGasPathPtr typedCopyLoopHeaderPtr
  bodyPtrMakeArrayExternalLoop exprSimStorageCopy bodyPtrMakeArrayPrefix typedCopyPtr

Theorem storage_body_scalar_add_ghost:
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ADD [left;right] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem storage_body_scalar_add_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule storage_body_scalar_add_ghost >> simp[]) >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] clean_binop_ptr_path) >>
  simp[]
QED

Theorem storage_body_load_path:
  (opc = SLOAD \/ opc = TLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  eval_operand src s = SOME key /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK (update_var tmp w s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tmp}))
    (tn with t_var := tn.t_var |+
      (tmp, if opc = SLOAD then key_taint tn.t_stor key
            else key_taint tn.t_trans key))
    (OK ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s) =
      DRESTRICT G (COMPL {tmp}) /\
   step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn =
      (tn with t_var := tn.t_var |+
        (tmp, if opc = SLOAD then key_taint tn.t_stor key
              else key_taint tn.t_trans key))` by
    (mp_tac (Q.INST [`opc` |-> `opc`, `src` |-> `src`,
      `s` |-> `s`, `a` |-> `key`] external_load_ghost_frame) >>
     simp[] >> strip_tac >> gvs[taint_component_equality]) >>
  mp_tac (Q.INST [`opc` |-> `opc`, `src` |-> `src`,
    `tmp` |-> `tmp`, `id` |-> `id`, `u` |-> `update_var tmp w s`]
    external_load_ptr_path) >> simp[]
QED

Theorem storage_body_source_load:
  (opc = SLOAD \/ opc = TLOAD) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from 0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src; Var cv] [av]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst lid opc [Var av] [vv]) /\
  eval_operand src s = SOME a /\ lookup_var cv s = SOME (n2w k) /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  s1 = ((update_var av (a+n2w k) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst id ADD [src; Var cv] [av]) (update_var av (a+n2w k) s) /\
  tm = step_taint (mk_inst id ADD [src; Var cv] [av]) s (update_var av (a+n2w k) s) tn /\
  step_inst_base (mk_inst lid opc [Var av] [vv]) s1 = OK (update_var vv w s1) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT H (COMPL {vv}))
    (tm with t_var := tm.t_var |+
      (vv, if opc = SLOAD then key_taint tm.t_stor (a+n2w k)
           else key_taint tm.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK s1)` by
    (gvs[] >> irule clean_binop_ptr_path >> simp[eval_operand_def]) >>
  `op_taint tm (Var av) = {}` by
    (gvs[] >> metis_tac[copy_len_binop_ghost_frame]) >>
  `gas_path_ptr D 0 ctx fn PG H tm s1 0
    (DRESTRICT H (COMPL {vv}))
    (tm with t_var := tm.t_var |+
      (vv, if opc = SLOAD then key_taint tm.t_stor (a+n2w k)
           else key_taint tm.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule storage_body_load_path >>
     simp[update_var_def, lookup_var_def, eval_operand_def, allocas_from_def] >>
     qexistsl_tac [`lid`, `Var av`] >>
     gvs[update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
         FLOOKUP_UPDATE]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem storage_body_mul_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id MUL [left;right] [out])
      (update_var out (a*b) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id MUL [left;right] [out]) s
      (update_var out (a*b) s) tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost >> simp[update_var_def]) >>
  mp_tac (Q.INST [`left` |-> `left`, `right` |-> `right`, `out` |-> `out`]
    copy_loop_mul_ptr_path) >> simp[]
QED

(* Loaded words need not be clean: fresh arithmetic outputs preserve the
   entire old byte-taint set as well as the value and provenance. *)
Theorem storage_body_arith_loaded_frame:
  (opc = ADD \/ opc = MUL) /\ out <> vv ==>
  lookup_var vv ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) =
    lookup_var vv s /\
  op_prov (step_prov PG G (mk_inst id opc [left;right] [out])
    (update_var out w s)) (Var vv) = op_prov G (Var vv) /\
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn) (Var vv) = op_taint tn (Var vv) /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_imm = tn.t_imm /\
  copy_static ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) =
    copy_static s /\
  ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_memory = s.vs_memory
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[copy_static_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  Cases_on `eval_operand left s` >> Cases_on `first_prov G [left;right]` >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem storage_body_destination_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst mid MUL [Var cv; Lit 32w] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst aid ADD [Var dst; Var ov] [dv]) /\
  lookup_var cv s = SOME (n2w k) /\ lookup_var dst s = SOME a /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var dst) = {} /\ ov <> dst /\
  s1 = ((update_var ov (n2w (k*32)) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = DRESTRICT G (COMPL {ov}) /\
  tn1 = (tn with t_var := tn.t_var |+ (ov,{})) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1))
    (step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1)
    (OK ((update_var dv (a+n2w (k*32)) s1) with
      vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[] >>
     mp_tac (Q.INST [`left` |-> `Var cv`, `right` |-> `Lit 32w`,
       `out` |-> `ov`, `id` |-> `mid`, `a` |-> `n2w k`, `b` |-> `32w`]
       storage_body_mul_path) >>
     simp[eval_operand_def, op_taint_def, word_mul_n2w]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0
    (step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1))
    (step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1)
    (OK ((update_var dv (a+n2w (k*32)) s1) with
      vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule clean_binop_ptr_path >> simp[] >>
     gvs[update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
         FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem storage_body_load_execution:
  (opc = SLOAD \/ opc = TLOAD) /\ eval_operand src s = SOME key ==>
  step_inst_base (mk_inst id opc [src] [out]) s =
    OK (update_var out (if opc = SLOAD then sload key s else tload key s) s)
Proof
  strip_tac >> gvs[] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def]
QED

Theorem storage_body_source_load_frame:
  s1 = ((update_var av key s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  sf = ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx) /\
  Gf = DRESTRICT (step_prov PG G (mk_inst id ADD [left;right] [av])
    (update_var av key s)) (COMPL {vv}) /\
  tnf = (tn with t_var := (tn.t_var |+ (av,{})) |+ (vv,kt)) ==>
  copy_static sf = copy_static s /\ sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  lookup_var vv sf = SOME w /\ op_prov Gf (Var vv) = NONE /\
  op_taint tnf (Var vv) = kt /\
  (!x. x <> av /\ x <> vv ==>
    lookup_var x sf = lookup_var x s /\
    op_prov Gf (Var x) = op_prov G (Var x) /\
    op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!x. x <> av ==>
    op_prov (step_prov PG G (mk_inst id ADD [left;right] [av])
      (update_var av key s)) (Var x) = op_prov G (Var x)` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`opc` |-> `ADD`, `out` |-> `av`, `vv` |-> `x`,
       `w` |-> `key`] storage_body_arith_loaded_frame) >> simp[]) >>
  gvs[copy_static_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, op_prov_def, op_taint_def]
QED

Theorem storage_body_assign_clean_ghost:
  op_prov G src = NONE /\ op_taint tn src = {} ==>
  step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, first_prov_def] >>
  Cases_on `eval_operand src s` >> simp[]
QED

Theorem storage_body_assign_clean_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [src] [out]) /\
  eval_operand src s = SOME w /\ op_prov G src = NONE /\ op_taint tn src = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [src] [out]) s = OK (update_var out w s)` by
    simp[Once step_inst_base_def, mk_inst_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [src] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
      mk_inst_def, source_memory_write_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id ASSIGN [src] [out]`,
      `lo` |-> `0`, `u` |-> `update_var out w s`] fragGasSeqPtrTheory.straight_line_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule storage_body_assign_clean_ghost >> simp[]) >>
  gvs[] >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_body_counter_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst aid ADD [Var cv; Lit 1w] [nv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst sid ASSIGN [Var nv] [cv]) /\
  lookup_var cv s = SOME (n2w k) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  s1 = ((update_var nv (n2w (k+1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (OK ((update_var cv (n2w (k+1)) s1) with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {nv})) (tn with t_var := tn.t_var |+ (nv,{}))
    (OK s1)` by
    (simp[] >>
     mp_tac (Q.INST [`left` |-> `Var cv`, `right` |-> `Lit 1w`,
       `out` |-> `nv`, `id` |-> `aid`, `a` |-> `n2w k`, `b` |-> `1w`]
       storage_body_scalar_add_path) >>
     simp[eval_operand_def, op_taint_def, op_prov_def, word_add_n2w]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {nv})) (tn with t_var := tn.t_var |+ (nv,{})) s1 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (OK ((update_var cv (n2w (k+1)) s1) with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (mp_tac (Q.INST [`s` |-> `s1`, `src` |-> `Var nv`, `out` |-> `cv`,
       `G` |-> `DRESTRICT G (COMPL {nv})`,
       `tn` |-> `tn with t_var := tn.t_var |+ (nv,{})`,
       `id` |-> `sid`, `w` |-> `n2w (k+1)`] storage_body_assign_clean_path) >>
     simp[] >> disch_then irule >>
     gvs[update_var_def, lookup_var_def, eval_operand_def, op_prov_def,
         op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem storage_body_mul_old_coverage:
  ptr_covers G tn root s n /\ root <> out ==>
  ptr_covers (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) root
    ((update_var out w s) with vs_inst_idx := idx) n
Proof
  strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, allocas_from_def]
QED

Theorem storage_body_destination_coverage:
  ptr_covers G tn dst s (32*n) /\ lookup_var dst s = SOME a /\
  k < n /\ w2n a + 32*n < dimword(:256) /\
  ov <> dst /\ dv <> dst /\
  s1 = ((update_var ov (n2w (k*32)) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = DRESTRICT G (COMPL {ov}) /\
  tn1 = (tn with t_var := tn.t_var |+ (ov,{})) ==>
  ptr_covers
    (step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1))
    (step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1)
    dv ((update_var dv (a+n2w (k*32)) s1) with
      vs_inst_idx := SUC s1.vs_inst_idx) 32
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G1 tn1 dst s1 (32*n)` by
    (gvs[] >> irule storage_body_mul_old_coverage >> simp[]) >>
  `lookup_var dst s1 = SOME a /\
   eval_operand (Var ov) s1 = SOME (n2w (k*32))` by
    gvs[update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE] >>
  `k*32 < 32*n /\ k*32+32 <= 32*n /\ w2n a+k*32 < dimword(:256)` by
    decide_tac >>
  `ptr_covers
    (step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1))
    (step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1)
    dv (update_var dv (a+n2w (k*32)) s1) 32` by
    (irule typed_copy_loop_dynamic_offset_covers >> simp[] >>
     qexists_tac `32*n` >> gvs[]) >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, eval_operand_def,
      allocas_from_def]
QED

Theorem storage_body_store_prefix:
  copy_prefix loc a b n sbase k s /\ k < n /\
  w = copy_runtime_word loc sbase (a+n2w k) /\
  lookup_var dv s = SOME (n2w (b+32*k)) /\ eval_operand value s = SOME w /\
  b+32*k < dimword(:256) /\
  (!i j. i < k /\ j < 32 /\ b+32*i+j IN tn.t_mem ==>
     j IN key_taint keys (a+n2w i)) /\
  op_taint tn value SUBSET key_taint keys (a+n2w k) /\
  sm = mstore (b+32*k) w s /\
  tnm = step_taint (mk_inst id MSTORE [Var dv;value] []) s sm tn ==>
  copy_prefix loc a b n sbase (k+1)
    (sm with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!i j. i < k+1 /\ j < 32 /\ b+32*i+j IN tnm.t_mem ==>
     j IN key_taint keys (a+n2w i))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (gvs[copy_prefix_idx] >> irule copy_prefix_extend >> simp[]) >>
  `tnm.t_mem =
    (tn.t_mem DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
    {b+32*k+j | j IN op_taint tn value}` by
    (mp_tac (Q.INST [`dst` |-> `dv`, `a` |-> `n2w (b+32*k)`,
      `value` |-> `value`, `w` |-> `w`] mstore_raw_ghost_frame) >>
     simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
     strip_tac >> AP_TERM_TAC >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  ho_match_mp_tac (Q.INST [`tainted` |-> `tn.t_mem`,
    `loaded` |-> `op_taint tn value`]
    (INST_TYPE [alpha |-> ``:256``] copied_prefix_taint_extend)) >> simp[]
QED

Theorem storage_body_destination_frame:
  s1 = ((update_var ov (n2w (k*32)) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = DRESTRICT G (COMPL {ov}) /\
  tn1 = (tn with t_var := tn.t_var |+ (ov,{})) /\
  sf = ((update_var dv (a+n2w (k*32)) s1) with
    vs_inst_idx := SUC s1.vs_inst_idx) /\
  Gf = step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
    (update_var dv (a+n2w (k*32)) s1) /\
  tnf = step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
    (update_var dv (a+n2w (k*32)) s1) tn1 ==>
  copy_static sf = copy_static s /\ sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!x. x <> ov /\ x <> dv ==>
    lookup_var x sf = lookup_var x s /\
    op_prov Gf (Var x) = op_prov G (Var x) /\
    op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!x. x <> dv ==>
    lookup_var x sf = lookup_var x s1 /\
    op_prov Gf (Var x) = op_prov G1 (Var x) /\
    op_taint tnf (Var x) = op_taint tn1 (Var x) /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
    tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
    copy_static sf = copy_static s1 /\ sf.vs_memory = s1.vs_memory` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `sf = _` (fn th => pure_rewrite_tac [th]) >>
     qpat_x_assum `Gf = _` (fn th => pure_rewrite_tac [th]) >>
     qpat_x_assum `tnf = _` (fn th => pure_rewrite_tac [th]) >>
     irule storage_body_arith_loaded_frame >> simp[]) >>
  `tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
   tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
   copy_static sf = copy_static s1 /\ sf.vs_memory = s1.vs_memory` by
    (first_x_assum (qspec_then `dv ++ "x"` mp_tac) >> simp[]) >>
  gvs[copy_static_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, op_prov_def, op_taint_def]
QED

Theorem storage_body_destination_endpoint:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst mid MUL [Var cv; Lit 32w] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst aid ADD [Var dst; Var ov] [dv]) /\
  lookup_var cv s = SOME (n2w k) /\ lookup_var dst s = SOME a /\
  op_taint tn (Var cv) = {} /\ ptr_covers G tn dst s (32*n) /\
  k < n /\ w2n a + 32*n < dimword(:256) /\ ov <> dst /\ dv <> dst /\
  s1 = ((update_var ov (n2w (k*32)) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = DRESTRICT G (COMPL {ov}) /\
  tn1 = (tn with t_var := tn.t_var |+ (ov,{})) ==>
  ?sf Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    ptr_covers Gf tnf dv sf 32 /\
    lookup_var dv sf = SOME (a+n2w (k*32)) /\
    sf.vs_current_bb = s.vs_current_bb /\
    sf.vs_inst_idx = s.vs_inst_idx+2 /\ ~sf.vs_halted /\
    copy_static sf = copy_static s /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> ov /\ x <> dv ==>
      lookup_var x sf = lookup_var x s /\
      op_prov Gf (Var x) = op_prov G (Var x) /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qexistsl_tac [
    `(update_var dv (a+n2w (k*32)) s1) with vs_inst_idx := SUC s1.vs_inst_idx`,
    `step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1)`,
    `step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1`] >>
  conj_tac >- (irule storage_body_destination_path >> simp[] >>
    gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (irule storage_body_destination_coverage >> simp[] >>
    qexistsl_tac [`G`, `n`, `s`, `tn`] >> simp[]) >>
  `!sf Gf tnf.
    sf = ((update_var dv (a+n2w (k*32)) s1) with
      vs_inst_idx := SUC s1.vs_inst_idx) /\
    Gf = step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1) /\
    tnf = step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1 ==>
    copy_static sf = copy_static s /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> ov /\ x <> dv ==>
      lookup_var x sf = lookup_var x s /\
      op_prov Gf (Var x) = op_prov G (Var x) /\
      op_taint tnf (Var x) = op_taint tn (Var x))` by
    (rpt gen_tac >> strip_tac >> drule_all storage_body_destination_frame >> simp[]) >>
  first_x_assum (qspecl_then [
    `(update_var dv (a+n2w (k*32)) s1) with vs_inst_idx := SUC s1.vs_inst_idx`,
    `step_prov PG G1 (mk_inst aid ADD [Var dst;Var ov] [dv])
      (update_var dv (a+n2w (k*32)) s1)`,
    `step_taint (mk_inst aid ADD [Var dst;Var ov] [dv]) s1
      (update_var dv (a+n2w (k*32)) s1) tn1`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> gvs[update_var_def]
QED

Theorem storage_body_counter_frame:
  s1 = ((update_var nv (n2w (k+1)) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  sf = ((update_var cv (n2w (k+1)) s1) with vs_inst_idx := SUC s1.vs_inst_idx) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}) /\
  tnf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{})) ==>
  lookup_var cv sf = SOME (n2w (k+1)) /\
  op_prov Gf (Var cv) = NONE /\ op_taint tnf (Var cv) = {} /\
  sf.vs_current_bb = s.vs_current_bb /\ sf.vs_inst_idx = s.vs_inst_idx+2 /\
  copy_static sf = copy_static s /\ sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!x. x <> nv /\ x <> cv ==>
    lookup_var x sf = lookup_var x s /\
    op_prov Gf (Var x) = op_prov G (Var x) /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!p n. p <> nv /\ p <> cv /\ ptr_covers G tn p s n ==>
    ptr_covers Gf tnf p sf n)
Proof
  strip_tac >>
  gvs[copy_static_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, op_prov_def, op_taint_def,
      bodyPtrDefsTheory.ptr_covers_def]
QED

Theorem storage_body_store_frame:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  sf = ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  Gf = step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s) /\
  tnf = step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn ==>
  Gf = G /\ tnf.t_var = tn.t_var /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  sf.vs_current_bb = s.vs_current_bb /\ sf.vs_inst_idx = SUC s.vs_inst_idx /\
  copy_static sf = copy_static s /\
  (!x. lookup_var x sf = lookup_var x s) /\
  (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n) /\
  mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
    sf.vs_memory s.vs_memory /\
  (!i. (!j. j IN op_taint tn value ==> j < 32) /\
    (i < w2n a \/ w2n a+32 <= i) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tn`, `id`, `PG`, `G`] strip_assume_tac) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[mstore_def] >> conj_tac >- simp[mstore_def] >>
  conj_tac >- simp[copy_static_def, mstore_def] >>
  conj_tac >- simp[lookup_var_def, mstore_def] >>
  conj_tac >- (rpt strip_tac >>
    gvs[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  conj_tac >- (simp[] >> irule typedCopyPtrTheory.mstore_memory_frame) >>
  rpt strip_tac >> qpat_assum `tnf = _` SUBST1_TAC >>
  irule mstore_raw_outside_taint >> simp[]
QED
