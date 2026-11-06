(* Straight-line stages of the actual external copy-loop body. *)
Theory bodyPtrMakeArrayStorageBody
Ancestors
  bodyPtrMakeArrayStorageControl bodyPtrMakeArrayAdd bodyPtrMakeArrayCopyStep
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map words codegenRel fragGasPathPtr typedCopyLoopHeaderPtr
  bodyPtrMakeArrayExternalLoop exprSimStorageCopy

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
  op_prov G src = NONE /\ op_prov G (Var cv) = NONE /\
  s1 = ((update_var av (a+n2w k) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst_base (mk_inst lid opc [Var av] [vv]) s1 = OK (update_var vv w s1) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {av})) (COMPL {vv}))
    (tn with t_var := (tn.t_var |+ (av,{})) |+
      (vv, if opc = SLOAD then key_taint tn.t_stor (a+n2w k)
           else key_taint tn.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {av})) (tn with t_var := tn.t_var |+ (av,{}))
    (OK s1)` by
    (simp[] >> irule storage_body_scalar_add_path >>
     simp[eval_operand_def] >>
     qexistsl_tac [`id`, `src`, `Var cv`] >> simp[eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {av})) (tn with t_var := tn.t_var |+ (av,{})) s1 0
    (DRESTRICT (DRESTRICT G (COMPL {av})) (COMPL {vv}))
    (tn with t_var := (tn.t_var |+ (av,{})) |+
      (vv, if opc = SLOAD then key_taint tn.t_stor (a+n2w k)
           else key_taint tn.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (mp_tac (Q.INST [`s` |-> `s1`, `G` |-> `DRESTRICT G (COMPL {av})`,
      `tn` |-> `tn with t_var := tn.t_var |+ (av,{})`, `src` |-> `Var av`,
      `tmp` |-> `vv`, `id` |-> `lid`, `key` |-> `a+n2w k`] storage_body_load_path) >>
     simp[] >> disch_then irule >>
     gvs[update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
         FLOOKUP_UPDATE, allocas_from_def]) >>
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
  Gf = DRESTRICT (DRESTRICT G (COMPL {av})) (COMPL {vv}) /\
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
