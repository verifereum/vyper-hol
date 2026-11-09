(* Arithmetic and two-region frames for the repeatedly visited Bool body. *)
Theory ctorDeployMemoryRunPtrPrefixBoolBody
Ancestors
  ctorDeployMemoryRunPtrPrefixBoolHeader ctorDeployMemoryRunPtrPrefixBoolWord
  ctorDeployMemoryRunPtrPrefixWordRead ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence instIdxIndep
  abiDecoderExecution abiDecoderContract abiDecoderFrame venomMemProofs venomMemDefs
  valueEncodingProps
  exprLoweringProps ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomState venomInst emitHelper
  words arithmetic list finite_map pred_set codegenRel contextCodegenRel memLocDefs

Theorem prefix_bool_body_add_dispatch[local]:
  step_inst_base (mk_inst iid ADD ops outs) s =
    exec_pure2 $+ (mk_inst iid ADD ops outs) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_bool_body_mul_dispatch[local]:
  step_inst_base (mk_inst iid MUL ops outs) s =
    exec_pure2 $* (mk_inst iid MUL ops outs) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_bool_body_add_step:
  eval_operand a s = SOME u /\ eval_operand b s = SOME v ==>
  step_inst_base (mk_inst iid ADD [a;b] [x]) s =
    OK (update_var x (u+v) s)
Proof
  simp[prefix_bool_body_add_dispatch, exec_pure2_def, mk_inst_def]
QED

Theorem prefix_bool_body_mul_step:
  eval_operand a s = SOME u /\ eval_operand b s = SOME v ==>
  step_inst_base (mk_inst iid MUL [a;b] [x]) s =
    OK (update_var x (u*v) s)
Proof
  simp[prefix_bool_body_mul_dispatch, exec_pure2_def, mk_inst_def]
QED

Theorem prefix_bool_body_arith_ptr_step:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid opc [a;b] [x]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, prefix_bool_body_add_dispatch,
       prefix_bool_body_mul_dispatch, mk_inst_def] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  simp[exec_pure2_def, mk_inst_def, update_var_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem prefix_bool_body_add_ghost:
  eval_operand a s = SOME u /\ eval_operand b s = SOME v ==>
  let inst = mk_inst iid ADD [a;b] [x];
      t = update_var x (u+v) s
  in ghost_step fuel ctx PG G tn inst s =
    (set_prov G [x] (first_prov G [a;b]), step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_bool_body_add_step,
       step_prov_def, out_prov_def, mk_inst_def,
       prefix_bool_body_add_dispatch, exec_pure2_def]
QED

Theorem prefix_bool_body_mul_ghost:
  eval_operand a s = SOME u /\ eval_operand b s = SOME v ==>
  let inst = mk_inst iid MUL [a;b] [x];
      t = update_var x (u*v) s
  in ghost_step fuel ctx PG G tn inst s =
    (DRESTRICT G (COMPL {x}), step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_bool_body_mul_step,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       prefix_bool_body_mul_dispatch, exec_pure2_def]
QED

Theorem prefix_bool_body_arith_taint_frame:
  (opc = ADD \/ opc = MUL) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  let q = step_taint (mk_inst iid opc [a;b] [x]) s t tn in
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!v. v <> x ==> op_taint q (Var v) = op_taint tn (Var v)) /\
    (op_taint tn a = {} /\ op_taint tn b = {} ==>
      op_taint q (Var x) = {})
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       FLOOKUP_UPDATE, DRESTRICT_UNIV, new_site_bytes_def,
       step_writes_def, written_taint_def, out_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF,
       op_taint_def] >>
  simp[EXTENSION, SF CONJ_ss, FAPPLY_FUPDATE_THM] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem prefix_bool_body_eval_update[local]:
  eval_operand (Var v) (update_var x w s) =
    if v = x then SOME w else eval_operand (Var v) s
Proof
  Cases_on `v = x` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem prefix_bool_body_add_n2w:
  eval_operand a s = SOME (n2w m) /\ eval_operand b s = SOME (n2w n) ==>
  step_inst_base (mk_inst iid ADD [a;b] [x]) s =
    OK (update_var x (n2w (m+n)) s)
Proof
  metis_tac[prefix_bool_body_add_step, word_add_n2w]
QED

Theorem prefix_bool_body_mul_n2w:
  eval_operand a s = SOME (n2w m) /\ eval_operand b s = SOME (n2w n) ==>
  step_inst_base (mk_inst iid MUL [a;b] [x]) s =
    OK (update_var x (n2w (m*n)) s)
Proof
  metis_tac[prefix_bool_body_mul_step, word_mul_n2w]
QED

Theorem prefix_bool_body_address_steps:
  ALL_DISTINCT [ip;src;dst;iv;sp0;isrc;sp;dp0;idst;dp] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  scratch < dimword(:256) /\ mload scratch s = n2w i ==>
  let u0 = update_var iv (n2w i) s;
      u1 = update_var sp0 (n2w (a+32)) u0;
      u2 = update_var isrc (n2w (i*32)) u1;
      u3 = update_var sp (n2w ((a+32)+i*32)) u2;
      u4 = update_var dp0 (n2w (d+32)) u3;
      u5 = update_var idst (n2w (i*32)) u4;
      u6 = update_var dp (n2w ((d+32)+i*32)) u5;
      insts = [
        mk_inst iid MLOAD [Var ip] [iv];
        mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
        mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
        mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
        mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
        mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
        mk_inst (iid+6) ADD [Var dp0;Var idst] [dp]]
  in
    step_inst_base (EL 0 insts) s = OK u0 /\
    step_inst_base (EL 1 insts) u0 = OK u1 /\
    step_inst_base (EL 2 insts) u1 = OK u2 /\
    step_inst_base (EL 3 insts) u2 = OK u3 /\
    step_inst_base (EL 4 insts) u3 = OK u4 /\
    step_inst_base (EL 5 insts) u4 = OK u5 /\
    step_inst_base (EL 6 insts) u5 = OK u6 /\
    run_inst_seq insts s = OK u6 /\
    eval_operand (Var sp) u6 = SOME (n2w (a+32+i*32)) /\
    eval_operand (Var dp) u6 = SOME (n2w (d+32+i*32)) /\
    eval_operand (Var iv) u6 = SOME (n2w i) /\
    u6.vs_memory = s.vs_memory /\ u6.vs_data_section = s.vs_data_section /\
    u6.vs_allocas = s.vs_allocas /\ u6.vs_alloca_next = s.vs_alloca_next /\
    u6.vs_halted = s.vs_halted /\ u6.vs_current_bb = s.vs_current_bb /\
    u6.vs_inst_idx = s.vs_inst_idx /\
    (!v. MEM v [ip;src;dst] ==> eval_operand (Var v) u6 = eval_operand (Var v) s)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `u0 = update_var iv (n2w i) s` >>
  qabbrev_tac `u1 = update_var sp0 (n2w (a+32)) u0` >>
  qabbrev_tac `u2 = update_var isrc (n2w (i*32)) u1` >>
  qabbrev_tac `u3 = update_var sp (n2w (a+32+i*32)) u2` >>
  qabbrev_tac `u4 = update_var dp0 (n2w (d+32)) u3` >>
  qabbrev_tac `u5 = update_var idst (n2w (i*32)) u4` >>
  qabbrev_tac `u6 = update_var dp (n2w (d+32+i*32)) u5` >>
  simp[EL, HD, TL] >>
  conj_asm1_tac >- suspend "load" >>
  conj_asm1_tac >- suspend "srcbase" >>
  conj_asm1_tac >- suspend "srcmul" >>
  conj_asm1_tac >- suspend "srcptr" >>
  conj_asm1_tac >- suspend "dstbase" >>
  conj_asm1_tac >- suspend "dstmul" >>
  conj_asm1_tac >- suspend "dstptr" >>
  conj_tac >- simp[run_inst_seq_def] >> suspend "frames"
QED

Resume prefix_bool_body_address_steps[load]:
  qpat_assum `eval_operand (Var ip) s = SOME _`
    (mp_then Any mp_tac prefix_mload_step) >>
  simp[Abbr `u0`, w2n_n2w]
QED

Resume prefix_bool_body_address_steps[srcbase]:
  simp_tac bool_ss [Abbr `u1`] >> irule prefix_bool_body_add_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u0`, prefix_bool_body_eval_update, eval_operand_lit_local]
QED

Resume prefix_bool_body_address_steps[srcmul]:
  simp_tac bool_ss [Abbr `u2`] >> irule prefix_bool_body_mul_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u1`, Abbr `u0`, prefix_bool_body_eval_update, eval_operand_lit_local]
QED

Resume prefix_bool_body_address_steps[srcptr]:
  simp_tac bool_ss [Abbr `u3`] >> irule prefix_bool_body_add_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u2`, Abbr `u1`, prefix_bool_body_eval_update]
QED

Resume prefix_bool_body_address_steps[dstbase]:
  simp_tac bool_ss [Abbr `u4`] >> irule prefix_bool_body_add_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
       prefix_bool_body_eval_update, eval_operand_lit_local]
QED

Resume prefix_bool_body_address_steps[dstmul]:
  simp_tac bool_ss [Abbr `u5`] >> irule prefix_bool_body_mul_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
       prefix_bool_body_eval_update, eval_operand_lit_local]
QED

Resume prefix_bool_body_address_steps[dstptr]:
  simp_tac bool_ss [Abbr `u6`] >> irule prefix_bool_body_add_n2w >>
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u5`, Abbr `u4`, prefix_bool_body_eval_update]
QED

Resume prefix_bool_body_address_steps[frames]:
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `u0`, prefix_bool_body_eval_update] >>
  simp[update_var_def] >> rpt strip_tac >> gvs[] >>
  simp[prefix_bool_body_eval_update]
QED

Finalise prefix_bool_body_address_steps

Theorem prefix_bool_body_arith_certificate:
  (opc = ADD \/ opc = MUL) /\
  eval_operand a s = SOME u /\ eval_operand b s = SOME v /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let inst = mk_inst iid opc [a;b] [x];
      w = if opc = ADD then u+v else u*v;
      t = update_var x w s;
      H = set_prov G [x] (if opc = ADD then first_prov G [a;b] else NONE);
      q = step_taint inst s t tn
  in
    step_inst_base inst s = OK t /\ step_inst f ctx inst s = OK t /\
    ptr_safe_step D lo f ctx fn PG G tn inst s /\
    ghost_step f ctx PG G tn inst s = (H,q) /\
    FLOOKUP H x = (if opc = ADD then first_prov G [a;b] else NONE) /\
    op_taint q (Var x) = {} /\
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!y. y <> x ==> op_taint q (Var y) = op_taint tn (Var y) /\
      FLOOKUP H y = FLOOKUP G y /\
      eval_operand (Var y) t = eval_operand (Var y) s) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `opc = ADD` >- suspend "add" >> suspend "mul"
QED

Resume prefix_bool_body_arith_certificate[add]:
  gvs[] >> rpt strip_tac >>
  `step_inst_base (mk_inst iid ADD [a;b] [x]) s = OK (update_var x (u+v) s)` by
    (irule prefix_bool_body_add_step >> simp[]) >>
  `ghost_step f ctx PG G tn (mk_inst iid ADD [a;b] [x]) s =
    (set_prov G [x] (first_prov G [a;b]),
     step_taint (mk_inst iid ADD [a;b] [x]) s (update_var x (u+v) s) tn)` by
    (irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >> simp[]) >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `t` |-> `update_var x (u+v) s`]
    prefix_bool_body_arith_taint_frame) >>
  simp[update_var_def] >> strip_tac >>
  simp[step_inst_non_invoke, prefix_bool_body_add_step,
       prefix_bool_body_arith_ptr_step,
       SRULE [LET_THM] prefix_bool_body_add_ghost,
       prefix_bool_body_eval_update, update_var_def] >>
  rpt strip_tac >> Cases_on `first_prov G [a;b]` >>
  simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Resume prefix_bool_body_arith_certificate[mul]:
  gvs[] >> rpt strip_tac >>
  `step_inst_base (mk_inst iid MUL [a;b] [x]) s = OK (update_var x (u*v) s)` by
    (irule prefix_bool_body_mul_step >> simp[]) >>
  `ghost_step f ctx PG G tn (mk_inst iid MUL [a;b] [x]) s =
    (DRESTRICT G (COMPL {x}),
     step_taint (mk_inst iid MUL [a;b] [x]) s (update_var x (u*v) s) tn)` by
    (irule (SRULE [LET_THM] prefix_bool_body_mul_ghost) >> simp[]) >>
  mp_tac (Q.INST [`opc` |-> `MUL`, `t` |-> `update_var x (u*v) s`]
    prefix_bool_body_arith_taint_frame) >>
  simp[update_var_def] >> strip_tac >>
  simp[step_inst_non_invoke, prefix_bool_body_mul_step,
       prefix_bool_body_arith_ptr_step,
       SRULE [LET_THM] prefix_bool_body_mul_ghost,
       prefix_bool_body_eval_update, update_var_def,
       set_prov_def, FLOOKUP_DRESTRICT,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Finalise prefix_bool_body_arith_certificate

(* The payload store and scratch increment restore the observational part
   of the loop invariant. Neither store changes any previously decoded word. *)
Theorem prefix_bool_body_store_memory:
  (d + 32*(ncount+1) <= scratch \/ scratch+32 <= d) /\
  i < ncount /\ mload d s = n2w ncount /\
  (!j. j < i ==> mload (d+32+32*j) s = value j) ==>
  let payload = d+32+32*i;
      t = mstore payload w s;
      u = mstore scratch (n2w (SUC i)) t
  in
    mload d u = n2w ncount /\ mload scratch u = n2w (SUC i) /\
    (!j. j < SUC i ==>
      mload (d+32+32*j) u = if j = i then w else value j) /\
    u.vs_data_section = s.vs_data_section /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `!p. d <= p /\ p+32 <= d+32*(ncount+1) ==>
    mload p (mstore scratch (n2w (SUC i))
      (mstore (d+32+32*i) w s)) = mload p (mstore (d+32+32*i) w s)` by
    (rpt strip_tac >> irule mload_mstore_disjoint_proof >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `mload d (mstore (d+32+32*i) w s) = mload d s` by
    (irule mload_mstore_disjoint_proof >> simp[regions_disjoint_def]) >>
  conj_tac >- (first_x_assum (qspec_then `d` mp_tac) >> simp[]) >>
  conj_tac >- simp[mload_mstore_same_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      `d <= d+32+32*j /\ d+32+32*j+32 <= d+32*(ncount+1)` by decide_tac >>
      qpat_assum `!p. d <= p /\ _ ==> _`
        (qspec_then `d+32+32*j` mp_tac) >>
      impl_tac >- simp[] >> disch_then SUBST1_TAC >>
      Cases_on `j = i` >- simp[mload_mstore_same_proof] >>
      `mload (d+32+32*j) (mstore (d+32+32*i) w s) = mload (d+32+32*j) s` by
        (irule mload_mstore_disjoint_proof >> simp[regions_disjoint_def] >> decide_tac) >>
      `j < i` by decide_tac >> gvs[]) >>
  simp_tac (srw_ss()) [mstore_def, LET_THM]
QED

Theorem prefix_bool_body_increment_store:
  ip <> inc /\ iv <> inc /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var iv) s = SOME (n2w i) /\
  FLOOKUP G ip = SOME (scratch,32) /\ FLOOKUP G iv = NONE /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var iv) = {} /\
  i < ncount /\ ncount < dimword(:256) /\
  scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let j = mk_inst iid ADD [Var iv;Lit 1w] [inc];
      k = mk_inst (iid+1) MSTORE [Var ip;Var inc] [];
      t = update_var inc (n2w (SUC i)) s;
      u = mstore scratch (n2w (SUC i)) t;
      H = DRESTRICT G (COMPL {inc});
      q = step_taint j s t tn;
      r = step_taint k t u q
  in
    step_inst_base j s = OK t /\ step_inst_base k t = OK u /\
    run_inst_seq [j;k] s = OK u /\
    (!f. ptr_safe_step D lo f ctx fn PG G tn j s /\
         ghost_step f ctx PG G tn j s = (H,q) /\
         ptr_safe_step D lo f ctx fn PG H q k t /\
         ghost_step f ctx PG H q k t = (H,r)) /\
    r.t_mem = tn.t_mem DIFF {p | scratch <= p /\ p < scratch+32} /\
    r.t_stor = tn.t_stor /\ r.t_trans = tn.t_trans /\ r.t_imm = tn.t_imm /\
    (!v. v <> inc ==> op_taint r (Var v) = op_taint tn (Var v) /\
      FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) u = eval_operand (Var v) s) /\
    op_taint r (Var inc) = {} /\ mload scratch u = n2w (SUC i)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `j = mk_inst iid ADD [Var iv;Lit 1w] [inc]` >>
  qabbrev_tac `k = mk_inst (iid+1) MSTORE [Var ip;Var inc] []` >>
  qabbrev_tac `t = update_var inc (n2w (SUC i)) s` >>
  qabbrev_tac `u = mstore scratch (n2w (SUC i)) t` >>
  qabbrev_tac `H = DRESTRICT G (COMPL {inc})` >>
  qabbrev_tac `q = step_taint j s t tn` >>
  qabbrev_tac `r = step_taint k t u q` >>
  `scratch < dimword(:256)` by decide_tac >>
  `eval_operand (Var ip) t = SOME (n2w scratch) /\
   eval_operand (Var inc) t = SOME (n2w (SUC i)) /\ allocas_from lo t` by
    (simp[Abbr `t`, prefix_bool_body_eval_update] >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base j s = OK t` by
    (simp[Abbr `j`, Abbr `t`, ADD1, GSYM word_add_n2w] >>
     irule prefix_bool_body_add_step >> simp[eval_operand_lit_local]) >>
  `step_inst_base k t = OK u` by
    (qpat_assum `eval_operand (Var ip) t = SOME _`
       (mp_then Any mp_tac prefix_mstore_step) >>
     disch_then drule >> disch_then (qspec_then `iid+1` mp_tac) >>
     simp[Abbr `k`, Abbr `u`, w2n_n2w]) >>
  simp[run_inst_seq_def] >>
  conj_tac >- suspend "paired" >> suspend "frames"
QED

Resume prefix_bool_body_increment_store[paired]:
  gen_tac >>
  `op_taint q (Var inc) = {} /\
   op_taint q (Var ip) = {}` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `t` |-> `t`, `x` |-> `inc`,
       `a` |-> `Var iv`, `b` |-> `Lit 1w`] prefix_bool_body_arith_taint_frame) >>
     simp[Abbr `t`, Abbr `q`, Abbr `j`, update_var_def, op_taint_def] >>
     gvs[op_taint_def]) >>
  conj_tac
  >- (simp[Abbr `j`] >> irule prefix_bool_body_arith_ptr_step >>
      simp[op_taint_def]) >>
  conj_tac
  >- (`ghost_step f ctx PG G tn j s =
        (set_prov G [inc] (first_prov G [Var iv;Lit 1w]),q)` by
        (simp[Abbr `q`, Abbr `j`, Abbr `t`, ADD1, GSYM word_add_n2w] >>
         irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >>
         simp[eval_operand_lit_local]) >>
      gvs[Abbr `H`, first_prov_def, op_prov_def, set_prov_def]) >>
  conj_tac
  >- (simp[Abbr `k`] >> irule prefix_mstore_ptr_step >>
      simp[Abbr `H`, FLOOKUP_DRESTRICT] >>
      qexistsl [`n2w scratch:bytes32`, `scratch`, `32`] >> simp[w2n_n2w]) >>
  gvs[Abbr `r`, Abbr `k`] >> irule prefix_mstore_ghost_step >>
  simp[step_inst_non_invoke]
QED

Resume prefix_bool_body_increment_store[frames]:
  `q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
   q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
   (!v. v <> inc ==> op_taint q (Var v) = op_taint tn (Var v)) /\
   op_taint q (Var inc) = {}` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `t` |-> `t`, `x` |-> `inc`,
       `a` |-> `Var iv`, `b` |-> `Lit 1w`] prefix_bool_body_arith_taint_frame) >>
     simp[Abbr `t`, Abbr `q`, Abbr `j`, update_var_def, op_taint_def] >>
     gvs[op_taint_def]) >>
  `r.t_mem = q.t_mem DIFF {p | scratch <= p /\ p < scratch+32}` by
    (qpat_assum `eval_operand (Var ip) t = SOME _`
       (mp_then Any mp_tac prefix_mstore_mem_taint) >>
     disch_then drule >>
     simp[Abbr `r`, Abbr `k`, Abbr `u`, w2n_n2w]) >>
  `r.t_var = q.t_var /\ r.t_stor = q.t_stor /\
   r.t_trans = q.t_trans /\ r.t_imm = q.t_imm` by
    simp[Abbr `r`, Abbr `k`, SRULE [LET_THM] prefix_mstore_taint_frame] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      simp[Abbr `H`, FLOOKUP_DRESTRICT, op_taint_def] >>
      simp_tac (srw_ss()) [Abbr `u`, Abbr `t`, mstore_def, LET_THM,
        eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      gvs[op_taint_def]) >>
  conj_tac >- gvs[op_taint_def] >>
  simp[Abbr `u`, mload_mstore_same_proof]
QED

Finalise prefix_bool_body_increment_store

(* Concrete successful or reverting execution of all fifteen body instructions.
   The pointer continuation is proved separately at the same endpoint. *)
Theorem prefix_bool_body_execution:
  ALL_DISTINCT [ip;src;dst;iv;sp0;isrc;sp;dp0;idst;dp;x;y;z;inc] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  scratch < dimword(:256) /\ mload scratch s = n2w i /\
  a+32+32*i < dimword(:256) /\ d+32+32*i < dimword(:256) ==>
  let u0 = update_var iv (n2w i) s;
      u1 = update_var sp0 (n2w (a+32)) u0;
      u2 = update_var isrc (n2w (i*32)) u1;
      u3 = update_var sp (n2w (a+32+i*32)) u2;
      u4 = update_var dp0 (n2w (d+32)) u3;
      u5 = update_var idst (n2w (i*32)) u4;
      u6 = update_var dp (n2w (d+32+i*32)) u5;
      w = abi_decode_load DLOAD (n2w (a+32+32*i):bytes32) s;
      v0 = update_var x w u6;
      v1 = update_var y (word_lsr w 1) v0;
      v2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) v1;
      v3 = mstore (d+32+32*i) w v2;
      v4 = update_var inc (n2w (SUC i)) v3;
      v5 = mstore scratch (n2w (SUC i)) v4;
      A = [mk_inst iid MLOAD [Var ip] [iv];
        mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
        mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
        mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
        mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
        mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
        mk_inst (iid+6) ADD [Var dp0;Var idst] [dp]];
      B = [mk_inst (iid+7) DLOAD [Var sp] [x];
        mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
        mk_inst (iid+9) ISZERO [Var y] [z];
        mk_inst (iid+10) ASSERT [Var z] [];
        mk_inst (iid+11) MSTORE [Var dp;Var x] []];
      C = [mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
        mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
        mk_inst (iid+14) JMP [Label hdr] []]
  in
    run_inst_seq (A ++ B ++ C) s =
      if w2n w < 2 then OK (jump_to hdr v5)
      else Abort Revert_abort (revert_state (set_returndata [] v2))
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `u0 = update_var iv (n2w i) s` >>
  qabbrev_tac `u1 = update_var sp0 (n2w (a+32)) u0` >>
  qabbrev_tac `u2 = update_var isrc (n2w (i*32)) u1` >>
  qabbrev_tac `u3 = update_var sp (n2w (a+32+i*32)) u2` >>
  qabbrev_tac `u4 = update_var dp0 (n2w (d+32)) u3` >>
  qabbrev_tac `u5 = update_var idst (n2w (i*32)) u4` >>
  qabbrev_tac `u6 = update_var dp (n2w (d+32+i*32)) u5` >>
  qmatch_goalsub_abbrev_tac `update_var x w u6` >>
  qabbrev_tac `v0 = update_var x w u6` >>
  qabbrev_tac `v1 = update_var y (word_lsr w 1) v0` >>
  qabbrev_tac `v2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) v1` >>
  qabbrev_tac `v3 = mstore (d+32+32*i) w v2` >>
  qabbrev_tac `v4 = update_var inc (n2w (SUC i)) v3` >>
  qabbrev_tac `v5 = mstore scratch (n2w (SUC i)) v4` >>
  qmatch_goalsub_abbrev_tac `A ++ B ++ C` >>
  `run_inst_seq A s = OK u6` by suspend "setup" >>
  `eval_operand (Var sp) u6 = SOME (n2w (a+32+32*i)) /\
   eval_operand (Var dp) u6 = SOME (n2w (d+32+32*i)) /\
   u6.vs_data_section = s.vs_data_section` by suspend "setupframes" >>
  `run_inst_seq B u6 = if w2n w < 2 then OK v3
     else Abort Revert_abort (revert_state (set_returndata [] v2))` by suspend "word" >>
  `run_inst_seq C v3 = OK (jump_to hdr v5)` by suspend "tail" >>
  suspend "compose"
QED

Resume prefix_bool_body_execution[setup]:
  simp_tac bool_ss [Abbr `A`, Abbr `u6`, Abbr `u5`, Abbr `u4`,
    Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`] >>
  irule (cj 8 (SRULE [LET_THM] prefix_bool_body_address_steps)) >>
  gvs[ALL_DISTINCT] >> qexists_tac `scratch` >> simp[]
QED

Resume prefix_bool_body_execution[setupframes]:
  gvs[ALL_DISTINCT] >>
  simp[Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
       Abbr `u0`, prefix_bool_body_eval_update, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Resume prefix_bool_body_execution[word]:
  qpat_assum `eval_operand (Var sp) u6 = SOME _`
    (mp_then Any mp_tac prefix_boolword_execution) >>
  disch_then drule >>
  disch_then (qspecl_then [`z`,`y`,`x`,`iid+7`] mp_tac) >>
  gvs[ALL_DISTINCT, Abbr `B`, Abbr `v3`, Abbr `v2`, Abbr `v1`, Abbr `v0`,
      Abbr `w`, abi_decode_load_def, abi_decode_source_def, w2n_n2w]
QED

Resume prefix_bool_body_execution[tail]:
  `eval_operand (Var iv) v3 = SOME (n2w i) /\
   eval_operand (Var ip) v3 = SOME (n2w scratch)` by
    (gvs[ALL_DISTINCT] >>
     asm_simp_tac (srw_ss()) [Abbr `v3`, Abbr `v2`, Abbr `v1`, Abbr `v0`,
       Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
       Abbr `u0`, mstore_def, LET_THM, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `step_inst_base (mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc]) v3 = OK v4` by
    (simp[Abbr `v4`, ADD1, GSYM word_add_n2w] >>
     irule prefix_bool_body_add_step >> simp[eval_operand_lit_local]) >>
  `eval_operand (Var ip) v4 = SOME (n2w scratch) /\
   eval_operand (Var inc) v4 = SOME (n2w (SUC i))` by
    (gvs[ALL_DISTINCT] >> simp[Abbr `v4`, prefix_bool_body_eval_update]) >>
  `step_inst_base (mk_inst (iid+13) MSTORE [Var ip;Var inc] []) v4 = OK v5` by
    (qpat_assum `eval_operand (Var ip) v4 = SOME _`
       (mp_then Any mp_tac prefix_mstore_step) >>
     disch_then drule >> disch_then (qspec_then `iid+13` mp_tac) >>
     simp[Abbr `v5`, w2n_n2w]) >>
  `step_inst_base (mk_inst (iid+14) JMP [Label hdr] []) v5 = OK (jump_to hdr v5)` by
    simp[mk_inst_def, venomExecProofsTheory.step_jmp_behavior] >>
  simp[Abbr `C`, run_inst_seq_def]
QED

Resume prefix_bool_body_execution[compose]:
  qpat_assum `run_inst_seq A s = OK u6`
    (mp_then Any (qspec_then `B ++ C` assume_tac) run_inst_seq_append) >>
  Cases_on `w2n w < 2` >> gvs[]
  >- (qpat_assum `run_inst_seq B u6 = OK v3`
        (mp_then Any (qspec_then `C` assume_tac) run_inst_seq_append) >> simp[]) >>
  `!t. run_inst_seq B u6 <> OK t` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `C` assume_tac) >> simp[]
QED

Finalise prefix_bool_body_execution

(* Paired initial scratch read, including its indexed trace certificate. *)
Theorem prefix_bool_body_scratch_read:
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  scratch+32 <= dimword(:256) /\ mload scratch s = n2w i /\
  FLOOKUP G ip = SOME (scratch,32) /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> scratch+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let inst = mk_inst iid MLOAD [Var ip] [iv];
      t = update_var iv (n2w i) s;
      H = DRESTRICT G (COMPL {iv});
      q = step_taint inst s t tn
  in
    step_inst_base inst s = OK t /\
    step_inst fuel ctx inst (s with vs_inst_idx := idx) =
      OK (t with vs_inst_idx := idx) /\
    ptr_safe_step D lo fuel ctx fn PG G tn inst (s with vs_inst_idx := idx) /\
    ghost_step fuel ctx PG G tn inst (s with vs_inst_idx := idx) = (H,q) /\
    op_taint q (Var iv) = {} /\ FLOOKUP H iv = NONE /\
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!v. v <> iv ==> op_taint q (Var v) = op_taint tn (Var v) /\
      FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `inst = mk_inst iid MLOAD [Var ip] [iv]` >>
  qabbrev_tac `t = update_var iv (n2w i) s` >>
  qabbrev_tac `H = DRESTRICT G (COMPL {iv})` >>
  qabbrev_tac `q = step_taint inst s t tn` >>
  `scratch < dimword(:256)` by decide_tac >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`, Abbr `t`] >>
     drule prefix_mload_step >> simp[w2n_n2w]) >>
  `step_inst fuel ctx inst s = OK t` by
    simp[Abbr `inst`, step_inst_non_invoke] >>
  simp[] >> conj_tac >- suspend "indexed" >>
  conj_tac >- suspend "safe" >>
  conj_tac >- suspend "ghost" >> suspend "frames"
QED

Resume prefix_bool_body_scratch_read[indexed]:
  simp[step_inst_non_invoke, Abbr `inst`] >>
  simp[step_inst_inst_idx_indep, mk_inst_def,
       is_terminator_def, exec_result_map_def]
QED

Resume prefix_bool_body_scratch_read[safe]:
  simp[Abbr `inst`] >> irule prefix_mload_ptr_step >>
  simp[eval_operand_def, lookup_var_def, allocas_from_def, w2n_n2w] >>
  gvs[eval_operand_def, lookup_var_def, allocas_from_def] >> metis_tac[]
QED

Resume prefix_bool_body_scratch_read[ghost]:
  simp[ghost_step_def, step_inst_non_invoke, Abbr `inst`] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def,
       mk_inst_def, is_terminator_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def] >>
  simp[Abbr `H`, Abbr `q`, Abbr `t`, step_taint_def, mk_inst_def,
       update_var_def, mem_taint_def, out_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, mem_word_taint_def, eval_operand_def,
       lookup_var_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def] >>
  gvs[eval_operand_def, lookup_var_def, w2n_n2w]
QED

Resume prefix_bool_body_scratch_read[frames]:
  `op_taint q (Var iv) = {}` by
    (simp[Abbr `q`, Abbr `inst`] >> irule prefix_mload_output_clean >>
     qexists_tac `n2w scratch:bytes32` >> simp[w2n_n2w] >>
     metis_tac[ADD_COMM]) >>
  mp_tac (Q.INST [`x` |-> `iv`, `w` |-> `n2w i`, `addr` |-> `Var ip`]
    (SRULE [LET_THM] prefix_mload_taint_frame)) >>
  simp[Abbr `q`, Abbr `inst`, Abbr `t`] >> strip_tac >>
  simp[Abbr `H`, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  simp[prefix_bool_body_eval_update] >> gvs[op_taint_def]
QED

Finalise prefix_bool_body_scratch_read

(* The paired boundary uses the very same endpoints as the raw execution. *)
Theorem prefix_bool_success_idx[local]:
  MEM inst.inst_opcode [MLOAD;ADD;MUL;DLOAD;SHR;ISZERO;ASSERT;MSTORE] /\
  step_inst f ctx inst s = OK s' /\
  (!check_fn. ptr_safe_step D lo f ctx check_fn PG G tn inst s) /\
  ghost_step f ctx PG G tn inst s = (G',tn') ==>
  step_inst f ctx inst (s with vs_inst_idx := idx) =
    OK (s' with vs_inst_idx := idx) /\
  ptr_safe_step D lo f ctx fn PG G tn inst (s with vs_inst_idx := idx) /\
  ghost_step f ctx PG G tn inst (s with vs_inst_idx := idx) = (G',tn')
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> REVERT /\ inst.inst_opcode <> RETURNDATACOPY` by
    (qpat_x_assum `MEM _ _` mp_tac >> simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  `step_inst f ctx inst (s with vs_inst_idx := idx) =
     OK (s' with vs_inst_idx := idx)` by
    (gvs[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "safety" >> suspend "ghost"
QED

Resume prefix_bool_success_idx[safety]:
  `source_memory_read_ranges inst (s with vs_inst_idx := idx) =
     source_memory_read_ranges inst s /\
   source_memory_write_ranges inst (s with vs_inst_idx := idx) =
     source_memory_write_ranges inst s` by
    (qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >>
     gvs[source_memory_read_ranges_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, eval_op_inst_idx]) >>
  qpat_x_assum `!check_fn. _` (qspec_then `fn with fn_blocks := []` mp_tac) >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, in_revert_forward_def,
       lookup_block_def, about_to_revert_def] >>
  simp[access_ok_def, taint_ok_def, in_revert_forward_def,
       lookup_block_def, about_to_revert_def, allocas_from_def,
       allocas_below_fmp_def, eval_op_inst_idx, FIND_thm] >>
  strip_tac >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume prefix_bool_success_idx[ghost]:
  gvs[ghost_step_def] >>
  simp[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       out_taint_def, store_taint_def, imm_taint_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       eval_op_inst_idx]
QED

Finalise prefix_bool_success_idx

Theorem prefix_bool_body_paired:
  ALL_DISTINCT [ip;src;dst;iv;sp0;isrc;sp;dp0;idst;dp;x;y;z;inc] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  FLOOKUP G ip = SOME (scratch,32) /\ FLOOKUP G src = NONE /\
  FLOOKUP G dst = SOME (b,sz) /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var src) = {} /\
  op_taint tn (Var dst) = {} /\ i < ncount /\ ncount < dimword(:256) /\
  a+32*(ncount+1) < dimword(:256) /\
  b <= d /\ d+32*(ncount+1) <= b+sz /\ b+sz <= s.vs_alloca_next /\
  scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  (d+32*(ncount+1) <= scratch \/ scratch+32 <= d) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  mload scratch s = n2w i /\ mload d s = n2w ncount /\
  (!j. j<i ==> mload (d+32+32*j) s = value j) /\
  (!r. r<32 ==> scratch+r NOTIN tn.t_mem) /\
  (!r. r<32*(i+1) ==> d+r NOTIN tn.t_mem) ==>
  let u0 = update_var iv (n2w i) s;
      u1 = update_var sp0 (n2w (a+32)) u0;
      u2 = update_var isrc (n2w (i*32)) u1;
      u3 = update_var sp (n2w (a+32+i*32)) u2;
      u4 = update_var dp0 (n2w (d+32)) u3;
      u5 = update_var idst (n2w (i*32)) u4;
      u6 = update_var dp (n2w (d+32+i*32)) u5;
      w = abi_decode_load DLOAD (n2w (a+32+32*i):bytes32) s;
      v0 = update_var x w u6;
      v1 = update_var y (word_lsr w 1) v0;
      v2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) v1;
      v3 = mstore (d+32+32*i) w v2;
      v4 = update_var inc (n2w (SUC i)) v3;
      v5 = mstore scratch (n2w (SUC i)) v4;
      A = [mk_inst iid MLOAD [Var ip] [iv];
        mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
        mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
        mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
        mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
        mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
        mk_inst (iid+6) ADD [Var dp0;Var idst] [dp]];
      B = [mk_inst (iid+7) DLOAD [Var sp] [x];
        mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
        mk_inst (iid+9) ISZERO [Var y] [z];
        mk_inst (iid+10) ASSERT [Var z] [];
        mk_inst (iid+11) MSTORE [Var dp;Var x] []];
      C = [mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
        mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
        mk_inst (iid+14) JMP [Label hdr] []];
      k = s.vs_inst_idx;
      I = A ++ B ++ C;
      U = [s;u0;u1;u2;u3;u4;u5;u6;v0;v1;v2;v2;v3;v4;v5];
      N = if w2n w < 2 then 14 else 10;
      V = (\j. (EL j U) with vs_inst_idx := k+j);
      J = jump_to hdr v5
  in
    (run_inst_seq I s = if w2n w < 2 then OK J
      else Abort Revert_abort (revert_state (set_returndata [] v2))) /\
    ?gs ts.
      LENGTH gs = N+1 /\ LENGTH ts = N+1 /\ HD gs = G /\ HD ts = tn /\
      (!j f. j<N ==>
        step_inst f ctx (EL j I) (V j) =
          OK ((EL (j+1) U) with vs_inst_idx := k+j) /\
        ptr_safe_step D lo f ctx fn PG (EL j gs) (EL j ts) (EL j I) (V j) /\
        ghost_step f ctx PG (EL j gs) (EL j ts) (EL j I) (V j) =
          (EL (j+1) gs,EL (j+1) ts)) /\
      (let H = LAST gs; q = LAST ts in
        (if w2n w < 2 then
          (!f. step_inst f ctx (EL 14 I) (V 14) = OK J /\
            ptr_safe_step D lo f ctx fn PG H q (EL 14 I) (V 14)) /\
          mload d J = n2w ncount /\ mload scratch J = n2w (SUC i) /\
          (!j. j<SUC i ==> mload (d+32+32*j) J =
            if j=i then w else value j) /\
          (!r. r<32 ==> scratch+r NOTIN q.t_mem) /\
          (!r. r<32*(SUC i+1) ==> d+r NOTIN q.t_mem) /\
          (!v. MEM v [ip;src;dst] ==>
            eval_operand (Var v) J = eval_operand (Var v) s /\
            FLOOKUP H v = FLOOKUP G v /\ op_taint q (Var v) = op_taint tn (Var v)) /\
          J.vs_data_section = s.vs_data_section /\ J.vs_allocas = s.vs_allocas /\
          J.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo J /\
          ~J.vs_halted /\ J.vs_current_bb = hdr /\ J.vs_inst_idx = 0 /\
          q.t_stor = tn.t_stor /\ q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
          (!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
            (p+len<=scratch \/ scratch+32<=p) ==>
            mem_bytes_at p len J.vs_memory = mem_bytes_at p len s.vs_memory)
        else !f.
          ptr_safe_step D lo f ctx fn PG H q (EL 10 I) (V 10) /\
          step_inst f ctx (EL 10 I) (V 10) =
            Abort Revert_abort (revert_state (set_returndata [] (V 10)))) /\
        (!bb. isPREFIX I (DROP k bb.bb_instructions) ==>
          ((w2n w<2 ==> !f. ptr_safe_blocks D lo f ctx fn PG
              (entry_prov fn J H) (entry_taint_vars fn J q) J) ==>
            !f. ptr_safe_block D lo f ctx fn PG G tn bb s)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  conj_tac >- suspend "execution" >>
  suspend "assembly"
QED

Resume prefix_bool_body_paired[execution]:
  pure_rewrite_tac[APPEND] >>
  irule (SRULE [LET_THM] prefix_bool_body_execution) >>
  gvs[ALL_DISTINCT] >> decide_tac
QED

Resume prefix_bool_body_paired[assembly]:
  qabbrev_tac `u0 = update_var iv (n2w i) s` >>
  qabbrev_tac `u1 = update_var sp0 (n2w (a+32)) u0` >>
  qabbrev_tac `u2 = update_var isrc (n2w (i*32)) u1` >>
  qabbrev_tac `u3 = update_var sp (n2w (a+32+i*32)) u2` >>
  qabbrev_tac `u4 = update_var dp0 (n2w (d+32)) u3` >>
  qabbrev_tac `u5 = update_var idst (n2w (i*32)) u4` >>
  qabbrev_tac `u6 = update_var dp (n2w (d+32+i*32)) u5` >>
  qabbrev_tac `w = abi_decode_load DLOAD (n2w (a+32+32*i):bytes32) s` >>
  qabbrev_tac `v0 = update_var x w u6` >>
  qabbrev_tac `v1 = update_var y (word_lsr w 1) v0` >>
  qabbrev_tac `v2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) v1` >>
  qabbrev_tac `v3 = mstore (d+32+32*i) w v2` >>
  qabbrev_tac `v4 = update_var inc (n2w (SUC i)) v3` >>
  qabbrev_tac `v5 = mstore scratch (n2w (SUC i)) v4` >>
  qabbrev_tac `J = jump_to hdr v5` >>
  qabbrev_tac `insns =
    [mk_inst iid MLOAD [Var ip] [iv];
     mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
     mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
     mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
     mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
     mk_inst (iid+6) ADD [Var dp0;Var idst] [dp]] ++
    [mk_inst (iid+7) DLOAD [Var sp] [x];
     mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
     mk_inst (iid+9) ISZERO [Var y] [z];
     mk_inst (iid+10) ASSERT [Var z] [];
     mk_inst (iid+11) MSTORE [Var dp;Var x] []] ++
    [mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
     mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
     mk_inst (iid+14) JMP [Label hdr] []]` >>
  qabbrev_tac `U = [s;u0;u1;u2;u3;u4;u5;u6;v0;v1;v2;v2;v3;v4;v5]` >>
  qabbrev_tac `N = if w2n w < 2 then 14 else 10` >>
  qabbrev_tac `k = s.vs_inst_idx` >>
  qabbrev_tac `g0 = DRESTRICT G (COMPL {iv})` >>
  qabbrev_tac `t0 = step_taint (mk_inst iid MLOAD [Var ip] [iv]) s u0 tn` >>
  `(!f. step_inst f ctx (EL 0 insns) (s with vs_inst_idx := k) =
           OK (u0 with vs_inst_idx := k) /\
         ptr_safe_step D lo f ctx fn PG G tn (EL 0 insns)
           (s with vs_inst_idx := k) /\
         ghost_step f ctx PG G tn (EL 0 insns) (s with vs_inst_idx := k) = (g0,t0)) /\
   op_taint t0 (Var iv) = {} /\ FLOOKUP g0 iv = NONE /\
   t0.t_mem = tn.t_mem /\ t0.t_stor = tn.t_stor /\
   t0.t_trans = tn.t_trans /\ t0.t_imm = tn.t_imm /\
   (!v. v <> iv ==> op_taint t0 (Var v) = op_taint tn (Var v) /\
      FLOOKUP g0 v = FLOOKUP G v /\
      eval_operand (Var v) u0 = eval_operand (Var v) s)` by suspend "read" >>
  suspend "setup_rest"
QED

Resume prefix_bool_body_paired[read]:
  simp_tac bool_ss [Abbr `insns`, APPEND, EL, HD] >>
  rpt conj_tac >> rpt gen_tac >>
  mp_tac (Q.INST [`idx` |-> `k`, `fuel` |-> `f`]
    (SRULE [LET_THM] prefix_bool_body_scratch_read)) >>
  impl_tac >- (simp[] >> decide_tac) >>
  simp[Abbr `g0`, Abbr `t0`, Abbr `u0`]
QED

Resume prefix_bool_body_paired[setup_rest]:
  qabbrev_tac `g1 = set_prov g0 [sp0] (first_prov g0 [Var src;Lit 32w])` >>
  qabbrev_tac `t1 = step_taint (EL 1 insns) u0 u1 t0` >>
  `eval_operand (Var src) u0 = SOME (n2w a) /\
   op_taint t0 (Var src) = {} /\ allocas_from lo u0` by
    (`src <> iv` by
       (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
     qpat_assum `!v. v <> iv ==> _` (qspec_then `src` mp_tac) >>
     simp[] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     simp[Abbr `u0`, allocas_from_def, update_var_def]) >>
  `!f check_fn. step_inst_base (EL 1 insns) u0 = OK u1 /\
    step_inst f ctx (EL 1 insns) u0 = OK u1 /\
    ptr_safe_step D lo f ctx check_fn PG g0 t0 (EL 1 insns) u0 /\
    ghost_step f ctx PG g0 t0 (EL 1 insns) u0 = (g1,t1) /\
    FLOOKUP g1 sp0 = first_prov g0 [Var src;Lit 32w] /\
    op_taint t1 (Var sp0) = {} /\
    t1.t_mem = t0.t_mem /\ t1.t_stor = t0.t_stor /\
    t1.t_trans = t0.t_trans /\ t1.t_imm = t0.t_imm /\
    (!v. v <> sp0 ==> op_taint t1 (Var v) = op_taint t0 (Var v) /\
      FLOOKUP g1 v = FLOOKUP g0 v /\
      eval_operand (Var v) u1 = eval_operand (Var v) u0) /\
    u1.vs_memory = u0.vs_memory /\ u1.vs_data_section = u0.vs_data_section /\
    u1.vs_allocas = u0.vs_allocas /\ u1.vs_alloca_next = u0.vs_alloca_next /\
    u1.vs_inst_idx = u0.vs_inst_idx /\ u1.vs_current_bb = u0.vs_current_bb /\
    u1.vs_halted = u0.vs_halted` by suspend "source_add" >>
  suspend "setup_arith_rest"
QED

Resume prefix_bool_body_paired[source_add]:
  rpt gen_tac >>
  `EL 1 insns = mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g1`, Abbr `t1`, Abbr `u1`] >>
  qpat_x_assum `EL 1 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM word_add_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_bool_body_arith_certificate))) >>
  simp[eval_operand_lit_local, op_taint_def]
QED

Resume prefix_bool_body_paired[setup_arith_rest]:
  qpat_assum `!f check_fn. step_inst_base _ _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `iv <> sp0` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var iv) u1 = SOME (n2w i) /\
   op_taint t1 (Var iv) = {} /\ allocas_from lo u1` by
    (conj_tac
     >- simp[Abbr `u1`, Abbr `u0`, prefix_bool_body_eval_update] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `allocas_from lo u0` mp_tac >>
     simp[Abbr `u1`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g2 = set_prov g1 [isrc] NONE` >>
  qabbrev_tac `t2 = step_taint (EL 2 insns) u1 u2 t1` >>
  `!f check_fn. step_inst_base (EL 2 insns) u1 = OK u2 /\
    step_inst f ctx (EL 2 insns) u1 = OK u2 /\
    ptr_safe_step D lo f ctx check_fn PG g1 t1 (EL 2 insns) u1 /\
    ghost_step f ctx PG g1 t1 (EL 2 insns) u1 = (g2,t2) /\
    FLOOKUP g2 isrc = NONE /\ op_taint t2 (Var isrc) = {} /\
    t2.t_mem = t1.t_mem /\ t2.t_stor = t1.t_stor /\
    t2.t_trans = t1.t_trans /\ t2.t_imm = t1.t_imm /\
    (!v. v <> isrc ==> op_taint t2 (Var v) = op_taint t1 (Var v) /\
      FLOOKUP g2 v = FLOOKUP g1 v /\
      eval_operand (Var v) u2 = eval_operand (Var v) u1) /\
    u2.vs_memory = u1.vs_memory /\ u2.vs_data_section = u1.vs_data_section /\
    u2.vs_allocas = u1.vs_allocas /\ u2.vs_alloca_next = u1.vs_alloca_next /\
    u2.vs_inst_idx = u1.vs_inst_idx /\ u2.vs_current_bb = u1.vs_current_bb /\
    u2.vs_halted = u1.vs_halted` by suspend "source_mul" >>
  suspend "setup_after_mul"
QED

Resume prefix_bool_body_paired[source_mul]:
  rpt gen_tac >>
  `EL 2 insns = mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g2`, Abbr `t2`, Abbr `u2`] >>
  qpat_x_assum `EL 2 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM word_mul_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `MUL`]
    prefix_bool_body_arith_certificate))) >>
  simp[eval_operand_lit_local, op_taint_def]
QED

Resume prefix_bool_body_paired[setup_after_mul]:
  qpat_assum `!f check_fn. step_inst_base (EL 2 insns) _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `sp0 <> isrc` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var sp0) u2 = SOME (n2w (a+32)) /\
   eval_operand (Var isrc) u2 = SOME (n2w (i*32)) /\
   op_taint t2 (Var sp0) = {} /\ allocas_from lo u2` by
    (conj_tac
     >- simp[Abbr `u2`, Abbr `u1`, prefix_bool_body_eval_update] >>
     conj_tac >- simp[Abbr `u2`, prefix_bool_body_eval_update] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `allocas_from lo u1` mp_tac >>
     simp[Abbr `u2`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g3 = set_prov g2 [sp] (first_prov g2 [Var sp0;Var isrc])` >>
  qabbrev_tac `t3 = step_taint (EL 3 insns) u2 u3 t2` >>
  `!f check_fn. step_inst_base (EL 3 insns) u2 = OK u3 /\
    step_inst f ctx (EL 3 insns) u2 = OK u3 /\
    ptr_safe_step D lo f ctx check_fn PG g2 t2 (EL 3 insns) u2 /\
    ghost_step f ctx PG g2 t2 (EL 3 insns) u2 = (g3,t3) /\
    FLOOKUP g3 sp = first_prov g2 [Var sp0;Var isrc] /\
    op_taint t3 (Var sp) = {} /\
    t3.t_mem = t2.t_mem /\ t3.t_stor = t2.t_stor /\
    t3.t_trans = t2.t_trans /\ t3.t_imm = t2.t_imm /\
    (!v. v <> sp ==> op_taint t3 (Var v) = op_taint t2 (Var v) /\
      FLOOKUP g3 v = FLOOKUP g2 v /\
      eval_operand (Var v) u3 = eval_operand (Var v) u2) /\
    u3.vs_memory = u2.vs_memory /\ u3.vs_data_section = u2.vs_data_section /\
    u3.vs_allocas = u2.vs_allocas /\ u3.vs_alloca_next = u2.vs_alloca_next /\
    u3.vs_inst_idx = u2.vs_inst_idx /\ u3.vs_current_bb = u2.vs_current_bb /\
    u3.vs_halted = u2.vs_halted` by suspend "source_ptr" >>
  suspend "setup_after_source"
QED

Resume prefix_bool_body_paired[source_ptr]:
  rpt gen_tac >>
  `EL 3 insns = mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g3`, Abbr `t3`, Abbr `u3`] >>
  qpat_x_assum `EL 3 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM ADD_ASSOC, GSYM word_add_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_bool_body_arith_certificate))) >> simp[word_add_n2w]
QED

Resume prefix_bool_body_paired[setup_after_source]:
  qpat_assum `!f check_fn. step_inst_base (EL 3 insns) _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `dst <> iv /\ dst <> sp0 /\ dst <> isrc /\ dst <> sp` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var dst) u3 = SOME (n2w d) /\
   op_taint t3 (Var dst) = {} /\ allocas_from lo u3` by
    (conj_tac
     >- simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
             prefix_bool_body_eval_update] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `allocas_from lo u2` mp_tac >>
     simp[Abbr `u3`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g4 = set_prov g3 [dp0] (first_prov g3 [Var dst;Lit 32w])` >>
  qabbrev_tac `t4 = step_taint (EL 4 insns) u3 u4 t3` >>
  `!f check_fn. step_inst_base (EL 4 insns) u3 = OK u4 /\
    step_inst f ctx (EL 4 insns) u3 = OK u4 /\
    ptr_safe_step D lo f ctx check_fn PG g3 t3 (EL 4 insns) u3 /\
    ghost_step f ctx PG g3 t3 (EL 4 insns) u3 = (g4,t4) /\
    FLOOKUP g4 dp0 = first_prov g3 [Var dst;Lit 32w] /\
    op_taint t4 (Var dp0) = {} /\
    t4.t_mem = t3.t_mem /\ t4.t_stor = t3.t_stor /\
    t4.t_trans = t3.t_trans /\ t4.t_imm = t3.t_imm /\
    (!v. v <> dp0 ==> op_taint t4 (Var v) = op_taint t3 (Var v) /\
      FLOOKUP g4 v = FLOOKUP g3 v /\
      eval_operand (Var v) u4 = eval_operand (Var v) u3) /\
    u4.vs_memory = u3.vs_memory /\ u4.vs_data_section = u3.vs_data_section /\
    u4.vs_allocas = u3.vs_allocas /\ u4.vs_alloca_next = u3.vs_alloca_next /\
    u4.vs_inst_idx = u3.vs_inst_idx /\ u4.vs_current_bb = u3.vs_current_bb /\
    u4.vs_halted = u3.vs_halted` by suspend "dest_add" >>
  suspend "setup_after_dest_add"
QED

Resume prefix_bool_body_paired[dest_add]:
  rpt gen_tac >>
  `EL 4 insns = mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g4`, Abbr `t4`, Abbr `u4`] >>
  qpat_x_assum `EL 4 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM word_add_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_bool_body_arith_certificate))) >>
  simp[eval_operand_lit_local, op_taint_def]
QED

Resume prefix_bool_body_paired[setup_after_dest_add]:
  qpat_assum `!f check_fn. step_inst_base (EL 4 insns) _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `iv <> sp /\ iv <> dp0 /\ iv <> isrc /\ iv <> sp0` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var iv) u4 = SOME (n2w i) /\
   op_taint t4 (Var iv) = {} /\ allocas_from lo u4` by
    (conj_tac
     >- simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
             prefix_bool_body_eval_update, ALL_DISTINCT] >>
     conj_tac
     >- (qpat_assum `!v. v <> dp0 ==> _` (qspec_then `iv` mp_tac) >>
         qpat_assum `!v. v <> sp ==> _` (qspec_then `iv` mp_tac) >>
         qpat_assum `!v. v <> isrc ==> _` (qspec_then `iv` mp_tac) >>
         `iv <> isrc` by
           (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
         simp[]) >>
     qpat_x_assum `allocas_from lo u3` mp_tac >>
     simp[Abbr `u4`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g5 = set_prov g4 [idst] NONE` >>
  qabbrev_tac `t5 = step_taint (EL 5 insns) u4 u5 t4` >>
  `!f check_fn. step_inst_base (EL 5 insns) u4 = OK u5 /\
    step_inst f ctx (EL 5 insns) u4 = OK u5 /\
    ptr_safe_step D lo f ctx check_fn PG g4 t4 (EL 5 insns) u4 /\
    ghost_step f ctx PG g4 t4 (EL 5 insns) u4 = (g5,t5) /\
    FLOOKUP g5 idst = NONE /\ op_taint t5 (Var idst) = {} /\
    t5.t_mem = t4.t_mem /\ t5.t_stor = t4.t_stor /\
    t5.t_trans = t4.t_trans /\ t5.t_imm = t4.t_imm /\
    (!v. v <> idst ==> op_taint t5 (Var v) = op_taint t4 (Var v) /\
      FLOOKUP g5 v = FLOOKUP g4 v /\
      eval_operand (Var v) u5 = eval_operand (Var v) u4) /\
    u5.vs_memory = u4.vs_memory /\ u5.vs_data_section = u4.vs_data_section /\
    u5.vs_allocas = u4.vs_allocas /\ u5.vs_alloca_next = u4.vs_alloca_next /\
    u5.vs_inst_idx = u4.vs_inst_idx /\ u5.vs_current_bb = u4.vs_current_bb /\
    u5.vs_halted = u4.vs_halted` by suspend "dest_mul" >>
  suspend "setup_after_dest_mul"
QED

Resume prefix_bool_body_paired[dest_mul]:
  rpt gen_tac >>
  `EL 5 insns = mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g5`, Abbr `t5`, Abbr `u5`] >>
  qpat_x_assum `EL 5 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM word_mul_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `MUL`]
    prefix_bool_body_arith_certificate))) >>
  simp[eval_operand_lit_local, op_taint_def]
QED

Resume prefix_bool_body_paired[setup_after_dest_mul]:
  qpat_assum `!f check_fn. step_inst_base (EL 5 insns) _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `dp0 <> idst` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var dp0) u5 = SOME (n2w (d+32)) /\
   eval_operand (Var idst) u5 = SOME (n2w (i*32)) /\
   op_taint t5 (Var dp0) = {} /\ allocas_from lo u5` by
    (conj_tac
     >- simp[Abbr `u5`, Abbr `u4`, prefix_bool_body_eval_update] >>
     conj_tac >- simp[Abbr `u5`, prefix_bool_body_eval_update] >>
     conj_tac
     >- (qpat_assum `!v. v <> idst ==> _` (qspec_then `dp0` mp_tac) >> simp[]) >>
     qpat_x_assum `allocas_from lo u4` mp_tac >>
     simp[Abbr `u5`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g6 = set_prov g5 [dp] (first_prov g5 [Var dp0;Var idst])` >>
  qabbrev_tac `t6 = step_taint (EL 6 insns) u5 u6 t5` >>
  `!f check_fn. step_inst_base (EL 6 insns) u5 = OK u6 /\
    step_inst f ctx (EL 6 insns) u5 = OK u6 /\
    ptr_safe_step D lo f ctx check_fn PG g5 t5 (EL 6 insns) u5 /\
    ghost_step f ctx PG g5 t5 (EL 6 insns) u5 = (g6,t6) /\
    FLOOKUP g6 dp = first_prov g5 [Var dp0;Var idst] /\
    op_taint t6 (Var dp) = {} /\
    t6.t_mem = t5.t_mem /\ t6.t_stor = t5.t_stor /\
    t6.t_trans = t5.t_trans /\ t6.t_imm = t5.t_imm /\
    (!v. v <> dp ==> op_taint t6 (Var v) = op_taint t5 (Var v) /\
      FLOOKUP g6 v = FLOOKUP g5 v /\
      eval_operand (Var v) u6 = eval_operand (Var v) u5) /\
    u6.vs_memory = u5.vs_memory /\ u6.vs_data_section = u5.vs_data_section /\
    u6.vs_allocas = u5.vs_allocas /\ u6.vs_alloca_next = u5.vs_alloca_next /\
    u6.vs_inst_idx = u5.vs_inst_idx /\ u6.vs_current_bb = u5.vs_current_bb /\
    u6.vs_halted = u5.vs_halted` by suspend "dest_ptr" >>
  suspend "setup_complete"
QED

Resume prefix_bool_body_paired[dest_ptr]:
  rpt gen_tac >>
  `EL 6 insns = mk_inst (iid+6) ADD [Var dp0;Var idst] [dp]` by
    simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g6`, Abbr `t6`, Abbr `u6`] >>
  qpat_x_assum `EL 6 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [GSYM ADD_ASSOC, GSYM word_add_n2w] >>
  irule (GEN_ALL (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_bool_body_arith_certificate))) >> simp[word_add_n2w]
QED

Resume prefix_bool_body_paired[setup_complete]:
  qpat_assum `!f check_fn. step_inst_base (EL 6 insns) _ = _ /\ _`
    (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `FLOOKUP g6 dp = SOME (b,sz)` by suspend "destination_provenance" >>
  `eval_operand (Var sp) u6 = SOME (n2w (a+32+32*i)) /\
   eval_operand (Var dp) u6 = SOME (n2w (d+32+32*i))` by
    (`sp <> dp /\ sp <> idst /\ sp <> dp0` by
       (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
     simp[Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`,
          prefix_bool_body_eval_update, Once MULT_COMM]) >>
  suspend "word_prepare"
QED

Resume prefix_bool_body_paired[destination_provenance]:
  `dst <> iv /\ dst <> sp0 /\ dst <> isrc /\ dst <> sp /\
   dp0 <> idst` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  qpat_assum `!v. v <> idst ==> _` (qspec_then `dp0` strip_assume_tac o SRULE []) >>
  qpat_assum `!v. v <> sp ==> _` (qspec_then `dst` mp_tac) >>
  qpat_assum `!v. v <> isrc ==> _` (qspec_then `dst` mp_tac) >>
  qpat_assum `!v. v <> sp0 ==> _` (qspec_then `dst` mp_tac) >>
  qpat_assum `!v. v <> iv ==> _` (qspec_then `dst` mp_tac) >>
  simp[first_prov_def, op_prov_def] >> rpt strip_tac >>
  gvs[first_prov_def, op_prov_def]
QED

Resume prefix_bool_body_paired[word_prepare]:
  `sp <> dp /\ sp <> idst /\ sp <> dp0` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `op_taint t6 (Var sp) = {} /\ op_taint t6 (Var dp) = {}` by
    (conj_tac >-
      (qpat_assum `!v. v <> dp ==> _` (qspec_then `sp` mp_tac) >>
       qpat_assum `!v. v <> idst ==> _` (qspec_then `sp` mp_tac) >>
       qpat_assum `!v. v <> dp0 ==> _` (qspec_then `sp` mp_tac) >> simp[]) >>
     simp[]) >>
  `allocas_from lo u6` by
    (qpat_x_assum `allocas_from lo u5` mp_tac >>
     simp[Abbr `u6`, allocas_from_def, update_var_def]) >>
  `d+32+32*i < dimword(:256) /\
   b <= d+32+32*i /\ d+32+32*i+32 <= b+sz` by decide_tac >>
  `b <= w2n (n2w (d+32+32*i):bytes32) /\
   w2n (n2w (d+32+32*i):bytes32)+32 <= b+sz` by simp[] >>
  suspend "word_certificates"
QED

Resume prefix_bool_body_paired[word_certificates]:
  qabbrev_tac `g7 = DRESTRICT g6 (COMPL {x})` >>
  qabbrev_tac `t7 = step_taint (EL 7 insns) u6 v0 t6` >>
  `EL 7 insns = mk_inst (iid+7) DLOAD [Var sp] [x]` by simp[Abbr `insns`] >>
  `u6.vs_data_section = s.vs_data_section` by simp[Abbr `u0`, update_var_def] >>
  `step_inst_base (EL 7 insns) u6 = OK v0` by suspend "word_load_raw" >>
  `!f check_fn. step_inst f ctx (EL 7 insns) u6 = OK v0 /\
    ptr_safe_step D lo f ctx check_fn PG g6 t6 (EL 7 insns) u6 /\
    ghost_step f ctx PG g6 t6 (EL 7 insns) u6 = (g7,t7)` by
    (rpt gen_tac >> conj_tac
     >- (qpat_x_assum `step_inst_base (EL 7 insns) u6 = _` mp_tac >>
         simp[step_inst_non_invoke, mk_inst_def]) >>
     conj_tac
     >- (qpat_x_assum `EL 7 insns = _` (fn th => pure_rewrite_tac [th]) >>
         irule prefix_dload_ptr_step >> simp[]) >>
     qpat_x_assum `step_inst_base (EL 7 insns) u6 = _` mp_tac >>
     simp[ghost_step_def, step_inst_non_invoke, Abbr `g7`, Abbr `t7`,
          step_prov_def, out_prov_def, set_prov_def, mk_inst_def]) >>
  suspend "word_after_load"
QED

Resume prefix_bool_body_paired[word_load_raw]:
  qpat_assum `eval_operand (Var sp) u6 = _`
    (mp_then Any mp_tac prefix_dload_step) >>
  disch_then (qspecl_then [`iid+7`,`x`] mp_tac) >>
  simp[Abbr `v0`, Abbr `w`, abi_decode_load_def, abi_decode_source_def]
QED

Resume prefix_bool_body_paired[word_after_load]:
  `eval_operand (Var x) v0 = SOME w` by
    simp[Abbr `v0`, prefix_bool_body_eval_update] >>
  `op_taint t7 (Var x) = {}` by
    simp[Abbr `t7`, prefix_dload_output_taint] >>
  `allocas_from lo v0` by
    (qpat_x_assum `allocas_from lo u6` mp_tac >>
     simp[Abbr `v0`, allocas_from_def, update_var_def]) >>
  qabbrev_tac `g8 = DRESTRICT g7 (COMPL {y})` >>
  qabbrev_tac `g9 = DRESTRICT g8 (COMPL {z})` >>
  qabbrev_tac `t8 = step_taint (EL 8 insns) v0 v1 t7` >>
  qabbrev_tac `t9 = step_taint (EL 9 insns) v1 v2 t8` >>
  `!f check_fn. step_inst_base (EL 8 insns) v0 = OK v1 /\
    step_inst_base (EL 9 insns) v1 = OK v2 /\
    step_inst_base (EL 10 insns) v2 =
      (if w2n w < 2 then OK v2
       else Abort Revert_abort (revert_state (set_returndata [] v2))) /\
    ghost_step f ctx PG g7 t7 (EL 8 insns) v0 = (g8,t8) /\
    ghost_step f ctx PG g8 t8 (EL 9 insns) v1 = (g9,t9) /\
    ghost_step f ctx PG g9 t9 (EL 10 insns) v2 = (g9,t9) /\
    ptr_safe_step D lo f ctx check_fn PG g7 t7 (EL 8 insns) v0 /\
    ptr_safe_step D lo f ctx check_fn PG g8 t8 (EL 9 insns) v1 /\
    ptr_safe_step D lo f ctx check_fn PG g9 t9 (EL 10 insns) v2 /\
    op_taint t9 (Var z) = {} /\ allocas_from lo v2` by suspend "word_clamp" >>
  suspend "word_after_clamp"
QED

Resume prefix_bool_body_paired[word_clamp]:
  rpt gen_tac >>
  `EL 8 insns = mk_inst (iid+8) SHR [Lit 1w;Var x] [y] /\
   EL 9 insns = mk_inst (iid+9) ISZERO [Var y] [z] /\
   EL 10 insns = mk_inst (iid+10) ASSERT [Var z] []` by simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g8`, Abbr `g9`, Abbr `t8`, Abbr `t9`,
                    Abbr `v1`, Abbr `v2`] >>
  qpat_x_assum `EL 8 insns = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_x_assum `EL 9 insns = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_x_assum `EL 10 insns = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [DRESTRICT_DRESTRICT] >>
  irule (GEN_ALL (SRULE [LET_THM, GSYM ADD_ASSOC]
    (Q.INST [`iid` |-> `iid+8`] prefix_boolword_clamp_steps))) >> simp[]
QED

Resume prefix_bool_body_paired[word_after_clamp]:
  `dp <> x /\ dp <> y /\ dp <> z /\ x <> y /\ x <> z` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var dp) v2 = SOME (n2w (d+32+32*i)) /\
   eval_operand (Var x) v2 = SOME w` by
    simp[Abbr `v2`, Abbr `v1`, Abbr `v0`, prefix_bool_body_eval_update] >>
  `op_taint t9 (Var x) = {}` by
    simp[Abbr `t9`, Abbr `t8`, Abbr `insns`, prefix_guard_taint_other] >>
  `op_taint t9 (Var dp) = {}` by
    simp[Abbr `t9`, Abbr `t8`, Abbr `t7`, Abbr `insns`, prefix_guard_taint_other] >>
  `FLOOKUP g9 dp = SOME (b,sz)` by
    simp[Abbr `g9`, Abbr `g8`, Abbr `g7`, FLOOKUP_DRESTRICT] >>
  suspend "word_store"
QED

Resume prefix_bool_body_paired[word_store]:
  qabbrev_tac `t10 = step_taint (EL 11 insns) v2 v3 t9` >>
  `EL 11 insns = mk_inst (iid+11) MSTORE [Var dp;Var x] []` by simp[Abbr `insns`] >>
  `step_inst_base (EL 11 insns) v2 = OK v3` by
    (qpat_assum `eval_operand (Var dp) v2 = _`
      (mp_then Any mp_tac prefix_mstore_step) >>
     disch_then (qspecl_then [`iid+11`,`Var x`,`w`] mp_tac) >>
     simp[Abbr `v3`]) >>
  `!f check_fn. step_inst f ctx (EL 11 insns) v2 = OK v3 /\
    ptr_safe_step D lo f ctx check_fn PG g9 t9 (EL 11 insns) v2 /\
    ghost_step f ctx PG g9 t9 (EL 11 insns) v2 = (g9,t10)` by
    (rpt gen_tac >> conj_tac
     >- (qpat_assum `EL 11 insns = _` (fn eq =>
           qpat_x_assum `step_inst_base (EL 11 insns) v2 = _`
             (mp_tac o REWRITE_RULE [eq])) >>
         simp[step_inst_non_invoke, mk_inst_def]) >>
     conj_tac
     >- (qpat_x_assum `EL 11 insns = _` (fn th => pure_rewrite_tac [th]) >>
         irule prefix_mstore_ptr_step >> simp[] >> metis_tac[]) >>
     simp[Abbr `t10`] >> irule prefix_mstore_ghost_step >>
     qpat_assum `EL 11 insns = _` (fn eq =>
       qpat_x_assum `step_inst_base (EL 11 insns) v2 = _`
         (mp_tac o REWRITE_RULE [eq])) >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  suspend "word_after_store"
QED

Resume prefix_bool_body_paired[word_after_store]:
  `ip <> iv /\ ip <> sp0 /\ ip <> isrc /\ ip <> sp /\
   ip <> dp0 /\ ip <> idst /\ ip <> dp /\ ip <> x /\ ip <> y /\ ip <> z /\
   iv <> sp0 /\ iv <> isrc /\ iv <> sp /\ iv <> dp0 /\ iv <> idst /\
   iv <> dp /\ iv <> x /\ iv <> y /\ iv <> z /\ ip <> inc /\ iv <> inc` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `!v. eval_operand (Var v) v3 = eval_operand (Var v) v2` by
    simp[Abbr `v3`, mstore_def, eval_operand_def, lookup_var_def] >>
  `eval_operand (Var ip) v3 = SOME (n2w scratch) /\
   eval_operand (Var iv) v3 = SOME (n2w i)` by
    simp[Abbr `v2`, Abbr `v1`, Abbr `v0`,
         Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
         prefix_bool_body_eval_update] >>
  suspend "tail_prepare"
QED

Resume prefix_bool_body_paired[tail_prepare]:
  qpat_assum `!v. v <> dp ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> idst ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> dp0 ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> sp ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> isrc ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> sp0 ==> _` (fn th =>
    map_every (fn v => qspec_then v strip_assume_tac th) [`ip`,`iv`]) >>
  qpat_assum `!v. v <> iv ==> _` (qspec_then `ip` strip_assume_tac) >>
  `op_taint t6 (Var ip) = {} /\ op_taint t6 (Var iv) = {} /\
   FLOOKUP g6 ip = SOME (scratch,32) /\ FLOOKUP g6 iv = NONE` by metis_tac[] >>
  `t10.t_var = t9.t_var` by
    simp[Abbr `t10`, Abbr `insns`, SRULE [LET_THM] prefix_mstore_taint_frame] >>
  `!v. op_taint t10 (Var v) = op_taint t9 (Var v)` by simp[op_taint_def] >>
  `op_taint t10 (Var ip) = {} /\ op_taint t10 (Var iv) = {}` by
    simp[Abbr `t9`, Abbr `t8`, Abbr `t7`, Abbr `insns`, prefix_guard_taint_other] >>
  `FLOOKUP g9 ip = SOME (scratch,32) /\ FLOOKUP g9 iv = NONE` by
    simp[Abbr `g9`, Abbr `g8`, Abbr `g7`, FLOOKUP_DRESTRICT] >>
  suspend "tail_certificate"
QED

Resume prefix_bool_body_paired[tail_certificate]:
  `v3.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo v3` by
    (conj_tac
     >- simp[Abbr `v3`, Abbr `v2`, Abbr `v1`, Abbr `v0`, Abbr `u0`,
             mstore_def, update_var_def] >>
     qpat_assum `!f check_fn. step_inst_base (EL 8 insns) _ = _ /\ _` 
       (qspecl_then [`0`,`fn`] strip_assume_tac) >>
     qpat_x_assum `allocas_from lo v2` mp_tac >>
     simp_tac (srw_ss()) [Abbr `v3`, allocas_from_def, mstore_def, LET_THM]) >>
  qabbrev_tac `g10 = DRESTRICT g9 (COMPL {inc})` >>
  qabbrev_tac `t11 = step_taint (EL 12 insns) v3 v4 t10` >>
  qabbrev_tac `t12 = step_taint (EL 13 insns) v4 v5 t11` >>
  `!check_fn. step_inst_base (EL 12 insns) v3 = OK v4 /\
   step_inst_base (EL 13 insns) v4 = OK v5 /\
   run_inst_seq [EL 12 insns;EL 13 insns] v3 = OK v5 /\
   (!f. ptr_safe_step D lo f ctx check_fn PG g9 t10 (EL 12 insns) v3 /\
        ghost_step f ctx PG g9 t10 (EL 12 insns) v3 = (g10,t11) /\
        ptr_safe_step D lo f ctx check_fn PG g10 t11 (EL 13 insns) v4 /\
        ghost_step f ctx PG g10 t11 (EL 13 insns) v4 = (g10,t12)) /\
   t12.t_mem = t10.t_mem DIFF {p | scratch <= p /\ p < scratch+32} /\
   t12.t_stor = t10.t_stor /\ t12.t_trans = t10.t_trans /\ t12.t_imm = t10.t_imm /\
   (!v. v <> inc ==> op_taint t12 (Var v) = op_taint t10 (Var v) /\
     FLOOKUP g10 v = FLOOKUP g9 v /\
     eval_operand (Var v) v5 = eval_operand (Var v) v3) /\
   op_taint t12 (Var inc) = {} /\ mload scratch v5 = n2w (SUC i)` by
    suspend "tail_apply" >>
  suspend "tail_after_certificate"
QED

Resume prefix_bool_body_paired[tail_apply]:
  gen_tac >>
  `EL 12 insns = mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc] /\
   EL 13 insns = mk_inst (iid+13) MSTORE [Var ip;Var inc] []` by simp[Abbr `insns`] >>
  simp_tac pure_ss [Abbr `g10`, Abbr `t11`, Abbr `t12`, Abbr `v5`, Abbr `v4`] >>
  qpat_x_assum `EL 12 insns = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_x_assum `EL 13 insns = _` (fn th => pure_rewrite_tac [th]) >>
  irule (GEN_ALL (SRULE [LET_THM, GSYM ADD_ASSOC]
    (Q.INST [`iid` |-> `iid+12`] prefix_bool_body_increment_store))) >> simp[] >>
  qexists_tac `ncount` >> simp[]
QED

Resume prefix_bool_body_paired[tail_after_certificate]:
  qpat_assum `!check_fn. step_inst_base (EL 12 insns) _ = _ /\ _`
    (qspec_then `fn` strip_assume_tac) >>
  `v2.vs_memory = s.vs_memory /\ v2.vs_data_section = s.vs_data_section /\
   v2.vs_allocas = s.vs_allocas /\ v2.vs_alloca_next = s.vs_alloca_next /\
   v2.vs_fmp = u6.vs_fmp` by
    simp[Abbr `v2`, Abbr `v1`, Abbr `v0`, Abbr `u0`, update_var_def] >>
  `!p. mload p v2 = mload p s` by simp[mload_def] >>
  `!p. mload p v4 = mload p v3` by simp[Abbr `v4`, mload_def, update_var_def] >>
  `mload d v5 = n2w ncount /\ mload scratch v5 = n2w (SUC i) /\
   (!j. j < SUC i ==> mload (d+32+32*j) v5 = if j=i then w else value j)` by
    suspend "memory_invariant" >>
  suspend "after_memory_invariant"
QED

Resume prefix_bool_body_paired[memory_invariant]:
  `v4.vs_memory = v3.vs_memory` by simp[Abbr `v4`, update_var_def] >>
  `v5.vs_memory = (mstore scratch (n2w (SUC i)) v3).vs_memory` by
    simp[Abbr `v5`, mstore_def] >>
  qpat_assum `v5.vs_memory = _` (fn th => simp_tac (srw_ss()) [mload_def, th]) >>
  pure_rewrite_tac [GSYM mload_def] >>
  qpat_x_assum `Abbrev (v3 = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  mp_tac (Q.INST [`s` |-> `v2`] (SRULE [LET_THM] prefix_bool_body_store_memory)) >>
  simp[]
QED

Resume prefix_bool_body_paired[after_memory_invariant]:
  `t7.t_mem = t6.t_mem /\ t7.t_stor = t6.t_stor /\
   t7.t_trans = t6.t_trans /\ t7.t_imm = t6.t_imm /\
   (!v. v <> x ==> op_taint t7 (Var v) = op_taint t6 (Var v))` by
    (simp_tac pure_ss [Abbr `t7`] >>
     `EL 7 insns = mk_inst (iid+7) DLOAD [Var sp] [x]` by simp[Abbr `insns`] >>
     qpat_x_assum `EL 7 insns = _` (fn th => pure_rewrite_tac [th]) >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >>
     simp[Abbr `v0`, update_var_def]) >>
  `t8.t_mem = t7.t_mem /\ t8.t_stor = t7.t_stor /\
   t8.t_trans = t7.t_trans /\ t8.t_imm = t7.t_imm /\
   (!v. v <> y ==> op_taint t8 (Var v) = op_taint t7 (Var v))` by
    (simp_tac pure_ss [Abbr `t8`] >>
     `EL 8 insns = mk_inst (iid+8) SHR [Lit 1w;Var x] [y]` by simp[Abbr `insns`] >>
     qpat_x_assum `EL 8 insns = _` (fn th => pure_rewrite_tac [th]) >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >>
     simp[Abbr `v1`, update_var_def]) >>
  `t9.t_mem = t8.t_mem /\ t9.t_stor = t8.t_stor /\
   t9.t_trans = t8.t_trans /\ t9.t_imm = t8.t_imm /\
   (!v. v <> z ==> op_taint t9 (Var v) = op_taint t8 (Var v))` by
    (simp_tac pure_ss [Abbr `t9`] >>
     `EL 9 insns = mk_inst (iid+9) ISZERO [Var y] [z]` by simp[Abbr `insns`] >>
     qpat_x_assum `EL 9 insns = _` (fn th => pure_rewrite_tac [th]) >>
     irule (SRULE [LET_THM] prefix_boolword_pure_taint_frame) >>
     simp[NoAsms, Abbr `v2`, update_var_def]) >>
  `t10.t_mem = t9.t_mem DIFF {p | d+32+32*i <= p /\ p < d+32+32*i+32}` by
    suspend "payload_taint" >>
  suspend "taint_invariant"
QED

Resume prefix_bool_body_paired[payload_taint]:
  qpat_assum `eval_operand (Var dp) v2 = _` (mp_then Any mp_tac prefix_mstore_mem_taint) >>
  disch_then drule >>
  simp[Abbr `t10`, Abbr `v3`, w2n_n2w]
QED

Resume prefix_bool_body_paired[taint_invariant]:
  qpat_assum `!f check_fn. step_inst_base (EL 1 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  qpat_assum `!f check_fn. step_inst_base (EL 2 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  qpat_assum `!f check_fn. step_inst_base (EL 3 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  qpat_assum `!f check_fn. step_inst_base (EL 4 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  qpat_assum `!f check_fn. step_inst_base (EL 5 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  qpat_assum `!f check_fn. step_inst_base (EL 6 insns) _ = _ /\ _` (qspecl_then [`0`,`fn`] strip_assume_tac) >>
  `t12.t_mem = (tn.t_mem DIFF {p | d+32+32*i <= p /\ p < d+32+32*i+32})
                    DIFF {p | scratch <= p /\ p < scratch+32}` by simp[] >>
  `(!r. r<32 ==> scratch+r NOTIN t12.t_mem) /\
   (!r. r<32*(SUC i+1) ==> d+r NOTIN t12.t_mem)` by
    (qpat_assum `t12.t_mem = _` (fn th => pure_rewrite_tac [th]) >>
     simp_tac (srw_ss()) [IN_DIFF, GSPECIFICATION] >>
     rpt strip_tac >> Cases_on `r < 32*(i+1)`
     >- (qpat_x_assum `!r. r < 32*(i+1) ==> _` drule >> simp[]) >>
     decide_tac) >>
  suspend "after_taint_invariant"
QED

Resume prefix_bool_body_paired[after_taint_invariant]:
  `t10.t_var = t9.t_var /\ t10.t_stor = t9.t_stor /\
   t10.t_trans = t9.t_trans /\ t10.t_imm = t9.t_imm` by
    (simp_tac pure_ss [Abbr `t10`] >>
     `EL 11 insns = mk_inst (iid+11) MSTORE [Var dp;Var x] []` by simp[Abbr `insns`] >>
     qpat_x_assum `EL 11 insns = _` (fn th => pure_rewrite_tac [th]) >>
     irule (SRULE [LET_THM] prefix_mstore_taint_frame)) >>
  `t12.t_stor = tn.t_stor /\ t12.t_trans = tn.t_trans /\ t12.t_imm = tn.t_imm` by simp[] >>
  suspend "endpoint_frames"
QED

Resume prefix_bool_body_paired[endpoint_frames]:
  `!v. MEM v [ip;src;dst] ==> v <> iv /\ v <> sp0 /\ v <> isrc /\
       v <> sp /\ v <> dp0 /\ v <> idst /\ v <> dp /\
       v <> x /\ v <> y /\ v <> z /\ v <> inc` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `!v. MEM v [ip;src;dst] ==>
      eval_operand (Var v) v5 = eval_operand (Var v) s /\
      FLOOKUP g10 v = FLOOKUP G v /\ op_taint t12 (Var v) = op_taint tn (Var v)` by
    suspend "variable_frames" >>
  suspend "after_variable_frames"
QED

Resume prefix_bool_body_paired[variable_frames]:
  rpt strip_tac >>
  `v <> iv /\ v <> sp0 /\ v <> isrc /\ v <> sp /\ v <> dp0 /\
   v <> idst /\ v <> dp /\ v <> x /\ v <> y /\ v <> z /\ v <> inc` by
    (qpat_x_assum `!v. MEM v [ip;src;dst] ==> v <> iv /\ _` drule >> simp[]) >>
  `eval_operand (Var v) v2 = eval_operand (Var v) u6` by
    simp[Abbr `v2`, Abbr `v1`, Abbr `v0`, prefix_bool_body_eval_update] >>
  `eval_operand (Var v) v3 = eval_operand (Var v) v2` by
    simp[Abbr `v3`, eval_operand_def, lookup_var_def, mstore_def] >>
  `op_taint t10 (Var v) = op_taint t9 (Var v)` by simp[op_taint_def] >>
  simp[Abbr `g9`, Abbr `g8`, Abbr `g7`, FLOOKUP_DRESTRICT]
QED

Resume prefix_bool_body_paired[after_variable_frames]:
  `v5.vs_data_section = s.vs_data_section /\ v5.vs_allocas = s.vs_allocas /\
   v5.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo v5 /\
   v5.vs_halted = s.vs_halted` by
    (simp_tac (srw_ss()) [Abbr `v5`, Abbr `v4`, Abbr `v3`,
       mstore_def, update_var_def, LET_THM, allocas_from_def] >>
     qpat_assum `allocas_from lo s` (assume_tac o SRULE [allocas_from_def]) >>
     simp[Abbr `v2`, Abbr `v1`, Abbr `v0`, Abbr `u0`, update_var_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  `J.vs_memory = v5.vs_memory /\ J.vs_data_section = v5.vs_data_section /\
   J.vs_allocas = v5.vs_allocas /\ J.vs_alloca_next = v5.vs_alloca_next /\
   allocas_from lo J /\ ~J.vs_halted /\ J.vs_current_bb = hdr /\ J.vs_inst_idx = 0` by
    (qpat_assum `allocas_from lo s` (assume_tac o SRULE [allocas_from_def]) >>
     simp[Abbr `J`, jump_to_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  suspend "after_control_frames"
QED

Resume prefix_bool_body_paired[after_control_frames]:
  `!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
      (p+len<=scratch \/ scratch+32<=p) ==>
      mem_bytes_at p len J.vs_memory = mem_bytes_at p len s.vs_memory` by
    suspend "memory_frame" >>
  suspend "trace_assembly"
QED

Resume prefix_bool_body_paired[memory_frame]:
  rpt strip_tac >>
  `mem_bytes_at p len v5.vs_memory = mem_bytes_at p len v4.vs_memory` by
    (simp_tac pure_ss [Abbr `v5`] >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `v4.vs_memory = v3.vs_memory` by simp[Abbr `v4`, update_var_def] >>
  `mem_bytes_at p len v3.vs_memory = mem_bytes_at p len v2.vs_memory` by
    (simp_tac pure_ss [Abbr `v3`] >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[]
QED

Resume prefix_bool_body_paired[trace_assembly]:
  `!f. step_inst f ctx (EL 14 insns) (v5 with vs_inst_idx := k+14) = OK J /\
       ptr_safe_step D lo f ctx fn PG g10 t12 (EL 14 insns)
         (v5 with vs_inst_idx := k+14)` by suspend "jump_certificate" >>
  suspend "trace_lists"
QED

Resume prefix_bool_body_paired[jump_certificate]:
  gen_tac >>
  `EL 14 insns = mk_inst (iid+14) JMP [Label hdr] []` by simp[Abbr `insns`] >>
  qpat_x_assum `EL 14 insns = _` (fn th => pure_rewrite_tac [th]) >>
  `step_inst f ctx (mk_inst (iid+14) JMP [Label hdr] [])
     (v5 with vs_inst_idx := k+14) = OK J` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
         Abbr `J`, jump_to_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       allocas_from_def] >>
  qpat_assum `allocas_from lo s` (assume_tac o SRULE [allocas_from_def]) >>
  simp[op_taint_def, Abbr `J`, jump_to_def] >> first_assum ACCEPT_TAC
QED

Resume prefix_bool_body_paired[trace_lists]:
  qexistsl [`TAKE (N+1) [G;g0;g1;g2;g3;g4;g5;g6;g7;g8;g9;g9;g9;g10;g10]`,
    `TAKE (N+1) [tn;t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t9;t10;t11;t12]`] >>
  conj_tac >- simp[Abbr `N`] >>
  conj_tac >- simp[Abbr `N`] >>
  conj_tac >- simp[Abbr `N`] >>
  conj_tac >- simp[Abbr `N`] >>
  conj_asm1_tac >- suspend "indexed_trace" >>
  suspend "terminal_continuation"
QED

Resume prefix_bool_body_paired[indexed_trace]:
  rpt gen_tac >> strip_tac >>
  `j < 14` by (qpat_x_assum `j < N` mp_tac >> simp[Abbr `N`] >> decide_tac) >>
  `MEM (EL j insns).inst_opcode [MLOAD;ADD;MUL;DLOAD;SHR;ISZERO;ASSERT;MSTORE]` by
    (`EVERY (\inst. MEM inst.inst_opcode [MLOAD;ADD;MUL;DLOAD;SHR;ISZERO;ASSERT;MSTORE])
       (TAKE 14 insns)` by simp[Abbr `insns`, mk_inst_def] >>
     qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `j` mp_tac) >> simp[EL_TAKE, Abbr `insns`]) >>
  `(EL j insns).inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM _.inst_opcode _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >> gvs[]) >>
  `10 < N ==> w2n w < 2` by simp[Abbr `N`] >>
  simp[EL_TAKE] >>
  Cases_on `j = 0`
  >- (simp[Abbr `U`] >>
      qpat_assum `!f. step_inst f ctx (EL 0 insns) _ = _ /\ _`
        (qspec_then `f` (ACCEPT_TAC o SRULE []))) >>
  `j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7 \/
   j=8 \/ j=9 \/ j=10 \/ j=11 \/ j=12 \/ j=13` by
    (qpat_x_assum `j < 14` mp_tac >> qpat_x_assum `j <> 0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >> simp_tac (srw_ss()) [Abbr `U`] >>
  irule prefix_bool_success_idx >>
  (conj_tac >- simp[Abbr `insns`, mk_inst_def])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 1 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 2 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 3 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 4 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 5 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst_base (EL 6 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!f check_fn. step_inst f ctx (EL 7 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `MEM _.inst_opcode _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  simp[step_inst_non_invoke]
QED

Resume prefix_bool_body_paired[terminal_continuation]:
  conj_asm1_tac >- suspend "terminal_facts" >>
  suspend "continuation"
QED

Resume prefix_bool_body_paired[terminal_facts]:
  Cases_on `w2n w < 2`
  >- (qpat_assum `w2n w < 2` (fn th =>
        simp_tac (srw_ss()) [th, Abbr `N`, Abbr `U`]) >>
      `!p. mload p J = mload p v5` by simp[Abbr `J`, jump_to_def, mload_def] >>
      `!v. eval_operand (Var v) J = eval_operand (Var v) v5` by
        simp[Abbr `J`, jump_to_def, eval_operand_def, lookup_var_def] >>
      qpat_assum `!f. step_inst f ctx (EL 14 insns) _ = _ /\ _` mp_tac >>
      qpat_assum `mload d v5 = _` mp_tac >>
      qpat_assum `mload scratch v5 = _` mp_tac >>
      qpat_assum `!j. j < SUC i ==> mload _ v5 = _` mp_tac >>
      qpat_assum `!r. r < 32 ==> scratch+r NOTIN t12.t_mem` mp_tac >>
      qpat_assum `!r. r < 32*(SUC i+1) ==> _` mp_tac >>
      qpat_assum `!v. MEM v [ip;src;dst] ==> eval_operand _ v5 = _ /\ _` mp_tac >>
      qpat_assum `v5.vs_data_section = _` mp_tac >>
      qpat_assum `v5.vs_allocas = _` mp_tac >>
      qpat_assum `v5.vs_alloca_next = _` mp_tac >>
      qpat_assum `J.vs_data_section = v5.vs_data_section` mp_tac >>
      qpat_assum `J.vs_allocas = v5.vs_allocas` mp_tac >>
      qpat_assum `J.vs_alloca_next = v5.vs_alloca_next` mp_tac >>
      qpat_assum `allocas_from lo J` mp_tac >>
      qpat_assum `~J.vs_halted` mp_tac >>
      qpat_assum `J.vs_current_bb = hdr` mp_tac >>
      qpat_assum `J.vs_inst_idx = 0` mp_tac >>
      qpat_assum `t12.t_stor = tn.t_stor` mp_tac >>
      qpat_assum `t12.t_trans = tn.t_trans` mp_tac >>
      qpat_assum `t12.t_imm = tn.t_imm` mp_tac >>
      qpat_assum `!p len. _ ==> mem_bytes_at p len J.vs_memory = _` mp_tac >>
      qpat_assum `!p. mload p J = _` mp_tac >>
      qpat_assum `!v. eval_operand (Var v) J = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  simp[Abbr `N`, Abbr `U`] >>
  `EL 10 insns = mk_inst (iid+10) ASSERT [Var z] []` by simp[Abbr `insns`] >>
  `eval_operand (Var z) (v2 with vs_inst_idx := k+10) = SOME (0w:bytes32)` by
    (simp[Abbr `v2`, prefix_bool_body_eval_update, eval_op_inst_idx,
          bool_to_word_def, prefix_bool_shr_guard]) >>
  gen_tac >> conj_tac
  >- (qpat_assum `EL 10 insns = _` (fn th => pure_rewrite_tac [th]) >>
      irule prefix_assert_ptr_step >> simp[allocas_from_def] >>
      qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  simp[step_inst_non_invoke] >>
  qpat_assum `eval_operand (Var z) (_ with vs_inst_idx := _) = SOME 0w`
    (mp_then Any (qspec_then `iid+10` mp_tac) prefix_assert_step) >> simp[]
QED

Resume prefix_bool_body_paired[continuation]:
  `!j. j < N ==> step_inst_base (EL j insns) (EL j U) = OK (EL (SUC j) U)`
    by suspend "raw_trace" >>
  suspend "block_continuation"
QED

Resume prefix_bool_body_paired[raw_trace]:
  rpt strip_tac >>
  `j < 14` by (qpat_x_assum `j < N` mp_tac >> simp[Abbr `N`] >> decide_tac) >>
  `10 < N ==> w2n w < 2` by simp[Abbr `N`] >>
  `j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7 \/
   j=8 \/ j=9 \/ j=10 \/ j=11 \/ j=12 \/ j=13` by
    (qpat_x_assum `j < 14` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >> simp_tac (srw_ss()) [Abbr `U`]
  >- (`scratch < dimword(:256)` by
        (qpat_x_assum `scratch+32 <= _` mp_tac >>
         qpat_x_assum `s.vs_alloca_next < _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
      simp_tac (srw_ss()) [Abbr `insns`, Abbr `u0`] >>
      qpat_assum `eval_operand (Var ip) s = _`
        (mp_then Any mp_tac prefix_mload_step) >> simp[]) >>
  simp[step_inst_non_invoke]
QED

Resume prefix_bool_body_paired[block_continuation]:
  qabbrev_tac `gs = TAKE (N+1) [G;g0;g1;g2;g3;g4;g5;g6;g7;g8;g9;g9;g9;g10;g10]` >>
  qabbrev_tac `ts = TAKE (N+1) [tn;t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t9;t10;t11;t12]` >>
  rpt strip_tac >>
  `run_inst_seq (TAKE N insns) s = OK (EL N U) /\
   (ptr_safe_block D lo f ctx fn PG (EL N gs) (EL N ts) bb
      ((EL N U) with vs_inst_idx := k+N) ==>
    ptr_safe_block D lo f ctx fn PG G tn bb s)` by suspend "trace_apply" >>
  suspend "terminal_block"
QED

Resume prefix_bool_body_paired[trace_apply]:
  `LENGTH (TAKE N insns) = N` by simp[Abbr `insns`, Abbr `N`] >>
  simp_tac pure_ss [Abbr `k`] >>
  qpat_assum `LENGTH (TAKE N insns) = N` (fn th =>
    irule (GEN_ALL (SRULE [th] (Q.INST
      [`u` |-> `\j. EL j U`, `g` |-> `\j. EL j gs`, `q` |-> `\j. EL j ts`]
      (SPEC_ALL (Q.SPEC `TAKE N insns` prefix_trace_ptr_safe_block)))))) >>
  conj_tac
  >- (rpt strip_tac >> simp[EL_TAKE] >>
      qpat_assum `!j. j < N ==> step_inst_base _ _ = _` (qspec_then `j` mp_tac) >>
      qpat_assum `!j f. j < N ==> _` (qspecl_then [`j`,`f`] mp_tac) >>
      qpat_assum `j < N` mp_tac >>
      simp_tac pure_ss [Abbr `gs`, Abbr `ts`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[EL_TAKE, GSYM ADD1] >>
      rpt strip_tac >> metis_tac[]) >>
  conj_tac >- simp[Abbr `gs`, Abbr `N`] >>
  conj_tac >- simp[Abbr `ts`, Abbr `N`] >>
  conj_tac >- simp[Abbr `U`] >>
  conj_tac >- (Cases_on `w2n w < 2` >>
    simp[Abbr `N`, Abbr `insns`, mk_inst_def, is_terminator_def]) >>
  `isPREFIX (TAKE N insns) insns` by
    (Cases_on `w2n w < 2` >> simp[Abbr `N`, Abbr `insns`]) >>
  qpat_x_assum `isPREFIX insns _` mp_tac >>
  qpat_x_assum `isPREFIX (TAKE N insns) insns` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[isPREFIX_TRANS]
QED

Resume prefix_bool_body_paired[terminal_block]:
  qpat_x_assum `ptr_safe_block D lo f ctx fn PG (EL N gs) _ _ _ ==> _` irule >>
  `get_instruction bb (k+N) = SOME (EL N insns)` by
    (qpat_assum `isPREFIX insns _` mp_tac >>
     `N < LENGTH insns` by simp[Abbr `N`, Abbr `insns`] >>
     qpat_x_assum `N < LENGTH insns` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[prefix_drop_equiv] >> rpt strip_tac >>
     qpat_assum `DROP k bb.bb_instructions = _` (assume_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     `k+N < LENGTH bb.bb_instructions` by gvs[LENGTH_DROP] >>
     simp[get_instruction_def] >>
     qspecl_then [`N`,`k`,`bb.bb_instructions`] mp_tac EL_DROP >>
     qpat_assum `DROP k bb.bb_instructions = _`
       (fn th => pure_once_rewrite_tac [th]) >>
     simp[EL_APPEND_EQN]) >>
  qpat_assum `if w2n w < 2 then _ else _` mp_tac >>
  qpat_assum `w2n w < 2 ==> !f. ptr_safe_blocks _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `get_instruction bb (k+N) = _` mp_tac >>
  simp_tac pure_ss [Abbr `gs`, Abbr `ts`, Abbr `N`, Abbr `U`] >>
  qpat_x_assum `Abbrev (insns = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  Cases_on `w2n w < 2` >> simp[] >> rpt strip_tac >>
  simp[Once ptr_safe_block_def] >> simp[is_terminator_def]
QED

Finalise prefix_bool_body_paired

val _ = export_theory();
