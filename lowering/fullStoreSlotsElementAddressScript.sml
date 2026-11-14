(* Arithmetic boundaries with explicit, uniform endpoints. *)
Theory fullStoreSlotsElementAddress
Ancestors
  fullStoreSlotsMembers typedCopyOriginPtrBase typedMemoryCopy stateFrame
  fragGasOriginPtr ptrDiscipline context emitHelper exprLoweringProps
  compileEnv loweringStateRelDefs venomState venomInst venomExecSemantics
  fragExec contextCodegenRel finite_map pred_set words list arithmetic

Theorem store_slots_binop_fixed_origin_ptr:
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
       (update_var out w s),
     step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
       (update_var out w s) tn)
Proof
  metis_tac[typed_copy_origin_ptr_binop_path, operand_11]
QED

Theorem store_slots_binop_uniform_path:
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !D explicit PG.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov ARB G (mk_inst sa.cs_next_id opc [left;right] [out])
       (update_var out w s),
     step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
       (update_var out w s) tn)
Proof
  rpt strip_tac >>
  `step_prov ARB G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s) =
   step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s)` by
    gvs[step_prov_def, out_prov_def, mk_inst_def] >>
  pure_once_asm_rewrite_tac[] >>
  metis_tac[store_slots_binop_fixed_origin_ptr]
QED

Theorem store_slots_binop_frame:
  emit_op opc [left;right] sa = (Var out,sb) /\
  (opc = MUL \/ opc = ADD) /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  execution_frame
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) = execution_frame s /\
  op_taint (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn) (Var out) = {} /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (!p. not_fresh_at sa p ==>
    lookup_var p (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
    FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn) (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> (
  `~not_fresh_at sa out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >> decide_tac) >>
  conj_tac >- simp[execution_frame_def, update_var_def] >>
  rpt conj_tac
  >- metis_tac[typed_copy_origin_ptr_binop_ghost_frame]
  >- metis_tac[typed_copy_origin_ptr_binop_ghost_frame]
  >- metis_tac[typed_copy_origin_ptr_binop_ghost_frame]
  >- metis_tac[typed_copy_origin_ptr_binop_ghost_frame]
  >- metis_tac[typed_copy_origin_ptr_binop_ghost_frame] >>
  gen_tac >> disch_tac >> `p <> out` by metis_tac[] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[typed_copy_origin_ptr_binop_ghost_frame])
QED

Theorem store_slots_binop_run:
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gu tu.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    u = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gu = step_prov ARB G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s) /\
    tu = step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn /\
    execution_frame u = execution_frame s /\
    lookup_var out u = SOME w /\ op_taint tu (Var out) = {} /\
    tu.t_mem = tn.t_mem /\ tu.t_imm = tn.t_imm /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\
    allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
      op_taint tu (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> (
  qexistsl_tac [`update_var out w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov ARB G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s)`,
    `step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn`] >>
  conj_tac >- metis_tac[store_slots_binop_uniform_path] >>
  pure_rewrite_tac [REFL_CLAUSE, AND_CLAUSES] >>
  drule store_slots_binop_frame >> disch_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  gvs[same_blocks_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      allocas_from_def] >> metis_tac[])
QED

Theorem store_slots_scaled_address_run:
  emit_op MUL [Var cv;Lit (n2w scale)] sa = (Var ov,sb) /\
  emit_op ADD [bop;Var ov] sb = (Var out,sc) /\
  fn_has_code sa sc func /\ not_fresh_at sa cv /\
  (!p. bop = Var p ==> not_fresh_at sa p) /\
  lookup_var cv s = SOME (n2w j) /\ eval_operand bop s = SOME a /\
  op_taint tn (Var cv) = {} /\ op_taint tn bop = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gu tu.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    lookup_var out u = SOME (a + n2w (j*scale)) /\
    op_taint tu (Var out) = {} /\
    (op_prov G bop = NONE ==> FLOOKUP Gu out = NONE) /\
    (!root span len. bop = Var root /\ ptr_covers G tn root s span /\
      j*scale + len <= span /\
      w2n a + j*scale < dimword(:256) ==> ptr_covers Gu tu out u len) /\
    execution_frame u = execution_frame s /\
    tu.t_mem = tn.t_mem /\ tu.t_imm = tn.t_imm /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\
    allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    not_fresh_at sc out /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
      op_taint tu (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sc func` by
    metis_tac[fn_has_code_split] >>
  `eval_operand (Var cv) s = SOME (n2w j) /\
   eval_operand (Lit (n2w scale)) s = SOME (n2w scale) /\
   op_taint tn (Lit (n2w scale)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all (store_slots_binop_run |> Q.INST
    [`opc` |-> `MUL`, `w` |-> `n2w (j*scale)`,
     `x` |-> `n2w j`, `y` |-> `n2w scale`] |> SIMP_RULE pure_ss
       [word_mul_n2w,REFL_CLAUSE,AND_CLAUSES,OR_CLAUSES]) >>
  disch_then (qspec_then `G` (qx_choose_then `q` (qx_choose_then `Gq`
    (qx_choose_then `tq` strip_assume_tac)))) >>
  `eval_operand bop q = SOME a /\
   eval_operand (Var ov) q = SOME (n2w (j*scale)) /\
   op_taint tq bop = {}` by
    (Cases_on `bop` >> gvs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  drule_all (store_slots_binop_run |> Q.INST
    [`opc` |-> `ADD`, `w` |-> `x+y`] |> SIMP_RULE pure_ss
      [REFL_CLAUSE,AND_CLAUSES,OR_CLAUSES]) >>
  disch_then (qspec_then `Gq` (qx_choose_then `u` (qx_choose_then `Gu`
    (qx_choose_then `tu` strip_assume_tac)))) >>
  suspend "finish"
QED

Resume store_slots_scaled_address_run[finish]:
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (gvs[not_fresh_at_def, ci_mono_def] >>
     metis_tac[typed_copy_emit_op_mono, ci_mono_def, LESS_EQ_TRANS]) >>
  `not_fresh_at sc out` by metis_tac[typed_copy_emit_op_fresh] >>
  `!root. bop = Var root ==> root <> out` by
    (rpt strip_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
     metis_tac[not_fresh_at_def, LESS_EQ_REFL]) >>
  `!root span. bop = Var root ==>
    (ptr_covers Gq tq root q span <=> ptr_covers G tn root s span)` by
    (simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "posts"
QED

Resume store_slots_scaled_address_run[posts]:
  conj_tac
  >- (strip_tac >>
      `op_prov Gq bop = NONE /\ FLOOKUP Gq ov = NONE` by
        (conj_tac
         >- (Cases_on `bop` >> gvs[op_prov_def] >> metis_tac[]) >>
         simp[typed_copy_origin_ptr_binop_ghost_frame]) >>
      simp[IgnAsm `Gq = _`, step_prov_def, out_prov_def, first_prov_def,
           op_prov_def, set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_covers Gq tq root q span` by metis_tac[] >>
      `ptr_covers Gu tu out (update_var out (a+n2w (j*scale)) q) len` by
        (qpat_x_assum `Gu = _` SUBST1_TAC >>
         qpat_x_assum `tu = _` SUBST1_TAC >>
         qpat_assum `bop = Var root` SUBST1_TAC >>
         irule typed_copy_origin_ptr_offset_covers >>
         simp[eval_operand_def] >> metis_tac[ADD_COMM,eval_operand_def]) >>
      gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def]) >>
  metis_tac[]
QED

Finalise store_slots_scaled_address_run

Theorem store_slots_element_addresses_origin_ptr:
  emit_op MUL [Var cv;Lit (n2w ms)] sa = (Var so,sb) /\
  emit_op ADD [Var xs;Var so] sb = (Var sp,sc) /\
  emit_op MUL [Var cv;Lit (n2w slots)] sc = (Var off,sd) /\
  emit_op ADD [dst;Var off] sd = (Var dp,se) /\
  not_fresh_at sa cv /\ not_fresh_at sa xs /\
  (!p. dst = Var p ==> not_fresh_at sa p) /\
  lookup_var cv s = SOME (n2w j) /\ lookup_var xs s = SOME sw /\
  eval_operand dst s = SOME dw /\ op_prov G dst = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn dst = {} /\
  ptr_covers G tn xs s (n*ms) /\ j < n /\
  w2n sw + n*ms < dimword(:256) /\
  w2n dw + n*slots <= dimword(:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ fn_has_code sa se func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gu tu.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    lookup_var sp u = SOME (n2w (w2n sw+j*ms)) /\
    lookup_var dp u = SOME (n2w (w2n dw+j*slots)) /\
    ptr_covers Gu tu sp u ms /\ FLOOKUP Gu dp = NONE /\
    op_taint tu (Var dp) = {} /\ sp <> dp /\
    not_fresh_at se sp /\ not_fresh_at se dp /\
    execution_frame u = execution_frame s /\
    tu.t_mem = tn.t_mem /\ tu.t_imm = tn.t_imm /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\
    allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = se.cs_current_bb /\
    u.vs_inst_idx = LENGTH se.cs_current_insts /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
      op_taint tu (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\
   cs_extends sd se` by metis_tac[typed_copy_emit_op_mono,ci_mono_def] >>
  `cs_extends sa sc /\ cs_extends sc se` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc func /\ fn_has_code sc se func` by
    metis_tac[fn_has_code_split] >>
  `eval_operand (Var xs) s = SOME sw /\ op_taint tn (Var xs) = {} /\
   (!p. Var xs = Var p ==> not_fresh_at sa p)` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def,eval_operand_def]) >>
  drule_all (store_slots_scaled_address_run |> Q.INST [`sa` |-> `sa`]) >>
  disch_then (qspec_then `G` (qx_choose_then `q` (qx_choose_then `Gq`
    (qx_choose_then `tq` strip_assume_tac)))) >>
  suspend "destination"
QED

Resume store_slots_element_addresses_origin_ptr[destination]:
  `!p. not_fresh_at sa p ==> not_fresh_at sc p` by
    (gvs[not_fresh_at_def] >>
     metis_tac[typed_copy_emit_op_mono,ci_mono_def,LESS_EQ_TRANS]) >>
  `not_fresh_at sc cv /\ (!p. dst = Var p ==> not_fresh_at sc p) /\
   lookup_var cv q = SOME (n2w j) /\ eval_operand dst q = SOME dw /\
   op_prov Gq dst = NONE /\ op_taint tq dst = {} /\
   op_taint tq (Var cv) = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def,op_prov_def,op_taint_def] >>
     metis_tac[]) >>
  drule_all (store_slots_scaled_address_run |> Q.INST
    [`sa` |-> `sc`, `sb` |-> `sd`, `sc` |-> `se`]) >>
  disch_then (qspec_then `Gq` (qx_choose_then `u` (qx_choose_then `Gu`
    (qx_choose_then `tu` strip_assume_tac)))) >>
  suspend "posts"
QED

Resume store_slots_element_addresses_origin_ptr[posts]:
  `j*ms+ms <= n*ms` by
    (`j+1 <= n` by decide_tac >>
     qspecl_then [`j+1`,`n`,`ms`] mp_tac arithmeticTheory.LESS_MONO_MULT >>
     asm_rewrite_tac[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,MULT_CLAUSES]) >>
  `w2n sw+j*ms < dimword(:256)` by decide_tac >>
  `not_fresh_at sc sp` by metis_tac[typed_copy_emit_op_fresh] >>
  `ptr_covers Gq tq sp q ms` by metis_tac[] >>
  `ptr_covers Gu tu sp u ms` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `sc.cs_next_var <= sd.cs_next_var /\
   sd.cs_next_var <= se.cs_next_var` by
    metis_tac[typed_copy_emit_op_mono,ci_mono_def] >>
  `not_fresh_at sd sp /\ not_fresh_at se sp` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS] >>
  `sp <> dp` by
    (qpat_x_assum `emit_op ADD [dst;Var off] sd = _` mp_tac >>
     simp[emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
          fresh_var_def,fresh_id_def,emit_def] >> strip_tac >>
     gvs[not_fresh_at_def] >>
     metis_tac[typed_copy_emit_op_mono,ci_mono_def,LESS_EQ_TRANS]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append,APPEND_NIL] >>
  simp[GSYM word_add_n2w] >> gvs[]
QED

Finalise store_slots_element_addresses_origin_ptr
