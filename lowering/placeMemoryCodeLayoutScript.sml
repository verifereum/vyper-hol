Theory placeMemoryCodeLayout
Ancestors
  fragExec exprLoweringProps compileEnv exprLowering emitHelper
  venomInst venomState list rich_list pair freshWrites ASCIInumbers arithmetic

(* Exact finished-block lookup, independent of runtime loop invariants. *)
Theorem fn_has_code_finished_mid:
  !start a b finish lbl x func.
  cs_extends start a /\ cs_extends a b /\ cs_extends b finish /\
  new_block lbl a = (x,b) /\ fn_has_code start finish func ==>
  lookup_block a.cs_current_bb func.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
           bb_instructions := a.cs_current_insts|>
Proof
  rpt strip_tac >>
  `fn_has_code a b func` by metis_tac[fn_has_code_mid] >>
  metis_tac[fn_has_code_new_block]
QED

(* The slow array loop, including recursive copies which may finish further
   blocks. The exit block is deliberately exposed only as a prefix. *)
Theorem typed_copy_dynarray_slow_code_lookup:
  !sa hdr l1 blabel l2 exit l3 counter init st0 st1 u1 sth
   length lt h1 done stj st2 u2 stb src so b1 doff b2 dst sp b3 dp b4
   cenv dty sty b5 inc b6 ste st3 u3 stx func cond_name body_name exit_name.
  fresh_label cond_name sa = (hdr,l1) /\
  fresh_label body_name l1 = (blabel,l2) /\
  fresh_label exit_name l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv sty))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dty))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\ fn_has_code sa stx func ==>
  fn_has_code stb b4 func /\ fn_has_code b4 b5 func /\
  sa.cs_next_var <= stb.cs_next_var /\
  lookup_block st1.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts|> /\
  lookup_block st2.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st2.cs_current_bb; bb_instructions := st2.cs_current_insts|> /\
  lookup_block st3.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st3.cs_current_bb; bb_instructions := st3.cs_current_insts|> /\
  ?bb. lookup_block stx.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX stx.cs_current_insts bb.bb_instructions
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa l1 /\ ci_mono l1 l2 /\ ci_mono l2 l3 /\ ci_mono l3 init` by
    metis_tac[ci_mono_fresh_label, ci_mono_fresh_var, SND] >>
  `ci_mono init st0 /\ ci_mono st0 st1 /\ ci_mono stj st2 /\
   ci_mono b6 ste /\ ci_mono ste st3` by
    metis_tac[ci_mono_emit_inst, SND] >>
  `ci_mono st1 sth /\ ci_mono st2 stb /\ ci_mono st3 stx` by
    metis_tac[ci_mono_new_block, SND] >>
  `ci_mono sth h1 /\ ci_mono h1 stj /\ ci_mono stb b1 /\
   ci_mono b1 b2 /\ ci_mono b2 b3 /\ ci_mono b3 b4 /\ ci_mono b5 b6` by
    metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono b4 b5` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  fs[ci_mono_def] >>
  `sa.cs_next_var <= stb.cs_next_var` by decide_tac >>
  conj_tac >- suspend "body_code" >>
  conj_tac >- suspend "child_code" >>
  rpt (qpat_x_assum `_ <= _` kall_tac) >>
  `cs_extends sa st1` by metis_tac[cs_extends_trans] >>
  `cs_extends sth st2` by metis_tac[cs_extends_trans] >>
  `cs_extends stb b4` by metis_tac[cs_extends_trans] >>
  `cs_extends b4 st3` by metis_tac[cs_extends_trans] >>
  `cs_extends stb st3` by metis_tac[cs_extends_trans] >>
  `cs_extends stb stx /\ cs_extends st2 stx /\ cs_extends sth stx /\ cs_extends sa st2 /\
   cs_extends sa st3` by metis_tac[cs_extends_trans] >>
  rpt conj_tac
  >- metis_tac[fn_has_code_finished_mid]
  >- metis_tac[fn_has_code_finished_mid]
  >- metis_tac[fn_has_code_finished_mid, cs_extends_refl] >>
  irule fn_has_code_start >> qexists_tac `stx` >>
  simp[cs_extends_refl] >>
  metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
QED

Resume typed_copy_dynarray_slow_code_lookup[body_code]:
  rpt (qpat_x_assum `_ <= _` kall_tac) >>
  metis_tac[fn_has_code_mid, cs_extends_trans]
QED

Resume typed_copy_dynarray_slow_code_lookup[child_code]:
  rpt (qpat_x_assum `_ <= _` kall_tac) >>
  metis_tac[fn_has_code_mid, cs_extends_trans]
QED

Finalise typed_copy_dynarray_slow_code_lookup

(* Scalar observations avoid substituting chains of entire compiler records. *)
Theorem fresh_label_next_var:
  fresh_label name sa = (label,sb) ==> sb.cs_next_var = sa.cs_next_var
Proof
  simp[fresh_label_def] >> strip_tac >> gvs[]
QED

Theorem fresh_var_next_var:
  fresh_var sa = (v,sb) ==>
  v = STRCAT "%" (toString sa.cs_next_var) /\
  sb.cs_next_var = sa.cs_next_var + 1
Proof
  simp[fresh_var_def] >> strip_tac >> gvs[]
QED

Theorem emit_inst_next_var:
  emit_inst opc args outs sa = ((),sb) ==> sb.cs_next_var = sa.cs_next_var
Proof
  simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]
QED

Theorem emit_op_next_var:
  emit_op opc args sa = (v,sb) ==>
  v = Var (STRCAT "%" (toString sa.cs_next_var)) /\
  sb.cs_next_var = sa.cs_next_var + 1
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]
QED

Theorem new_block_next_var:
  new_block label sa = (old,sb) ==> sb.cs_next_var = sa.cs_next_var
Proof
  simp[new_block_def, LET_THM] >> strip_tac >> gvs[]
QED

Theorem typed_copy_slow_array_control_layout:
  fresh_label cond_name sa = (hdr,l1) /\
  fresh_label body_name l1 = (blabel,l2) /\
  fresh_label exit_name l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv sty))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dty))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\ fn_has_code sa stx func ==>
  ?lvar dvar ivar ibb hbb ebb id1 id2 hid1 hid2 hid3 eid1 eid2 eid3.
  lt = Var lvar /\ done = Var dvar /\ inc = Var ivar /\
  lookup_block sa.cs_current_bb func.fn_blocks = SOME ibb /\
  DROP (LENGTH sa.cs_current_insts) ibb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst hid1 LT [Var counter; length] [lvar];
     mk_inst hid2 ISZERO [Var lvar] [dvar];
     mk_inst hid3 JNZ [Var dvar; Label exit; Label blabel] []] /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME ebb /\
  DROP (LENGTH b5.cs_current_insts) ebb.bb_instructions =
    [mk_inst eid1 ADD [Var counter; Lit 1w] [ivar];
     mk_inst eid2 ASSIGN [Var ivar] [counter]; mk_inst eid3 JMP [Label hdr] []] /\
  sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
  stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
  stx.cs_current_bb = exit /\ stx.cs_current_insts = [] /\
  fn_has_code stb b4 func /\ fn_has_code b4 b5 func /\
  sa.cs_next_var <= stb.cs_next_var /\
  counter <> lvar /\ counter <> dvar /\ not_fresh_at stb counter /\
  (!x. not_fresh_at sa x ==> x <> lvar /\ x <> dvar /\
       not_fresh_at stb x /\ x <> ivar /\ x <> counter)
Proof
  strip_tac >>
  `?lvar. lt = Var lvar /\ lvar = STRCAT "%" (toString sth.cs_next_var)` by
    metis_tac[emit_op_next_var] >>
  `?dvar. done = Var dvar /\ dvar = STRCAT "%" (toString h1.cs_next_var)` by
    metis_tac[emit_op_next_var] >>
  `?ivar. inc = Var ivar /\ ivar = STRCAT "%" (toString b5.cs_next_var)` by
    metis_tac[emit_op_next_var] >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  `sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
   stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
   stx.cs_current_bb = exit /\ stx.cs_current_insts = []` by suspend "endpoints" >>
  `?id1 id2. st1.cs_current_bb = sa.cs_current_bb /\
   st1.cs_current_insts = sa.cs_current_insts ++
     [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []]`
    by suspend "init" >>
  `?hid1 hid2 hid3. st2.cs_current_bb = hdr /\ st2.cs_current_insts =
     [mk_inst hid1 LT [Var counter; length] [lvar];
      mk_inst hid2 ISZERO [Var lvar] [dvar];
      mk_inst hid3 JNZ [Var dvar; Label exit; Label blabel] []]`
    by suspend "condition" >>
  `?eid1 eid2 eid3. st3.cs_current_bb = b5.cs_current_bb /\
   st3.cs_current_insts = b5.cs_current_insts ++
     [mk_inst eid1 ADD [Var counter; Lit 1w] [ivar];
      mk_inst eid2 ASSIGN [Var ivar] [counter]; mk_inst eid3 JMP [Label hdr] []]`
    by suspend "backedge" >>
  `counter <> lvar /\ counter <> dvar /\ not_fresh_at stb counter /\
   (!x. not_fresh_at sa x ==> x <> lvar /\ x <> dvar /\
      not_fresh_at stb x /\ x <> ivar /\ x <> counter)` by suspend "fresh" >>
  qexistsl_tac [`lvar`, `dvar`, `ivar`,
    `<|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts|>`,
    `<|bb_label := st2.cs_current_bb; bb_instructions := st2.cs_current_insts|>`,
    `<|bb_label := st3.cs_current_bb; bb_instructions := st3.cs_current_insts|>`,
    `id1`, `id2`, `hid1`, `hid2`, `hid3`, `eid1`, `eid2`, `eid3`] >>
  gvs[DROP_APPEND]
QED

Resume typed_copy_slow_array_control_layout[endpoints]:
  map_every (fn q => qpat_assum q mp_tac)
    [`new_block hdr _ = _`, `new_block blabel _ = _`, `new_block exit _ = _`] >>
  rpt (first_x_assum kall_tac) >>
  simp[new_block_def, LET_THM] >> rpt strip_tac >> gvs[]
QED

Resume typed_copy_slow_array_control_layout[init]:
  map_every (fn q => qpat_assum q mp_tac)
    [`fresh_label cond_name _ = _`, `fresh_label body_name _ = _`,
     `fresh_label exit_name _ = _`, `fresh_var l3 = _`,
     `emit_inst ASSIGN _ _ init = _`, `emit_inst JMP _ _ st0 = _`] >>
  rpt (first_x_assum kall_tac) >>
  simp[fresh_label_def, fresh_var_def, fresh_id_def, emit_inst_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id + 1`] >> simp[]
QED

Resume typed_copy_slow_array_control_layout[condition]:
  map_every (fn q => qpat_assum q mp_tac)
    [`emit_op LT _ sth = _`, `emit_op ISZERO _ h1 = _`,
     `emit_inst JNZ _ _ stj = _`, `sth.cs_current_bb = hdr`,
     `sth.cs_current_insts = []`, `lt = Var lvar`, `done = Var dvar`] >>
  rpt (first_x_assum kall_tac) >>
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_inst_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`sth.cs_next_id`, `sth.cs_next_id + 1`, `sth.cs_next_id + 2`] >> simp[]
QED

Resume typed_copy_slow_array_control_layout[backedge]:
  map_every (fn q => qpat_assum q mp_tac)
    [`emit_op ADD _ b5 = _`, `emit_inst ASSIGN _ _ b6 = _`,
     `emit_inst JMP _ _ ste = _`, `inc = Var ivar`] >>
  rpt (first_x_assum kall_tac) >>
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_inst_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`b5.cs_next_id`, `b5.cs_next_id + 1`, `b5.cs_next_id + 2`] >> simp[]
QED

Resume typed_copy_slow_array_control_layout[fresh]:
  imp_res_tac fresh_label_next_var >>
  imp_res_tac fresh_var_next_var >>
  imp_res_tac emit_inst_next_var >>
  imp_res_tac emit_op_next_var >>
  imp_res_tac new_block_next_var >>
  `ci_mono b4 b5` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  `b4.cs_next_var <= b5.cs_next_var` by fs[ci_mono_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `ci_mono b4 b5` kall_tac >>
  gvs[not_fresh_at_def, toString_inj] >>
  rpt strip_tac >> gvs[toString_inj] >> decide_tac
QED

Finalise typed_copy_slow_array_control_layout
