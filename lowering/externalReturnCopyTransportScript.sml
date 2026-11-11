(* Task-owned transport interfaces; no recursive copy execution here. *)
Theory externalReturnCopyTransport
Ancestors
  externalReturnCopyFrame exprLoweringProps venomState compileEnv loweringStateRelDefs
  loweringPosts valueEncoding valueEncodingDefs valueEncodingProps arithmetic
  fragExec emitHelper emitHelperProps context venomExecSemantics venomInst words finite_map

Theorem return_copy_frame_mono:
  ci_mono sa sb /\ return_copy_frame sb off len s t ==>
  return_copy_frame sa off len s t
Proof
  rw[ci_mono_def, return_copy_frame_def] >>
  first_x_assum irule >>
  gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem return_copy_frame_operand:
  return_copy_frame sa dst len s t /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op t = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, return_copy_frame_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality]
QED

Theorem return_copy_frame_jump:
  return_copy_frame sa off len s t ==>
  return_copy_frame sa off len s (jump_to l t)
Proof
  simp[return_copy_frame_def, jump_to_def, lookup_var_def]
QED

Theorem return_copy_operand_jump[simp]:
  eval_operand op (jump_to l t) = eval_operand op t
Proof
  Cases_on `op` >> simp[eval_operand_def, jump_to_def, lookup_var_def]
QED

Theorem return_footprint_le_layout:
  val_wf tv v ==> val_footprint tv v <= type_memory_size tv
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[val_wf_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[val_wf_def] >> decide_tac
QED

Theorem return_copy_array_child_window:
  (i:num) < n ==> off <= off + i * stride /\
    off + i * stride + stride <= off + n * stride
Proof
  strip_tac >> simp[] >>
  `SUC i <= n` by decide_tac >>
  qpat_x_assum `SUC i <= n` mp_tac >>
  disch_then (mp_tac o Q.SPEC `stride` o MATCH_MP LESS_MONO_MULT) >>
  pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED

Theorem return_copy_offset_mono:
  compile_with_byte_offset baseop off sa = (op,sb) ==> ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa (SND (compile_with_byte_offset baseop off sa))` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` kall_tac >>
     rw[compile_with_byte_offset_def] >>
     simp[ci_mono_comp_return, ci_mono_emit_op]) >> gvs[]
QED

Theorem return_copy_offset_run_seq[local]:
  compile_with_byte_offset baseop off sa = (op,sb) /\
  eval_operand baseop s = SOME w /\ off <> 0 ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (w + n2w off) s) /\
  op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >> gvs[compile_with_byte_offset_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_def, exec_pure2_def, eval_operand_def]
QED

Theorem return_copy_offset_frag:
  compile_with_byte_offset baseop off sa = (op,sb) /\
  eval_operand baseop s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. eval_operand op t = SOME (w + n2w off) /\
         t.vs_memory = s0.vs_memory /\
         return_copy_frame sa dst len s0 t) (\r. F)
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      irule frag_exec_refl >> simp[WORD_ADD_0]) >>
  drule_all return_copy_offset_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[] >>
  simp[eval_operand_def, lookup_var_update_var, return_copy_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem return_copy_offset_child_frag:
  !baseop off sa op sm sb s0 w dst len Q.
  compile_with_byte_offset baseop off sa = (op,sm) /\
  eval_operand baseop s0 = SOME w /\
  cs_extends sa sm /\ cs_extends sm sb /\
  (!t. eval_operand op t = SOME (w + n2w off) /\
       t.vs_memory = s0.vs_memory /\ return_copy_frame sa dst len s0 t ==>
       frag_exec ctx sm sb (\s. s = t)
         (\u. Q u /\ return_copy_frame sa dst len t u) (\r. F)) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\u. Q u /\ return_copy_frame sa dst len s0 u) (\r. F)
Proof
  rpt gen_tac >> strip_tac >> drule_all return_copy_offset_frag >>
  disch_then (qspecl_then [`len`, `dst`, `ctx`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> irule return_copy_frame_trans >>
  qexists_tac `t` >> simp[]
QED

Theorem return_copy_operand_fresh_mono:
  ci_mono sa sb /\ (!x. op = Var x ==> not_fresh_at sa x) ==>
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rw[ci_mono_def, not_fresh_at_def] >>
  first_x_assum drule >> simp[] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem return_copy_offset_fresh:
  !baseop off sa op sb.
  compile_with_byte_offset baseop off sa = (op,sb) /\
  (!x. baseop = Var x ==> not_fresh_at sa x) ==>
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rw[compile_with_byte_offset_def] >>
  gvs[comp_return_def, emit_op_def, comp_bind_def, fresh_var_def,
      emit_def, comp_ignore_bind_def, emit_inst_def, fresh_id_def,
      not_fresh_at_def] >> simp[ASCIInumbersTheory.toString_inj]
QED

Theorem return_copy_offset_nonwrap:
  !w:bytes32. !off. w2n w + off < dimword (:256) ==>
    w2n (w + n2w off) = w2n w + off
Proof
  rpt strip_tac >> `off < dimword (:256)` by decide_tac >>
  `w = n2w (w2n w)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[word_add_n2w, LESS_MOD]
QED

Theorem return_copy_source_offset:
  val_wf tv v /\ val_in_memory tv v (w2n (sw:bytes32) + soff) mem /\
  (0 < val_footprint tv v ==>
    w2n sw + soff + val_footprint tv v < dimword (:256)) ==>
  val_in_memory tv v (w2n (sw + n2w soff)) mem
Proof
  strip_tac >> Cases_on `val_footprint tv v = 0`
  >- (`type_memory_size tv = 0` by
        (Cases_on `v` >> gvs[val_footprint_def, AllCaseEqs()]) >>
      metis_tac[return_zero_layout_memory_address]) >>
  `w2n sw + soff < dimword (:256)` by decide_tac >>
  drule return_copy_offset_nonwrap >> metis_tac[]
QED


Theorem return_copy_two_offsets_frag:
  !dst src doff soff sa dp s1 sp s2 sb s0 dw sw off len Q.
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  ci_mono s2 sb /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s0 = SOME dw /\ eval_operand src s0 = SOME sw /\
  (!u. eval_operand dp u = SOME (dw + n2w doff) /\
       eval_operand sp u = SOME (sw + n2w soff) /\
       u.vs_memory = s0.vs_memory ==>
       frag_exec ctx s2 sb (\s. s = u)
         (\t. Q t /\ return_copy_frame s2 off len u t) (\r. F)) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. Q t /\ return_copy_frame sa off len s0 t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by metis_tac[return_copy_offset_mono] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s1 sb /\ cs_extends s2 sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `!x. dp = Var x ==> not_fresh_at s1 x` by
    metis_tac[return_copy_offset_fresh] >>
  irule return_copy_offset_child_frag >>
  qexistsl_tac [`dst`, `doff`, `dp`, `s1`, `dw`] >> simp[] >>
  rpt strip_tac >>
  `eval_operand src t = SOME sw` by metis_tac[return_copy_frame_operand] >>
  irule frag_exec_conseq >>
  qexistsl_tac [`(\u. u = t)`, `(\u. Q u /\ return_copy_frame s1 off len t u)`, `(\r. F)`] >>
  simp[] >> conj_tac
  >- metis_tac[return_copy_frame_mono] >>
  irule return_copy_offset_child_frag >>
  qexistsl_tac [`src`, `soff`, `sp`, `s2`, `sw`] >> simp[] >>
  rpt strip_tac >>
  `eval_operand dp t' = SOME (dw + n2w doff)` by
    metis_tac[return_copy_frame_operand] >>
  first_x_assum drule_all >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  metis_tac[return_copy_frame_mono]
QED

Theorem return_copy_remaining_source_separation:
  (src:num) <= childsrc /\ childsrc + footprint <= src + extent /\
  dst <= childdst /\ childdst + childlen <= dst + len /\
  (src + extent <= dst \/ dst + len <= src) ==>
  childsrc + footprint <= childdst \/ childdst + childlen <= childsrc
Proof
  decide_tac
QED

Theorem return_copy_offsets_value_frag:
  !dst src doff soff sa dp s1 sp s2 sb s0 dw sw dtv stv v.
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\ ci_mono s2 sb /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s0 = SOME dw /\ eval_operand src s0 = SOME sw /\
  val_wf stv v /\ val_in_memory stv v (w2n sw + soff) s0.vs_memory /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + soff + val_footprint stv v < dimword (:256) /\
    (w2n sw + soff + val_footprint stv v <= w2n dw + doff \/
     w2n dw + doff + type_memory_size dtv <= w2n sw + soff)) /\
  (!u. eval_operand dp u = SOME (dw + n2w doff) /\
       eval_operand sp u = SOME (sw + n2w soff) /\
       val_in_memory stv v (w2n (sw + n2w soff)) u.vs_memory ==>
       frag_exec ctx s2 sb (\s. s = u)
         (\t. val_in_memory dtv v (w2n (dw + n2w doff)) t.vs_memory /\
              return_copy_frame s2 (w2n dw + doff) (type_memory_size dtv) u t)
         (\r. F)) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
         return_copy_frame sa (w2n dw + doff) (type_memory_size dtv) s0 t)
    (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n dw + doff < dimword (:256)` by decide_tac >>
  `w2n (dw + n2w doff) = w2n dw + doff` by
    metis_tac[return_copy_offset_nonwrap] >>
  `val_in_memory stv v (w2n (sw + n2w soff)) s0.vs_memory` by
    (irule return_copy_source_offset >> simp[]) >>
  ho_match_mp_tac return_copy_two_offsets_frag >>
  qexistsl_tac [`dst`, `src`, `doff`, `soff`, `dp`, `s1`, `sp`, `s2`, `dw`, `sw`] >>
  simp[] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED
