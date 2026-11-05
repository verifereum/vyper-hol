(* Generated-label intervals do not require freshness of the initial state. *)
Theory exprSimAbiEncodeLabelProvenance
Ancestors
  fragExec compileEnv emitHelper emitHelperProps abiEncoder abiEncoderAppend context list rich_list arithmetic pred_set

Definition enc_label_between_def:
  enc_label_between lo hi l <=>
    ?s k. MEM s ["enc_dyn_hdr"; "enc_dyn_body"; "enc_dyn_exit"] /\
      lo <= k /\ k < hi /\ l = fresh_label_output s k
End

Definition enc_label_span_def:
  enc_label_span sa sb <=>
    sa.cs_next_label <= sb.cs_next_label /\
    (?bs. sb.cs_blocks = bs ++ sa.cs_blocks) /\
    (!b. MEM b (emitted_blocks sa sb) ==>
      b.bb_label = sa.cs_current_bb \/
      enc_label_between sa.cs_next_label sb.cs_next_label b.bb_label) /\
    (sb.cs_current_bb = sa.cs_current_bb \/
      enc_label_between sa.cs_next_label sb.cs_next_label sb.cs_current_bb)
End

Theorem enc_label_between_mono:
  lo' <= lo /\ hi <= hi' /\ enc_label_between lo hi l ==>
    enc_label_between lo' hi' l
Proof
  simp[enc_label_between_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem enc_label_between_split:
  lo <= mid /\ mid <= hi ==>
  (enc_label_between lo hi l <=>
    enc_label_between lo mid l \/ enc_label_between mid hi l)
Proof
  simp[enc_label_between_def] >> rpt strip_tac >> eq_tac
  >- (strip_tac >> Cases_on `k < mid` >> metis_tac[NOT_LESS]) >>
  strip_tac >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem enc_label_between_older:
  enc_label_between lo hi l /\ k < lo ==> l <> fresh_label_output s k
Proof
  simp[enc_label_between_def] >> rpt strip_tac >> gvs[] >>
  drule fresh_label_output_inj >> strip_tac >> gvs[]
QED

Theorem enc_label_span_refl:
  enc_label_span sa sa
Proof
  simp[enc_label_span_def, emitted_blocks_def]
QED

Theorem enc_label_span_trans:
  enc_label_span sa sm /\ enc_label_span sm sb ==> enc_label_span sa sb
Proof
  simp[enc_label_span_def] >> strip_tac >>
  `emitted_blocks sa sm = bs /\ emitted_blocks sm sb = bs' /\
   emitted_blocks sa sb = bs' ++ bs` by
    (rpt conj_tac >> irule emitted_blocks_append >> simp[APPEND_ASSOC]) >>
  `?new. sb.cs_blocks = new ++ sa.cs_blocks` by
    (qexists_tac `bs' ++ bs` >> simp[APPEND_ASSOC]) >>
  simp[] >> metis_tac[enc_label_between_mono, LESS_EQ_REFL, LESS_EQ_TRANS]
QED

Theorem enc_label_span_older:
  enc_label_span sa sb /\ k < sa.cs_next_label /\
  sa.cs_current_bb <> fresh_label_output s k ==>
  sb.cs_current_bb <> fresh_label_output s k /\
  (!b. MEM b (emitted_blocks sa sb) ==> b.bb_label <> fresh_label_output s k)
Proof
  simp[enc_label_span_def] >> metis_tac[enc_label_between_older]
QED

Definition enc_label_action_def:
  enc_label_action (action : 'a compiler) <=>
    !sa out sb. action sa = (out,sb) ==> enc_label_span sa sb
End

Theorem enc_label_action_bind:
  enc_label_action action /\ (!v. enc_label_action (next v)) ==>
  enc_label_action (comp_bind action next)
Proof
  rw[enc_label_action_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
  irule enc_label_span_trans >> metis_tac[]
QED

Theorem enc_label_action_ignore_bind:
  enc_label_action action /\ enc_label_action next ==>
  enc_label_action (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule enc_label_action_bind >> simp[]
QED

Theorem enc_label_action_return:
  enc_label_action (comp_return v)
Proof
  simp[enc_label_action_def, comp_return_def, enc_label_span_refl]
QED

Theorem enc_label_action_linear:
  (!opc ops. enc_label_action (emit_op opc ops)) /\
  (!opc ops. enc_label_action (emit_void opc ops)) /\
  (!opc ops outs. enc_label_action (emit_inst opc ops outs)) /\
  (!n. enc_label_action (compile_alloc_buffer n))
Proof
  simp[enc_label_action_def, enc_label_span_def, emitted_blocks_def,
    emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, LET_THM]
QED

Theorem enc_label_action_static:
  enc_label_action (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >>
  irule enc_label_action_bind >> simp[enc_label_action_linear] >>
  gen_tac >> irule enc_label_action_ignore_bind >>
  simp[enc_label_action_linear, enc_label_action_return]
QED

Theorem enc_label_action_static_info:
  enc_label_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    enc_label_action_static, enc_label_action_return] >>
  irule enc_label_action_ignore_bind >>
  simp[enc_label_action_linear, enc_label_action_return]
QED

Definition enc_label_flat_def:
  enc_label_flat (action : 'a compiler) <=>
    !sa out sb. action sa = (out,sb) ==>
      sb.cs_next_label = sa.cs_next_label /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb
End

Theorem enc_label_flat_static_info:
  enc_label_flat (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >>
  simp[enc_label_flat_def, compile_abi_encode_static_info_def,
    compile_abi_encode_static_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, LET_THM]
QED

Theorem enc_label_between_three:
  enc_label_between n (n+3) (fresh_label_output "enc_dyn_hdr" n) /\
  enc_label_between n (n+3) (fresh_label_output "enc_dyn_body" (n+1)) /\
  enc_label_between n (n+3) (fresh_label_output "enc_dyn_exit" (n+2))
Proof
  simp[enc_label_between_def] >> rpt conj_tac
  >- (qexistsl_tac [`"enc_dyn_hdr"`, `n`] >> simp[])
  >- (qexistsl_tac [`"enc_dyn_body"`, `n+1`] >> simp[])
  >> qexistsl_tac [`"enc_dyn_exit"`, `n+2`] >> simp[]
QED

Theorem enc_label_action_static_loop:
  enc_label_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  simp[enc_label_action_def, compile_abi_encode_dyn_static_loop_def,
    compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule (SRULE[enc_label_flat_def] enc_label_flat_static_info) >>
  strip_tac >> qpat_x_assum `compile_abi_encode_static_info _ _ _ _ = _` kall_tac >>
  gvs[] >>
  simp[enc_label_span_def, emitted_blocks_def, enc_label_between_three, ADD1] >>
  rpt strip_tac >> gvs[enc_label_between_three]
QED

Theorem enc_label_span_close:
  enc_label_span sa sc /\
  enc_label_between sa.cs_next_label sc.cs_next_label l ==>
  enc_label_span sa
    (sc with <|cs_next_var := v; cs_next_id := i; cs_current_bb := l;
      cs_current_insts := js;
      cs_blocks := <|bb_label := sc.cs_current_bb; bb_instructions := is|> :: sc.cs_blocks|>)
Proof
  simp[enc_label_span_def] >> strip_tac >>
  `emitted_blocks sa sc = bs` by
    (irule emitted_blocks_append >> simp[]) >>
  `emitted_blocks sa
    (sc with <|cs_next_var := v; cs_next_id := i; cs_current_bb := l;
      cs_current_insts := js;
      cs_blocks := <|bb_label := sc.cs_current_bb; bb_instructions := is|> :: sc.cs_blocks|>) =
    <|bb_label := sc.cs_current_bb; bb_instructions := is|> :: bs` by
    (irule emitted_blocks_append >> simp[]) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem enc_label_action_dyn_loop_step:
  (!dst src. enc_label_action (compile_abi_encode_to_buf dst src ei)) ==>
  enc_label_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  strip_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[enc_label_action_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!dst src. _` (mp_tac o SRULE[enc_label_action_def]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `enc_label_span sm sc` >>
  `enc_label_span sa sm` by
    (simp[Abbr `sm`, enc_label_span_def, emitted_blocks_def,
      enc_label_between_three, ADD1] >> rpt strip_tac >>
     gvs[enc_label_between_three]) >>
  `sa.cs_next_label + 3 <= sc.cs_next_label` by
    (qpat_x_assum `enc_label_span sm sc` mp_tac >>
     simp[enc_label_span_def, Abbr `sm`]) >>
  irule enc_label_span_close >> conj_tac
  >- (irule enc_label_span_trans >> qexists_tac `sm` >> simp[]) >>
  irule enc_label_between_mono >>
  qexistsl_tac [`sa.cs_next_label + 3`, `sa.cs_next_label`] >>
  simp[enc_label_between_three]
QED

(* Syntax-directed composition of label spans; no compiler bodies are unfolded
   below these boundary facts. *)
fun enc_label_compose_tac g =
  (FIRST [
    FIRST_PROVE [asm_simp_tac (srw_ss())
      [enc_label_action_return, enc_label_action_linear,
       enc_label_action_static, enc_label_action_static_loop, LET_THM]],
    first_x_assum (fn th => FIRST_PROVE [irule (SRULE[] th) >> simp[]]),
    ho_match_mp_tac enc_label_action_bind >> conj_tac
      >- enc_label_compose_tac >> gen_tac >> enc_label_compose_tac,
    ho_match_mp_tac enc_label_action_ignore_bind >> conj_tac >> enc_label_compose_tac,
    IF_CASES_TAC >> fs[] >> enc_label_compose_tac]) g;

Theorem enc_label_action_mutual:
  (!dst src ei dyn off ptr.
    enc_label_action (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. enc_label_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    enc_label_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    enc_label_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`enc_label_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule enc_label_action_dyn_loop_step >> simp[]) >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> fs[] >> enc_label_compose_tac)
  >- enc_label_compose_tac
  >- enc_label_compose_tac
  >- enc_label_compose_tac
  >- (Cases_on `elem_is_dyn` >> fs[] >> enc_label_compose_tac)
  >- enc_label_compose_tac
  >- (IF_CASES_TAC >> fs[] >> enc_label_compose_tac)
  >- enc_label_compose_tac >>
  enc_label_compose_tac
QED

Theorem enc_label_span_to_buf:
  compile_abi_encode_to_buf dst src ei sa = (out,sb) ==>
  enc_label_span sa sb
Proof
  metis_tac[cj 2 enc_label_action_mutual, enc_label_action_def]
QED

Theorem enc_label_span_nested_child:
  compile_abi_encode_to_buf dst src ei sa = (out,sb) /\
  sa.cs_current_bb = fresh_label_output "enc_dyn_body" (k+1) /\
  k+3 <= sa.cs_next_label ==>
  (sb.cs_current_bb <> fresh_label_output "enc_dyn_hdr" k /\
   (!b. MEM b (emitted_blocks sa sb) ==>
     b.bb_label <> fresh_label_output "enc_dyn_hdr" k)) /\
  (sb.cs_current_bb <> fresh_label_output "enc_dyn_exit" (k+2) /\
   (!b. MEM b (emitted_blocks sa sb) ==>
     b.bb_label <> fresh_label_output "enc_dyn_exit" (k+2)))
Proof
  strip_tac >> drule enc_label_span_to_buf >> strip_tac >>
  `fresh_label_output "enc_dyn_body" (k+1) <> fresh_label_output "enc_dyn_hdr" k /\
   fresh_label_output "enc_dyn_body" (k+1) <> fresh_label_output "enc_dyn_exit" (k+2)` by
    (conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]) >>
  conj_tac >> irule enc_label_span_older >> simp[]
QED
