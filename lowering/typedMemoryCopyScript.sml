(* Layout conversion between disjoint memory regions. Memory Assign stages
   its source before invoking this routine; that staging allocation belongs
   to the caller's frame, while this routine writes only the destination.
   Metadata premises are the field-layout clauses of expr_sim_inv. *)
Theory typedMemoryCopy
Ancestors
  exprSimProps loweringPosts
  context typedCopyDomain compileEnv emitHelper emitHelperProps structFieldsProps valueEncoding valueEncodingProps
  valueEncodingProofs valueCopy fragExec exprLoweringProps exprSimHyps
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping
  venomExecSemantics venomState venomInst words list pair finite_map arithmetic vfmConstants


Theorem typed_copy_static_fits:
  (!sty dty. arg_type_fits sty dty /\ ~is_abi_dynamic sf dty ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys /\
     ~EXISTS (is_abi_dynamic sf) dtys ==> stys = dtys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_abi_dynamic_def] >>
  gvs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> fs[]
QED

Theorem typed_copy_static_widening:
  type_widens_to tenv sty dty /\ ~is_abi_dynamic sf dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  stv = dtv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  drule (cj 1 typed_copy_static_fits) >>
  disch_then (qspec_then `sf` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem typed_copy_array_count_bound:
  evaluate_type tenv (ArrayT elem bd) = SOME tv ==>
  bound_length bd < dimword (:256)
Proof
  rw[evaluate_type_def, AllCaseEqs()] >> Cases_on `bd` >>
  gvs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
  `n <= n * type_slot_size tv'` by
    (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >>
  decide_tac
QED

Theorem typed_copy_array_widening:
  type_widens_to tenv (ArrayT se sb) (ArrayT de db) ==>
  (se = de \/ arg_type_fits se de) /\
  ((?n m. sb = Dynamic n /\ db = Dynamic m /\ n <= m) \/
   (?n. sb = Fixed n /\ db = Fixed n))
Proof
  Cases_on `sb` >> Cases_on `db` >>
  rw[type_widens_to_def, arg_type_fits_def] >>
  simp[arg_type_fits_def]
QED

Theorem typed_copy_struct_widening:
  type_widens_to tenv sty (StructT name) ==> sty = StructT name
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >> metis_tac[]
QED

Theorem typed_copy_tuple_widening:
  type_widens_to tenv sty (TupleT dtys) ==>
  ?stys. sty = TupleT stys /\ (stys = dtys \/ arg_types_fit stys dtys)
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  metis_tac[]
QED

Theorem typed_copy_array_source:
  type_widens_to tenv sty (ArrayT de db) ==>
  ?se sb. sty = ArrayT se sb
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  Cases_on `b` >> Cases_on `db` >> simp[arg_type_fits_def] >> metis_tac[]
QED

Theorem typed_copy_word_widening:
  type_widens_to tenv sty dty /\ is_word_type dty ==> sty = dty
Proof
  metis_tac[compileEnvTheory.type_widens_to_word]
QED

Theorem typed_copy_bytestring_source:
  type_widens_to tenv sty dty /\ is_bytestring_type dty ==>
  is_bytestring_type sty
Proof
  metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem typed_copy_array_subinterval:
  !i n off stride:num.
  i < n ==> off <= off + i * stride /\
    off + i * stride + stride <= off + n * stride
Proof
  rpt gen_tac >> strip_tac >>
  `SUC i <= n` by decide_tac >>
  `SUC i * stride <= n * stride` by simp[] >>
  pop_assum mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED

(* Destination-local memory effects; independent of control-flow state. *)
Definition typed_copy_frame_def:
  typed_copy_frame off len mem mem' <=>
    (!a n. a + n <= off \/ off + len <= a ==>
      mem_bytes_at a n mem' = mem_bytes_at a n mem) /\
    LENGTH mem <= LENGTH mem'
End

Theorem typed_copy_frame_refl[simp]:
  typed_copy_frame off len mem mem
Proof
  simp[typed_copy_frame_def]
QED

Theorem typed_copy_frame_trans:
  typed_copy_frame off len mem1 mem2 /\
  typed_copy_frame off len mem2 mem3 ==>
  typed_copy_frame off len mem1 mem3
Proof
  rw[typed_copy_frame_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem typed_copy_frame_subinterval:
  off <= child /\ child + clen <= off + len /\
  typed_copy_frame child clen mem mem' ==>
  typed_copy_frame off len mem mem'
Proof
  rw[typed_copy_frame_def] >>
  `a + n <= child \/ child + clen <= a` by decide_tac >>
  metis_tac[]
QED

Theorem typed_copy_frame_preserves_source:
  typed_copy_frame dst dlen mem mem' /\
  val_in_memory tv v src mem /\ val_wf tv v /\
  (src + type_memory_size tv <= dst \/ dst + dlen <= src) ==>
  val_in_memory tv v src mem'
Proof
  rw[typed_copy_frame_def] >>
  (irule val_in_memory_mem_agree >>
   conj_tac >- simp[] >>
   qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[])
QED

Theorem typed_copy_elems_indexed:
  !vs off tv mem.
  elems_in_memory vs off tv mem <=>
  !i. i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases >> simp[ADD_CLAUSES, MULT_CLAUSES] >>
      rpt strip_tac >> first_x_assum drule >> simp[ADD_ASSOC]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  pure_rewrite_tac[LT_SUC, EL, HD, TL, MULT_CLAUSES, ADD_ASSOC] >> simp[]
QED

Definition typed_copy_elems_prefix_def:
  typed_copy_elems_prefix vs tv off k mem <=>
    k <= LENGTH vs /\
    !i. i < k ==>
      val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
End

Theorem typed_copy_elems_prefix_zero[simp]:
  typed_copy_elems_prefix vs tv off 0 mem
Proof
  simp[typed_copy_elems_prefix_def]
QED

Theorem typed_copy_elems_prefix_step:
  typed_copy_elems_prefix vs tv off k mem /\ k < LENGTH vs /\
  val_in_memory tv (EL k vs) (off + k * type_memory_size tv) mem ==>
  typed_copy_elems_prefix vs tv off (SUC k) mem
Proof
  rw[typed_copy_elems_prefix_def] >>
  Cases_on `i = k` >> gvs[]
QED

Theorem typed_copy_elems_prefix_complete:
  typed_copy_elems_prefix vs tv off (LENGTH vs) mem ==>
  elems_in_memory vs off tv mem
Proof
  simp[typed_copy_elems_prefix_def, typed_copy_elems_indexed]
QED

Theorem typed_copy_sarray_element:
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
  i < n ==>
  val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (off + i * type_memory_size tv) mem
Proof
  rw[val_in_memory_sarray] >> Cases_on `ALOOKUP kvs i` >> simp[] >>
  metis_tac[kvs_in_memory_lookup]
QED

Theorem typed_copy_sparse_member:
  !kvs tv n i v.
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  MEM (i,v) kvs ==> i < n /\ ALOOKUP kvs i = SOME v
Proof
  rpt gen_tac >> simp[value_has_type_def] >> strip_tac >>
  `ALL_DISTINCT (MAP FST kvs)` by metis_tac[SORTED_lt_ALL_DISTINCT] >>
  qpat_x_assum `SORTED _ _` kall_tac >>
  Induct_on `kvs` >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def] >> rpt strip_tac >> gvs[] >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem typed_copy_kvs_members:
  !kvs off tv mem.
  kvs_in_memory kvs off tv mem <=>
  !i v. MEM (i,v) kvs ==>
    val_in_memory tv v (off + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> Cases >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem typed_copy_sarray_indexed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (!i. i < n ==>
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      (off + i * type_memory_size tv) mem) ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem
Proof
  strip_tac >> rewrite_tac[val_in_memory_sarray] >> conj_tac
  >- (rewrite_tac[typed_copy_kvs_members] >> rpt strip_tac >>
      drule_all typed_copy_sparse_member >> strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Definition typed_copy_sparse_prefix_def:
  typed_copy_sparse_prefix kvs tv n off k mem <=>
    k <= n /\ !i. i < k ==>
      val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
        (off + i * type_memory_size tv) mem
End

Theorem typed_copy_sparse_prefix_zero[simp]:
  typed_copy_sparse_prefix kvs tv n off 0 mem
Proof
  simp[typed_copy_sparse_prefix_def]
QED

Theorem typed_copy_sparse_prefix_step:
  typed_copy_sparse_prefix kvs tv n off k mem /\ k < n /\
  val_in_memory tv (case ALOOKUP kvs k of NONE => default_value tv | SOME v => v)
    (off + k * type_memory_size tv) mem ==>
  typed_copy_sparse_prefix kvs tv n off (SUC k) mem
Proof
  rw[typed_copy_sparse_prefix_def] >> Cases_on `i = k` >> gvs[]
QED

Theorem typed_copy_sparse_prefix_complete:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  typed_copy_sparse_prefix kvs tv n off n mem ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem
Proof
  rw[typed_copy_sparse_prefix_def] >> irule typed_copy_sarray_indexed >> simp[]
QED

Theorem typed_copy_elems_wf_indexed:
  !vs tv. elems_val_wf vs tv <=>
    !i. i < LENGTH vs ==> val_wf tv (EL i vs)
Proof
  Induct >> simp[val_wf_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases >> simp[] ) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem typed_copy_elems_prefix_frame:
  typed_copy_elems_prefix vs tv off k mem /\ elems_val_wf vs tv /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_elems_prefix vs tv off k mem'
Proof
  rw[typed_copy_elems_prefix_def] >>
  irule typed_copy_frame_preserves_source >>
  conj_tac
  >- metis_tac[typed_copy_elems_wf_indexed, LESS_LESS_EQ_TRANS] >>
  qexistsl_tac [`len`, `off + k * type_memory_size tv`, `mem`] >>
  simp[] >> disj1_tac >> drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]
QED

Theorem typed_copy_sparse_lookup_wf:
  !kvs tv n i. kvs_val_wf kvs tv n ==>
    val_wf tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
Proof
  Induct >> simp[val_wf_def, cj 1 val_wf_default_value_proof] >>
  Cases >> simp[val_wf_def] >> rpt strip_tac >>
  Cases_on `q = i` >> gvs[] >> metis_tac[]
QED

Theorem typed_copy_sparse_prefix_frame:
  typed_copy_sparse_prefix kvs tv n off k mem /\ kvs_val_wf kvs tv n /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_sparse_prefix kvs tv n off k mem'
Proof
  rw[typed_copy_sparse_prefix_def] >>
  irule typed_copy_frame_preserves_source >> conj_tac
  >- metis_tac[typed_copy_sparse_lookup_wf] >>
  qexistsl_tac [`len`, `off + k * type_memory_size tv`, `mem`] >>
  simp[] >> disj1_tac >> drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]
QED

Theorem typed_copy_tuple_cursor:
  !vs tvs ws uts off mem.
  LENGTH vs = LENGTH tvs ==>
  (tuple_in_memory (vs ++ ws) (tvs ++ uts) off mem <=>
   tuple_in_memory vs tvs off mem /\
   tuple_in_memory ws uts (off + type_memory_size_list tvs) mem)
Proof
  Induct >> Cases_on `tvs` >>
  simp[val_in_memory_def, type_memory_size_def] >>
  rpt strip_tac >> pure_rewrite_tac[ADD_ASSOC, CONJ_ASSOC] >> metis_tac[]
QED

Theorem typed_copy_fields_cursor:
  !vs tvs ws uts off mem.
  LENGTH vs = LENGTH tvs ==>
  (fields_in_memory (vs ++ ws) (tvs ++ uts) off mem <=>
   fields_in_memory vs tvs off mem /\
   fields_in_memory ws uts (off + type_memory_size_fields tvs) mem)
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def, val_in_memory_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  simp[type_memory_size_def, val_in_memory_def] >>
  rpt strip_tac >> pure_rewrite_tac[ADD_ASSOC, CONJ_ASSOC] >> metis_tac[]
QED

Definition typed_copy_state_frame_def:
  typed_copy_state_frame sa off len s t <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    typed_copy_frame off len s.vs_memory t.vs_memory
End

Theorem typed_copy_state_frame_refl[simp]:
  typed_copy_state_frame sa off len s s
Proof
  simp[typed_copy_state_frame_def]
QED

Theorem typed_copy_state_frame_trans:
  typed_copy_state_frame sa off len s t /\
  typed_copy_state_frame sa off len t u ==>
  typed_copy_state_frame sa off len s u
Proof
  rw[typed_copy_state_frame_def]
  >- gvs[venom_state_component_equality] >>
  metis_tac[typed_copy_frame_trans]
QED

Theorem typed_copy_state_frame_subinterval:
  off <= child /\ child + clen <= off + len /\
  typed_copy_state_frame sa child clen s t ==>
  typed_copy_state_frame sa off len s t
Proof
  rw[typed_copy_state_frame_def] >>
  irule typed_copy_frame_subinterval >> qexistsl_tac [`child`, `clen`] >> simp[]
QED

Theorem typed_copy_empty_frag:
  val_in_memory tv v off s0.vs_memory ==>
  frag_exec ctx sa sa (\s. s = s0)
    (\t. val_in_memory tv v off t.vs_memory /\
         typed_copy_state_frame sa off (type_memory_size tv) s0 t)
    (\r. F)
Proof
  strip_tac >> irule frag_exec_refl >> simp[]
QED

Theorem typed_copy_frag_run:
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v off t.vs_memory /\
         typed_copy_state_frame sa off (type_memory_size tv) s0 t) (\r. F) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v off t.vs_memory /\
      typed_copy_state_frame sa off (type_memory_size tv) s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
         ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  simp[frag_exec_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `func` mp_tac) >> simp[CONJ_ASSOC]
QED

Theorem typed_copy_mcopy_frag:
  emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  n < dimword (:256) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) (w2n a) n s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all emit_mcopy_run >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def] >> simp[]
QED

Theorem typed_copy_fixed_raw_frag:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword (:256) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((if n = 0 then s0 else mcopy (w2n d) (w2n a) n s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, comp_return_def] >> strip_tac
  >- (gvs[] >> irule frag_exec_refl >> simp[venom_state_component_equality]) >>
  irule typed_copy_mcopy_frag >> simp[] >> qexistsl_tac [`dst`, `src`] >> simp[]
QED

Theorem typed_copy_dynamic_run_seq:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME w ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n d) (w2n a) (w2n w) s)
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[same_blocks_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, run_inst_seq_def] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem typed_copy_dynamic_raw_frag:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) (w2n a) (w2n w) s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dynamic_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
QED

Theorem typed_copy_mcopy_state_frame:
  typed_copy_state_frame sa dst n s
    ((mcopy dst src n s) with vs_inst_idx := idx)
Proof
  rw[typed_copy_state_frame_def]
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] 
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >> simp[]) >>
  simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity, MAX_DEF]
QED

Theorem typed_copy_dynamic_frag:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= w2n w /\ w2n w <= type_memory_size tv ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dynamic_raw_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >> simp[] >>
  conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n d`, `w2n w`] >>
  simp[typed_copy_mcopy_state_frame]
QED

Theorem typed_copy_fixed_frag:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_fixed_raw_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >> simp[] >>
  Cases_on `n = 0` >> simp[]
  >- (conj_tac
      >- (irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
          qexistsl_tac [`w2n a`, `0`, `s0.vs_memory`] >> simp[mem_bytes_at_def]) >>
      simp[typed_copy_state_frame_def, venom_state_component_equality,
           lookup_var_def]) >>
  conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n d`, `n`] >> simp[typed_copy_mcopy_state_frame]
QED

Theorem typed_copy_operand_fresh_mono:
  ci_mono sa sb /\ (!x. op = Var x ==> not_fresh_at sa x) ==>
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rw[ci_mono_def, not_fresh_at_def] >>
  first_x_assum drule >> simp[] >>
  metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem typed_copy_offset_mono:
  !ptr0 off sa op sb.
    compile_with_byte_offset ptr0 off sa = (op,sb) ==> ci_mono sa sb
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa (SND (compile_with_byte_offset ptr0 off sa))` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` kall_tac >>
     rw[compile_with_byte_offset_def] >>
     simp[ci_mono_comp_return, ci_mono_emit_op]) >>
  gvs[]
QED

Theorem typed_copy_offset_fresh:
  !ptr off sa op sb.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  (!x. ptr = Var x ==> not_fresh_at sa x) ==>
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rw[compile_with_byte_offset_def] >>
  gvs[comp_return_def, emit_op_def, comp_bind_def, fresh_var_def,
      emit_def, comp_ignore_bind_def, emit_inst_def, fresh_id_def,
      not_fresh_at_def] >>
  simp[ASCIInumbersTheory.toString_inj]
QED

Theorem typed_copy_offset_run_seq:
  !ptr off sa op sb s w.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s = SOME w /\ off <> 0 ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (w + n2w off) s) /\
  op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_with_byte_offset_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       run_inst_seq_def, step_inst_base_def, exec_pure2_def, eval_operand_def]
QED

Theorem typed_copy_offset_frag:
  !ptr off sa op sb s0 w dst len.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. eval_operand op t = SOME (w + n2w off) /\
         t.vs_memory = s0.vs_memory /\
         typed_copy_state_frame sa dst len s0 t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      irule frag_exec_refl >> simp[wordsTheory.WORD_ADD_0]) >>
  drule_all typed_copy_offset_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[] >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_state_frame_operand:
  typed_copy_state_frame sa dst len s t /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op t = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, typed_copy_state_frame_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality]
QED

Theorem typed_copy_offset_nonwrap:
  !w:bytes32. !off. w2n w + off < dimword (:256) ==>
    w2n (w + n2w off) = w2n w + off
Proof
  rpt strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `w = n2w (w2n w)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_add_n2w, LESS_MOD]
QED

Theorem typed_copy_offset_child_frag:
  !ptr off sa op sm sb s0 w dst len Q.
  compile_with_byte_offset ptr off sa = (op,sm) /\
  eval_operand ptr s0 = SOME w /\
  cs_extends sa sm /\ cs_extends sm sb /\
  (!t. eval_operand op t = SOME (w + n2w off) /\
       t.vs_memory = s0.vs_memory /\ typed_copy_state_frame sa dst len s0 t ==>
       frag_exec ctx sm sb (\s. s = t)
         (\u. Q u /\ typed_copy_state_frame sa dst len t u) (\r. F)) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\u. Q u /\ typed_copy_state_frame sa dst len s0 u) (\r. F)
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_copy_offset_frag >>
  disch_then (qspecl_then [`ctx`, `dst`, `len`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> irule typed_copy_state_frame_trans >>
  qexists_tac `t` >> simp[]
QED

Theorem typed_copy_word_run_seq:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n d) (mload (w2n a) s)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s) s))
Proof
  strip_tac >>
  `!w. eval_operand dst
       (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def, update_var_def, lookup_var_def] >>
     rpt strip_tac >>
     `s' <> STRING #"%" (toString sa.cs_next_var)` by
       (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     simp[FLOOKUP_UPDATE]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[eval_operand_def, exec_read1_def, exec_write2_def, lookup_var_update_var]
QED

Theorem typed_copy_word_raw_frag:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = (mstore (w2n d) (mload (w2n a) s0)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s0) s0))
      with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_word_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
QED

Theorem typed_copy_word_state_frame:
  typed_copy_state_frame sa dst 32 s
    ((mstore dst w (update_var (STRING #"%" (toString sa.cs_next_var)) w s))
      with vs_inst_idx := idx)
Proof
  simp[typed_copy_state_frame_def] >> conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def, update_var_def,
          venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
      simp[mstore_def, write_memory_with_expansion_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE]) >>
  `(mstore dst w (update_var (STRING #"%" (toString sa.cs_next_var)) w s)).vs_memory =
   (mstore dst w s).vs_memory` by simp[mstore_def, update_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, update_var_def, MAX_DEF]
QED

Theorem typed_copy_word_frag:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s0.vs_memory = typed_val_to_w256 tv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_word_raw_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >> simp[] >>
  conj_tac
  >- (drule_all entryDecodePropsTheory.val_in_memory_word >> strip_tac >>
      simp[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  simp[typed_copy_word_state_frame]
QED

Theorem typed_copy_bytestring_frag_exact:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all store_bytestring_run_exact >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[] >>
  conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  simp[typed_copy_state_frame_def] >> conj_tac
  >- gvs[venom_state_component_equality] >>
  conj_tac >- gvs[lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
      decide_tac) >>
  simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity, MAX_DEF]
QED

Theorem typed_copy_bytestring_frag:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\ L + 64 < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >>
  `32 + 32 * word_size L < dimword (:256)` by
    (`(L + 31) DIV 32 * 32 <= L + 31` by
       (qspec_then `32` mp_tac DIVISION >> simp[] >>
        disch_then (qspec_then `L + 31` mp_tac) >> decide_tac) >>
     qpat_x_assum `_ DIV _ * _ <= _` mp_tac >>
     simp_tac pure_ss [word_size_def, MULT_COMM] >> decide_tac) >>
  drule_all typed_copy_bytestring_frag_exact >> simp[]
QED

Theorem typed_copy_bytestring_extent_bound:
  32 + 32 * word_size L <= type_memory_size stv /\
  src + type_memory_size stv < dimword (:256) ==>
  32 + 32 * word_size L < dimword (:256)
Proof
  decide_tac
QED

Definition typed_copy_entry_def:
  typed_copy_entry cenv ctx dty sty dtv stv v <=>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) ==>
      frag_exec ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t)
        (\r. F)
End

Definition typed_copy_entries_def:
  (typed_copy_entries cenv ctx [] stys dtvs stvs vs <=>
     stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []) /\
  (typed_copy_entries cenv ctx (dty::dtys) stys dtvs stvs vs <=>
     case (stys,dtvs,stvs,vs) of
       (sty::stys,dtv::dtvs,stv::stvs,v::vs) =>
         type_memory_bytes cenv dty = type_memory_size dtv /\
         type_memory_bytes cenv sty = type_memory_size stv /\
         typed_copy_entry cenv ctx dty sty dtv stv v /\
         typed_copy_entries cenv ctx dtys stys dtvs stvs vs
     | _ => F)
End

Theorem typed_copy_entries_nil[simp]:
  typed_copy_entries cenv ctx [] stys dtvs stvs vs <=>
  stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []
Proof
  simp[typed_copy_entries_def]
QED

Theorem typed_copy_entries_cons[simp]:
  typed_copy_entries cenv ctx (dty::dtys) (sty::stys)
    (dtv::dtvs) (stv::stvs) (v::vs) <=>
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  typed_copy_entry cenv ctx dty sty dtv stv v /\
  typed_copy_entries cenv ctx dtys stys dtvs stvs vs
Proof
  simp[typed_copy_entries_def]
QED

Theorem typed_copy_entries_lengths:
  !dtys stys dtvs stvs vs.
    typed_copy_entries cenv ctx dtys stys dtvs stvs vs ==>
    LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs
Proof
  Induct >> simp[typed_copy_entries_def] >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[typed_copy_entries_def] >> metis_tac[]
QED

Theorem typed_copy_state_frame_mono:
  ci_mono sa sb /\ typed_copy_state_frame sb off len s t ==>
  typed_copy_state_frame sa off len s t
Proof
  rw[ci_mono_def, typed_copy_state_frame_def] >>
  first_x_assum irule >>
  gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem typed_copy_tuple_mem_agree:
  LENGTH vs = LENGTH tvs /\ tuple_val_wf vs tvs /\
  tuple_in_memory vs tvs off mem /\
  mem_bytes_at off (type_memory_size_list tvs) mem =
    mem_bytes_at off (type_memory_size_list tvs) mem' ==>
  tuple_in_memory vs tvs off mem'
Proof
  rpt strip_tac >> irule (cj 5 val_in_memory_mem_agree_proof) >>
  simp[] >> qexists_tac `mem` >> simp[]
QED

Theorem typed_copy_tuple_frame:
  LENGTH vs = LENGTH tvs /\ tuple_val_wf vs tvs /\
  tuple_in_memory vs tvs off mem /\ typed_copy_frame dst len mem mem' /\
  (off + type_memory_size_list tvs <= dst \/ dst + len <= off) ==>
  tuple_in_memory vs tvs off mem'
Proof
  rpt strip_tac >> irule typed_copy_tuple_mem_agree >>
  simp[] >> qexists_tac `mem` >> gvs[typed_copy_frame_def] >>
  metis_tac[]
QED

Theorem typed_copy_entry_offset_frag:
  !cenv ctx dty sty dtv stv v dst src doff soff sa s1 s2 sb dp sp s dw sw.
  typed_copy_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
         typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t)
    (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by metis_tac[typed_copy_offset_mono] >>
  `ci_mono s2 sb` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s1 sb /\ cs_extends s2 sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x)` by
    metis_tac[typed_copy_offset_fresh, typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac typed_copy_offset_frag) >>
  disch_then (drule_at Any) >>
  disch_then (qspecl_then [`ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >>
  simp[] >> rpt strip_tac >>
  `eval_operand src t = SOME sw` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  qpat_assum `compile_with_byte_offset src _ _ = _`
    (mp_then Any mp_tac typed_copy_offset_frag) >>
  disch_then (drule_at Any) >>
  disch_then (qspecl_then [`ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >>
  simp[ci_mono_def] >> rpt strip_tac >>
  `eval_operand dp t' = SOME (dw + n2w doff)` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  qpat_x_assum `typed_copy_entry _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [typed_copy_entry_def]) >>
  disch_then drule >>
  disch_then (qspecl_then [`t'`, `dw + n2w doff`, `sw + n2w soff`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[ADD_COMM]) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
  irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t'` >> simp[] >>
  metis_tac[typed_copy_state_frame_mono]
QED

Theorem typed_copy_tuple_frag:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw.
    typed_copy_entries cenv ctx dtys stys dtvs stvs vs /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) ==>
    frag_exec ctx sa sb (\u. u = s)
      (\t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw + doff)
             (type_memory_size_list dtvs) s t) (\r. F)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[typed_copy_entries_def, compile_store_memory_typed_def,
          comp_return_def, val_in_memory_def, type_memory_size_def] >>
      irule frag_exec_refl >> simp[]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[typed_copy_entries_def] >>
  rename1 `typed_copy_entry cenv ctx dty sty dtv stv v` >>
  rename1 `typed_copy_entries cenv ctx dtys stys dtvs stvs vs` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dst_ptr dty src_ptr sty cs'' = (u,sc)` >>
  Cases_on `u` >> suspend "cons"
QED

Resume typed_copy_tuple_frag[cons]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs''` by metis_tac[typed_copy_offset_mono] >>
     `ci_mono cs'' sc` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
     `ci_mono sc sb` by metis_tac[cj 2 ci_mono_typed_memory_family, SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
      typed_copy_entry_offset_frag) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (mp_then Any irule frag_exec_then) >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  simp[] >> rpt strip_tac >>
  suspend "suffix"
QED

Resume typed_copy_tuple_frag[suffix]:
  `LENGTH vs = LENGTH stvs` by metis_tac[typed_copy_entries_lengths] >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `typed_copy_entry _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  disch_then (mp_then Any irule frag_exec_conseq) >>
  simp[] >> rpt strip_tac
  >- suspend "preserve_head" >>
  suspend "frames"
QED

Resume typed_copy_tuple_frag[preserve_head]:
  irule typed_copy_frame_preserves_source >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size_list dtvs`,
    `doff + (type_memory_size dtv + w2n dw)`, `t.vs_memory`] >>
  fs[typed_copy_state_frame_def] >> decide_tac
QED

Resume typed_copy_tuple_frag[frames]:
  irule typed_copy_state_frame_trans >> qexists_tac `t` >>
  conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`] >>
      simp[]) >>
  irule typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`doff + (type_memory_size dtv + w2n dw)`,
    `type_memory_size_list dtvs`] >> simp[]
QED

Finalise typed_copy_tuple_frag

Theorem typed_copy_struct_fields_producer:
  !fs full cenv dst src doff soff.
    ALL_DISTINCT (MAP FST full) /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full /\
    EVERY (\f. MEM f full) fs ==>
    compile_struct_typed_copy cenv dst src fs full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (\(name,ty,sz). ty) fs) (MAP (\(name,ty,sz). ty) fs) doff soff
Proof
  Induct
  >- simp[compile_store_memory_typed_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[EVERY_DEF] >> strip_tac >>
  `ALOOKUP full h0 = SOME (h1,h2)` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> gvs[]) >>
  `h2 = type_memory_bytes cenv h1` by
    (gvs[EVERY_MEM] >>
     qpat_x_assum `!e. MEM e full ==> _` (qspec_then `(h0,h1,h2)` mp_tac) >> simp[]) >>
  simp[Once compile_store_memory_typed_def] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  simp[]
QED

Theorem typed_copy_struct_suffix_producer:
  ALL_DISTINCT (MAP FST full) /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full ==>
  !n dst src doff soff.
    compile_struct_typed_copy cenv dst src (DROP n full) full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (\(name,ty,sz). ty) (DROP n full))
      (MAP (\(name,ty,sz). ty) (DROP n full)) doff soff
Proof
  rpt strip_tac >> irule typed_copy_struct_fields_producer >>
  simp[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

Theorem typed_copy_fields_tuple_zip:
  !names vs tvs off mem.
    LENGTH names = LENGTH vs /\ LENGTH names = LENGTH tvs ==>
    (fields_in_memory (ZIP(names,vs)) (ZIP(names,tvs)) off mem <=>
     tuple_in_memory vs tvs off mem)
Proof
  Induct >> Cases_on `vs` >> Cases_on `tvs` >>
  simp[val_in_memory_def]
QED

Theorem typed_copy_struct_suffix_frag:
  !n tvs vs dst src doff soff sa sb s dw sw.
    ALL_DISTINCT (MAP FST full) /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full /\
    typed_copy_entries cenv ctx
      (MAP (\(name,ty,sz). ty) (DROP n full))
      (MAP (\(name,ty,sz). ty) (DROP n full)) tvs tvs vs /\
    tuple_val_wf vs tvs /\
    compile_struct_typed_copy cenv dst src (DROP n full) full doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs tvs (w2n sw + soff) s.vs_memory /\
    w2n sw + soff + type_memory_size_list tvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list tvs < dimword (:256) /\
    (w2n sw + soff + type_memory_size_list tvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list tvs <= w2n sw + soff) ==>
    frag_exec ctx sa sb (\u. u = s)
      (\t. tuple_in_memory vs tvs (w2n dw + doff) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw + doff)
             (type_memory_size_list tvs) s t) (\r. F)
Proof
  rpt strip_tac >>
  drule_all typed_copy_struct_suffix_producer >> strip_tac >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule typed_copy_tuple_frag >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >> simp[]
QED

Definition typed_copy_index_prefix_def:
  typed_copy_index_prefix f tv off N k mem <=>
    k <= N /\ (!i. i < k ==>
      val_in_memory tv (f i) (off + i * type_memory_size tv) mem)
End

Theorem typed_copy_index_prefix_zero[simp]:
  typed_copy_index_prefix f tv off N 0 mem
Proof
  simp[typed_copy_index_prefix_def]
QED

Theorem typed_copy_index_prefix_step:
  typed_copy_index_prefix f tv off N k mem /\ k < N /\
  val_in_memory tv (f k) (off + k * type_memory_size tv) mem ==>
  typed_copy_index_prefix f tv off N (SUC k) mem
Proof
  rw[typed_copy_index_prefix_def] >> Cases_on `i = k` >> gvs[]
QED

Theorem typed_copy_index_prefix_complete:
  typed_copy_index_prefix f tv off N N mem <=>
  !i. i < N ==> val_in_memory tv (f i) (off + i * type_memory_size tv) mem
Proof
  simp[typed_copy_index_prefix_def]
QED

Theorem typed_copy_index_prefix_frame:
  typed_copy_index_prefix f tv off N k mem /\
  (!i. i < N ==> val_wf tv (f i)) /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_index_prefix f tv off N k mem'
Proof
  rw[typed_copy_index_prefix_def] >>
  irule typed_copy_frame_preserves_source >> conj_tac
  >- (first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`len`, `off + k * type_memory_size tv`, `mem`] >>
  simp[] >> disj1_tac >> drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]
QED

Theorem typed_copy_state_frame_jump:
  typed_copy_state_frame sa off len s t ==>
  typed_copy_state_frame sa off len s (jump_to l t)
Proof
  simp[typed_copy_state_frame_def, jump_to_def, lookup_var_def]
QED

Theorem typed_copy_eval_operand_jump[simp]:
  eval_operand opnd (jump_to l t) = eval_operand opnd t
Proof
  Cases_on `opnd` >> simp[eval_operand_def, jump_to_def, lookup_var_def]
QED

Theorem typed_copy_lookup_var_jump[simp]:
  lookup_var x (jump_to l t) = lookup_var x t
Proof
  simp[jump_to_def, lookup_var_def]
QED

Theorem typed_copy_sarray_bulk_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
  ~is_abi_dynamic cenv.ce_struct_fields dty /\
  type_memory_bytes cenv dty = ds /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N * ds < dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= N * ds /\ N * ds <= type_memory_size tv ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory tv v (w2n dw) t.vs_memory /\
         typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t) (\r. F)
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  irule typed_copy_fixed_frag >> simp[] >>
  qexistsl_tac [`sw`, `dst`, `N * ds`, `src`] >> simp[]
QED

(* Pure emitted operations expose their result without any source-language
   simulation invariant.  The semantic premise is just the single step. *)
Theorem typed_copy_emit_op_frag:
  !ctx opc args a op b s w off len.
    emit_op opc args a = (op,b) /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
           OK (update_var out w s)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, run_inst_seq_def] >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_emit_op_mono:
  emit_op opc args a = (op,b) ==> ci_mono a b
Proof
  strip_tac >> qspecl_then [`opc`, `args`, `a`] mp_tac ci_mono_emit_op >> simp[]
QED

Theorem typed_copy_header_frag:
  !ctx counter N k a lt b done c s off len.
    emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
    emit_op ISZERO [lt] b = (done,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    k <= N /\ N < dimword (:256) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand done t = SOME (if k < N then 0w else 1w) /\
           t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand lt t = SOME (bool_to_word (k < N)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, w2n_n2w, LESS_MOD]) >>
  drule frag_exec_then >> disch_then irule >>
  simp[emit_op_extends] >> conj_tac
  >- (rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
         (\u. eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
              u.vs_memory = t.vs_memory /\
              typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def, exec_pure1_def]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >>
      simp[] >> rpt strip_tac >>
      fs[bool_to_word_def] >> Cases_on `k < N` >> gvs[] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[typed_copy_emit_op_mono]) >>
  metis_tac[typed_copy_emit_op_mono, ci_mono_def]
QED

Theorem typed_copy_assign_frag:
  !ctx op counter a b s w.
    emit_inst ASSIGN [op] [counter] a = ((),b) /\
    eval_operand op s = SOME w ==>
    frag_exec ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. x <> counter ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, venomInstTheory.is_terminator_def] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  simp[lookup_var_update_var, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_counter_increment_frag:
  !ctx counter k a inc b c s.
    emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
    emit_inst ASSIGN [inc] [counter] b = ((),c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    k + 1 < dimword (:256) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
        t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. not_fresh_at a x /\ x <> counter ==>
             lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand inc t = SOME (n2w (k + 1)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a 0 0 s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> fs[] >> drule_all typed_copy_assign_frag >>
      disch_then (qspec_then `ctx` mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >>
      simp[] >> rpt strip_tac >>
      gvs[typed_copy_state_frame_def, venom_state_component_equality]) >>
  `ci_mono a b` by metis_tac[typed_copy_emit_op_mono] >>
  qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `b`] mp_tac ci_mono_emit_inst >>
  simp[] >> gvs[ci_mono_def]
QED

Theorem typed_copy_counter_init_frag:
  !ctx counter a b s off len.
    emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
    (!x. not_fresh_at a x ==> x <> counter) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME 0w /\ t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all typed_copy_assign_frag >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >>
  simp[typed_copy_state_frame_def] >> rpt strip_tac >> simp[]
QED

Theorem typed_copy_emit_op_fresh:
  emit_op opc args a = (op,b) ==>
  (!x. op = Var x ==> not_fresh_at b x)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       emit_def, emit_inst_def, fresh_id_def, comp_return_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem typed_copy_two_ops_frag:
  !ctx opc1 args1 opc2 args2 a op1 b op2 c s w1 w2 off len.
    emit_op opc1 args1 a = (op1,b) /\ emit_op opc2 args2 b = (op2,c) /\
    opc1 <> INVOKE /\ ~is_terminator opc1 /\
    opc2 <> INVOKE /\ ~is_terminator opc2 /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc1 args1 [out]) s =
           OK (update_var out w1 s)) /\
    (!t out. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t ==>
       step_inst_base (mk_inst b.cs_next_id opc2 args2 [out]) t =
       OK (update_var out w2 t)) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand op1 t = SOME w1 /\ eval_operand op2 t = SOME w2 /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `!x. op1 = Var x ==> not_fresh_at b x` by metis_tac[typed_copy_emit_op_fresh] >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand op1 t = SOME w1 /\ t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> goal_assum (drule_at Any) >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
        (\u. eval_operand op2 u = SOME w2 /\ u.vs_memory = t.vs_memory /\
             typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag >> qexistsl_tac [`args2`, `opc2`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt gen_tac >> strip_tac >>
      conj_tac
      >- metis_tac[typed_copy_state_frame_operand] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_index_offsets_frag:
  !ctx counter ss ds a so b doff c s k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand so t = SOME (n2w (k * ss)) /\
           eval_operand doff t = SOME (n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule typed_copy_two_ops_frag >>
  qexistsl_tac [`[Var counter; Lit (n2w ss)]`, `[Var counter; Lit (n2w ds)]`,
               `b`, `MUL`, `MUL`] >>
  simp[venomInstTheory.is_terminator_def] >> conj_tac
  >- (rewrite_tac[GSYM word_mul_n2w] >> rpt gen_tac >> irule step_MUL >>
      simp[eval_operand_def]) >>
  rpt strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[typed_copy_state_frame_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[word_mul_n2w]
QED

Theorem typed_copy_index_adds_frag:
  !ctx src dst so doff sw dw sv dv a sp b dp c s off len.
    emit_op ADD [src;so] a = (sp,b) /\
    emit_op ADD [dst;doff] b = (dp,c) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    (!x. doff = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    eval_operand so s = SOME sv /\ eval_operand doff s = SOME dv ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + sv) /\
           eval_operand dp t = SOME (dw + dv) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule typed_copy_two_ops_frag >>
  qexistsl_tac [`[src;so]`, `[dst;doff]`, `b`, `ADD`, `ADD`] >>
  conj_tac
  >- (gen_tac >> rewrite_tac[mk_inst_def, step_inst_base_def] >>
      simp[exec_pure2_def]) >>
  simp[venomInstTheory.is_terminator_def] >> rpt strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand doff t = SOME dv` by
    metis_tac[typed_copy_state_frame_operand] >>
  rewrite_tac[mk_inst_def, step_inst_base_def] >> simp[exec_pure2_def]
QED

Theorem typed_copy_index_addresses_frag:
  !ctx counter ss ds src dst a so b doff c sp d dp e s sw dw k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    (!x. src = Var x ==> not_fresh_at a x) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
    frag_exec ctx a e (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + n2w (k * ss)) /\
           eval_operand dp t = SOME (dw + n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all typed_copy_index_offsets_frag >>
  disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `!x. dst = Var x ==> not_fresh_at c x` by
        metis_tac[typed_copy_operand_fresh_mono] >>
      `!x. doff = Var x ==> not_fresh_at c x` by
        metis_tac[typed_copy_emit_op_fresh] >>
      drule_all typed_copy_index_adds_frag >>
      disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >> irule typed_copy_state_frame_trans >>
      qexists_tac `t` >> simp[] >> irule typed_copy_state_frame_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_index_child_frag:
  !cenv ctx dty sty dtv stv v counter src dst a so b doff c sp d dp e z s sw dw k.
    emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
    compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
    typed_copy_entry cenv ctx dty sty dtv stv v /\ not_fresh_at a counter /\
    (!x. src = Var x ==> not_fresh_at a x) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    lookup_var counter s = SOME (n2w k) /\ k < dimword (:256) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
    w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
    w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
    (w2n sw + k * type_memory_size stv + type_memory_size stv <=
       w2n dw + k * type_memory_size dtv \/
     w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
       w2n sw + k * type_memory_size stv) ==>
    frag_exec ctx a z (\u. u = s)
      (\t. val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono e z` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv /\
   w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_index_addresses_frag >>
  disch_then (qspecl_then [`ctx`, `w2n dw + k * type_memory_size dtv`,
                                    `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `typed_copy_entry _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [typed_copy_entry_def]) >>
      disch_then drule >>
      disch_then (qspecl_then [`t`, `dw + n2w (k * type_memory_size dtv)`,
                                     `sw + n2w (k * type_memory_size stv)`] mp_tac) >>
      simp[] >> disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >> irule typed_copy_state_frame_trans >> qexists_tac `t` >>
      simp[] >> irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

(* In particular, indexed-child execution preserves the loop counter: it
   was already old at the start of address generation. *)
Theorem typed_copy_state_frame_counter:
  typed_copy_state_frame a off len s t /\ not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) ==>
  lookup_var counter t = SOME (n2w k)
Proof
  simp[typed_copy_state_frame_def]
QED

(* Position-independent header invariant for the indexed typed-copy loop. *)
Definition typed_copy_index_inv_def:
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t <=>
    k <= N /\ lookup_var counter t = SOME (n2w k) /\
    eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw /\
    (!i. i < N ==> val_in_memory stv (f i)
      (w2n sw + i * type_memory_size stv) t.vs_memory) /\
    typed_copy_index_prefix f dtv (w2n dw) N k t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s0 t
End

Theorem typed_copy_index_inv_jump:
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t ==>
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k (jump_to l t)
Proof
  simp[typed_copy_index_inv_def, jump_to_def, typed_copy_state_frame_jump]
QED

Theorem typed_copy_index_source_frame:
  (!i. i < N ==> val_in_memory stv (f i) (so + i * type_memory_size stv) mem /\
                     val_wf stv (f i)) /\
  k < N /\ (so + N * type_memory_size stv <= dst \/
             dst + N * type_memory_size dtv <= so) /\
  typed_copy_frame (dst + k * type_memory_size dtv) (type_memory_size dtv) mem mem' ==>
  !i. i < N ==> val_in_memory stv (f i) (so + i * type_memory_size stv) mem'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qx_gen_tac `i` >> strip_tac >>
  irule typed_copy_frame_preserves_source >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`type_memory_size dtv`, `dst + k * type_memory_size dtv`, `mem`] >>
  simp[] >>
  `so <= so + i * type_memory_size stv /\
   so + i * type_memory_size stv + type_memory_size stv <=
     so + N * type_memory_size stv` by metis_tac[typed_copy_array_subinterval] >>
  `dst <= dst + k * type_memory_size dtv /\
   dst + k * type_memory_size dtv + type_memory_size dtv <=
     dst + N * type_memory_size dtv` by metis_tac[typed_copy_array_subinterval] >>
  decide_tac
QED

Theorem typed_copy_index_inv_step:
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  k < N /\ (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
    (type_memory_size dtv) s t /\
  val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
  lookup_var counter t = SOME (n2w (SUC k)) /\
  eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw ==>
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `typed_copy_index_inv _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[typed_copy_index_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `typed_copy_frame (w2n dw + k * type_memory_size dtv)
      (type_memory_size dtv) s.vs_memory t.vs_memory` by
    gvs[typed_copy_state_frame_def] >>
  pure_rewrite_tac[typed_copy_index_inv_def] >> rpt conj_tac
  >- decide_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (rpt strip_tac >> irule typed_copy_index_source_frame >>
      qexistsl_tac [`N`, `w2n dw`, `dtv`, `k`, `s.vs_memory`] >> simp[]) 
  >- (irule typed_copy_index_prefix_step >> simp[] >>
      irule typed_copy_index_prefix_frame >> conj_tac
      >- simp[] >>
      qexistsl_tac [`type_memory_size dtv`, `s.vs_memory`] >> simp[]) >>
  irule typed_copy_state_frame_trans >> qexists_tac `s` >> simp[] >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n dw + k * type_memory_size dtv`, `type_memory_size dtv`] >>
  simp[] >>
  drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`w2n dw`, `type_memory_size dtv`] mp_tac) >>
  decide_tac
QED

Theorem typed_copy_counter_increment_frame_frag:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  ci_mono sa a /\ ~not_fresh_at sa counter /\ not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) /\ k + 1 < dimword (:256) ==>
  frag_exec ctx a c (\u. u = s)
    (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
         t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa off len s t) (\r. F)
Proof
  rpt strip_tac >> drule_all typed_copy_counter_increment_frag >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> simp[typed_copy_state_frame_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[ci_mono_def, not_fresh_at_def] >> decide_tac
QED

Theorem typed_copy_index_body_frag:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx a endst
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k)) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z` by
    metis_tac[typed_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family, SND] >>
  `ci_mono z z1` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono z1 endst` by
    (qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `z1`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono a z /\ ci_mono sa z /\ ci_mono z endst` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     conj_tac >> metis_tac[typed_copy_operand_fresh_mono]) >>
  `w2n sw <= w2n sw + k * type_memory_size stv /\
   w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n sw + N * type_memory_size stv` by metis_tac[typed_copy_array_subinterval] >>
  `w2n dw <= w2n dw + k * type_memory_size dtv /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by metis_tac[typed_copy_array_subinterval] >>
  irule frag_exec_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `lookup_var counter s = SOME (n2w k) /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
   val_in_memory stv (f k) (w2n sw + k * type_memory_size stv) s.vs_memory` by
    gvs[typed_copy_index_inv_def] >>
  `k < dimword (:256) /\ k + 1 < dimword (:256)` by decide_tac >>
  `typed_copy_entry cenv ctx dty sty dtv stv (f k)` by metis_tac[] >>
  `w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `frag_exec ctx a z (\u. u = s)
     (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
          typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
            (type_memory_size dtv) s t) (\r. F)` by
    (irule typed_copy_index_child_frag >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     qexists_tac `sw` >> simp[] >> decide_tac) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `lookup_var counter t = SOME (n2w k)` by
        metis_tac[typed_copy_state_frame_counter] >>
      drule_all typed_copy_counter_increment_frame_frag >>
      disch_then (qspecl_then [`w2n dw + k * type_memory_size dtv`,
                                    `type_memory_size dtv`, `ctx`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >>
      `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s t` by
        (irule typed_copy_state_frame_mono >> qexists_tac `a` >> simp[]) >>
      `eval_operand src s'' = SOME sw /\ eval_operand dst s'' = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      irule typed_copy_index_inv_step >> simp[ADD1] >>
      qexists_tac `s` >> simp[] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_index_inv_preserve:
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  typed_copy_state_frame a off len s t /\ t.vs_memory = s.vs_memory ==>
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `typed_copy_index_inv _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[typed_copy_index_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `lookup_var counter t = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  simp[typed_copy_index_inv_def] >>
  irule typed_copy_state_frame_trans >> qexists_tac `s` >> simp[] >>
  irule typed_copy_state_frame_mono >> qexists_tac `a` >> simp[] >>
  gvs[typed_copy_state_frame_def]
QED

Theorem typed_copy_index_header_frag:
  emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\ N < dimword (:256) ==>
  frag_exec ctx a c
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  drule_all typed_copy_header_frag >>
  disch_then (qspecl_then [`ctx`, `w2n dw`, `N * type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> irule typed_copy_index_inv_preserve >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem typed_copy_sarray_slow_layout:
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) ==>
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\ not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks
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
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono b4 b5` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono sa l3` by metis_tac[] >>
  `ci_mono sa init /\ ci_mono st0 sth /\ ci_mono sth st2` by metis_tac[] >>
  `ci_mono sa st0 /\ ci_mono sth stb /\ ci_mono stb b4` by metis_tac[] >>
  `ci_mono sa sth /\ ci_mono stb b6 /\ ci_mono ste stx` by metis_tac[] >>
  `ci_mono sa stb /\ ci_mono stb ste /\ ci_mono st0 stb` by metis_tac[] >>
  `ci_mono st0 stx /\ ci_mono sth stj` by metis_tac[] >>
  qpat_x_assum `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` kall_tac >>
  simp[] >>
  `cs_extends sth stj /\ cs_extends stb ste` by metis_tac[ci_mono_def] >>
  simp[] >>
  `~not_fresh_at sa counter /\ not_fresh_at init counter /\
   sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  simp[] >> gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem typed_copy_index_init_frag:
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec ctx sa st0 (\u. u = s)
    (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)
Proof
  rpt strip_tac >>
  `~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `frag_exec ctx init st0 (\u. u = s)
     (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)` by
    (drule_all typed_copy_assign_frag >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var counter t = SOME 0w` >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
       (simp[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
     `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
       metis_tac[typed_copy_state_frame_operand] >>
     simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def, fn_has_code_def, emitted_blocks_def]
QED

Theorem typed_copy_sarray_slow_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\
  N < dimword (:256) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
         typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_sa_cond" sa = (hdr,l1)` >>
  rename1 `fresh_label "typed_sa_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2)` >>
  rename1 `emit_op ADD [src;so] b2 = (sp,b3)` >>
  rename1 `emit_op ADD [dst;doff] b3 = (dp,b4)` >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5)` >>
  rename1 `emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6)` >>
  rename1 `emit_inst ASSIGN [inc] [counter] b6 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa stx P Q R` >>
  qabbrev_tac `Inv = typed_copy_index_inv sa counter src dst sw dw f stv dtv N s` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  `frag_exec ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule typed_copy_index_init_frag >> simp[] >>
     goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_exit" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_body" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_cond" _ = _`)) >> simp[]) >>
  `frag_exec ctx st0 stx (Inv 0) (J N) R` by
    (irule frag_exec_loop >> conj_tac
     >- simp[Abbr `Inv`, typed_copy_index_inv_jump] >>
     conj_tac
     >- simp[Abbr `J`, Abbr `Inv`, typed_copy_index_inv_jump,
             typed_copy_eval_operand_jump] >>
     qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
     goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
     goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
     rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
     qpat_x_assum `fresh_var _ = _` kall_tac >>
     rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
     rpt (qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac) >>
     qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
     conj_tac
     >- (simp[Abbr `J`] >> rpt strip_tac >>
         Cases_on `k < N` >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
         drule_all typed_copy_index_body_frag >>
         disch_then (qspec_then `s` mp_tac) >>
         disch_then (mp_then Any irule frag_exec_conseq) >> simp[]) >>
     rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
     irule typed_copy_index_header_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]) >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_seq >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_index_inv_def,
       typed_copy_index_prefix_complete]
QED

Theorem typed_copy_sarray_cond_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N < dimword (:256) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  type_memory_size tv = N * type_memory_size dtv /\
  ((type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) ==>
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= N * type_memory_size dtv) /\
  (~(type_memory_size dtv = type_memory_size stv /\
     ~is_abi_dynamic cenv.ce_struct_fields dty) ==>
    (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
      val_wf stv (f i) /\ val_wf dtv (f i) /\
      val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) s.vs_memory) /\
    (!mem. (!i. i < N ==> val_in_memory dtv (f i)
      (w2n dw + i * type_memory_size dtv) mem) ==>
      val_in_memory tv v (w2n dw) mem)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- (irule typed_copy_sarray_bulk_frag >>
      simp[] >>
      goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
      gvs[] >> decide_tac) >>
  `frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)` by
    (irule typed_copy_sarray_slow_frag >>
     simp[] >>
     goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
     qexists_tac `stv` >> simp[] >> metis_tac[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> metis_tac[]
QED

Theorem typed_copy_default_widening:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  default_value stv = default_value dtv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[cj 1 arg_type_fits_default_value]
QED

Theorem typed_copy_sarray_representation:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) off mem ==>
  (!i. i < N ==>
    val_wf stv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v) /\
    val_wf dtv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v) /\
    val_in_memory stv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
      (off + i * type_memory_size stv) mem) /\
  (!mem' dstoff.
    (!i. i < N ==> val_in_memory dtv
      (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
      (dstoff + i * type_memory_size dtv) mem') ==>
    val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) dstoff mem')
Proof
  strip_tac >> drule_all typed_copy_default_widening >> strip_tac >>
  conj_tac
  >- (rpt strip_tac
      >- (irule typed_copy_sparse_lookup_wf >> qexists_tac `N` >> fs[val_wf_def])
      >- (asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
          qexists_tac `N` >> fs[val_wf_def])
      >> metis_tac[typed_copy_sarray_element]) >>
  rpt strip_tac >> irule typed_copy_sarray_indexed >> gvs[]
QED

Theorem typed_copy_sarray_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv
     (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N < dimword (:256) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
       (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `type_memory_size (ArrayTV dtv (Fixed N)) = N * type_memory_size dtv` by
    simp[type_memory_size_def] >>
  `frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
       (w2n dw) t.vs_memory /\ typed_copy_state_frame sa (w2n dw)
       (type_memory_size (ArrayTV dtv (Fixed N))) s t) (\r. F)` suffices_by simp[] >>
  irule typed_copy_sarray_cond_frag >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`dtv`,
    `\i. case ALOOKUP kvs i of NONE => default_value stv | SOME v => v`, `stv`, `sw`] >>
  simp[] >> conj_tac
  >- (strip_tac >> drule_all typed_copy_sarray_representation >>
      strip_tac >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` (SUBST_ALL_TAC o SYM) >>
  simp[loweringPostsTheory.val_footprint_def, type_memory_size_def]
QED

Theorem typed_copy_dynarray_mload_step:
  eval_operand src s = SOME sw /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory ==>
  step_inst_base (mk_inst id MLOAD [src] [out]) s =
    OK (update_var out (n2w (LENGTH vs)) s)
Proof
  strip_tac >> fs[val_in_memory_def] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
       GSYM mem_word_at_eq_mload]
QED

Theorem typed_copy_mstore_state_frame:
  typed_copy_state_frame a off 32 s ((mstore off w s) with vs_inst_idx := idx)
Proof
  simp[typed_copy_state_frame_def] >> conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def, venom_state_component_equality] >>
  conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, MAX_DEF]
QED

Theorem typed_copy_mstore_frag:
  emit_void MSTORE [dst; value] a = ((),b) /\
  eval_operand dst s = SOME dw /\ eval_operand value s = SOME w ==>
  frag_exec ctx a b (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, venomInstTheory.is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_write2_def] >>
  simp[mstore_mem_word_at_same, typed_copy_mstore_state_frame]
QED

Theorem typed_copy_assert_frag:
  emit_void ASSERT [ok] a = ((),b) /\ eval_operand ok s = SOME 1w ==>
  frag_exec ctx a b (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, venomInstTheory.is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs] >>
  simp[typed_copy_state_frame_def, lookup_var_def, venom_state_component_equality]
QED

Theorem typed_copy_dyn_check_frag:
  emit_op GT [length; Lit (n2w C)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  emit_void ASSERT [ok] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\ N <= C /\ C < dimword (:256) ==>
  frag_exec ctx a d (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >>
  `N < dimword (:256)` by decide_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono c d` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand too_long t = SOME 0w /\ t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def] >>
     simp[NOT_LESS]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
         (\u. eval_operand ok u = SOME 1w /\ u.vs_memory = t.vs_memory /\
              typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
              exec_pure1_def, bool_to_word_def]) >>
      drule frag_exec_then >> disch_then irule >> conj_tac
      >- (simp[] >> rpt strip_tac >> drule_all typed_copy_assert_frag >>
          disch_then (qspecl_then [`off`, `len`, `ctx`] mp_tac) >>
          disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
          rpt strip_tac >>
          metis_tac[typed_copy_state_frame_trans, typed_copy_state_frame_mono]) >>
      gvs[ci_mono_def]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_data_frag:
  emit_void MSTORE [dst; length] a = ((),b) /\
  emit_op ADD [src; Lit 32w] b = (sd,c) /\
  emit_op ADD [dst; Lit 32w] c = (dd,d) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME w ==>
  frag_exec ctx a d (\u. u = s)
    (\t. eval_operand length t = SOME w /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >>
  `ci_mono a b` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono b c /\ ci_mono c d` by metis_tac[typed_copy_emit_op_mono] >>
  drule_all typed_copy_mstore_frag >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `frag_exec ctx b d (\u. u = t)
         (\u. eval_operand sd u = SOME (sw + 32w) /\
           eval_operand dd u = SOME (dw + 32w) /\ u.vs_memory = t.vs_memory /\
           typed_copy_state_frame b (w2n dw) 32 t u) (\r. F)` by
        (irule typed_copy_index_adds_frag >> simp[eval_operand_def] >>
         goal_assum (drule_at (Pat `emit_op ADD _ b = _`)) >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl_tac [`Lit 32w`, `src`] >> simp[eval_operand_def] >>
         metis_tac[typed_copy_operand_fresh_mono]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- (drule_all typed_copy_state_frame_mono >> strip_tac >>
          metis_tac[typed_copy_state_frame_operand]) >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_read_check_frag:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  N <= C /\ C < dimword (:256) /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) ==>
  frag_exec ctx a e (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono d e` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  `frag_exec ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      drule_all typed_copy_dyn_check_frag >>
      disch_then (qspecl_then [`off`, `len`, `ctx`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- metis_tac[typed_copy_state_frame_operand] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_prefix_mono:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) ==>
  ci_mono a a4 /\ ci_mono a1 a4 /\ ci_mono a4 b /\ ci_mono a b /\
  (!x. length = Var x ==> not_fresh_at a4 x) /\
  (!x. length = Var x ==> not_fresh_at b x) /\
  (!x. sd = Var x ==> not_fresh_at b x) /\
  (!x. dd = Var x ==> not_fresh_at b x)
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3 /\
   ci_mono a5 a6 /\ ci_mono a6 b` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a3 a4 /\ ci_mono a4 a5` by
    metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono a1 a4 /\ ci_mono a4 b` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono a a4 /\ ci_mono a b` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `(!x. length = Var x ==> not_fresh_at a1 x) /\
   (!x. sd = Var x ==> not_fresh_at a6 x) /\
   (!x. dd = Var x ==> not_fresh_at b x)` by
    metis_tac[typed_copy_emit_op_fresh] >>
  simp[] >> metis_tac[typed_copy_operand_fresh_mono]
QED

Theorem typed_copy_dyn_prefix_frag:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N <= C /\ C < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) ==>
  frag_exec ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w N : bytes32) T /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `frag_exec ctx a a4 (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)` by
    (irule typed_copy_dyn_read_check_frag >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `frag_exec ctx a4 b (\u. u = t)
        (\u. eval_operand length u = SOME (n2w N) /\
          eval_operand sd u = SOME (sw + 32w) /\ eval_operand dd u = SOME (dw + 32w) /\
          mem_word_at (w2n dw) u.vs_memory = n2w N /\
          typed_copy_state_frame a4 (w2n dw) 32 t u) (\r. F)` by
        (irule typed_copy_dyn_data_frag >> simp[] >>
         goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
         goal_assum (drule_at (Pat `emit_op ADD _ a5 = _`)) >>
         goal_assum (drule_at Any) >> simp[] >>
         metis_tac[typed_copy_operand_fresh_mono]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- (rename1 `mem_bytes_at (w2n dw) 32 u.vs_memory` >>
          `mem_bytes_at (w2n dw) 32 u.vs_memory =
             word_to_bytes (mem_word_at (w2n dw) u.vs_memory) T` suffices_by simp[] >>
          simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >> irule EQ_SYM >>
          irule venomMemPropsTheory.word_bytes_roundtrip_256 >> simp[]) >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_runtime_header_frag:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword (:256) ==>
  frag_exec ctx a c (\u. u = s)
    (\t. eval_operand done t = SOME (if k < N then 0w else 1w) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >> `k < dimword (:256)` by decide_tac >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand lt t = SOME (bool_to_word (k < N)) /\
          t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
         (\u. eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
              u.vs_memory = t.vs_memory /\ typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs,
              mk_inst_def, exec_pure1_def]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac >>
      fs[bool_to_word_def] >> Cases_on `k < N` >> gvs[] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[typed_copy_emit_op_mono]) >>
  metis_tac[typed_copy_emit_op_mono, ci_mono_def]
QED

Theorem typed_copy_runtime_index_header_frag:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\ N < dimword (:256) ==>
  frag_exec ctx a c
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N))
    (\t. (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
          eval_operand length t = SOME (n2w N)) /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `s` >> strip_tac >> fs[] >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  `!x. length = Var x ==> not_fresh_at a x` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_runtime_header_frag >>
  disch_then (qspecl_then [`w2n dw`, `N * type_memory_size dtv`, `ctx`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
  >- (irule typed_copy_index_inv_preserve >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[typed_copy_state_frame_operand]
QED

Theorem typed_copy_runtime_index_body_frag:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s0 = SOME (n2w N) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx a endst
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N))
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t /\
         eval_operand length t = SOME (n2w N)) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_index_body_frag >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac >>
  fs[typed_copy_index_inv_def] >> metis_tac[typed_copy_state_frame_operand]
QED

Theorem typed_copy_dynarray_slow_layout:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) ==>
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\ not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa l1 /\ ci_mono l1 l2 /\ ci_mono l2 l3 /\ ci_mono l3 init` by
    metis_tac[ci_mono_fresh_label, ci_mono_fresh_var, SND] >>
  `ci_mono init st0 /\ ci_mono st0 st1 /\ ci_mono stj st2 /\
   ci_mono b6 ste /\ ci_mono ste st3` by
    metis_tac[ci_mono_emit_inst, SND] >>
  `ci_mono st1 sth /\ ci_mono st2 stb /\ ci_mono st3 stx` by
    metis_tac[ci_mono_new_block, SND] >>
  `ci_mono sth h1 /\ ci_mono h1 stj /\ ci_mono stb b1 /\
   ci_mono b1 b2 /\ ci_mono b2 b3 /\ ci_mono b3 b4 /\ ci_mono b5 b6` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono b4 b5` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono sa l3` by metis_tac[] >>
  `ci_mono sa init /\ ci_mono st0 sth /\ ci_mono sth st2` by metis_tac[] >>
  `ci_mono sa st0 /\ ci_mono sth stb /\ ci_mono stb b4` by metis_tac[] >>
  `ci_mono sa sth /\ ci_mono stb b6 /\ ci_mono ste stx` by metis_tac[] >>
  `ci_mono sa stb /\ ci_mono stb ste /\ ci_mono st0 stb` by metis_tac[] >>
  `ci_mono st0 stx /\ ci_mono sth stj` by metis_tac[] >>
  qpat_x_assum `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` kall_tac >>
  simp[] >>
  `cs_extends sth stj /\ cs_extends stb ste` by metis_tac[ci_mono_def] >> simp[] >>
  `~not_fresh_at sa counter /\ not_fresh_at init counter /\
   sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  simp[] >> gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem typed_copy_dynarray_index_init_frag:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec ctx sa st0 (\u. u = s)
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t /\
         eval_operand length t = SOME (n2w N)) (\r. F)
Proof
  strip_tac >>
  `~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `frag_exec ctx init st0 (\u. u = s)
     (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t /\
          eval_operand length t = SOME (n2w N)) (\r. F)` by
    (drule_all typed_copy_assign_frag >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var counter t = SOME 0w` >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
       (simp[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
     `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw /\
      eval_operand length t = SOME (n2w N)` by
       metis_tac[typed_copy_state_frame_operand] >>
     simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def, fn_has_code_def, emitted_blocks_def]
QED

Theorem typed_copy_dynarray_slow_data_frag:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
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
  emit_op ADD [src;so] b2 = (sp,b3) /\ emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx sa stx (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gns[] >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa stx P Q R` >>
  qabbrev_tac `Inv = \k t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s k t /\
                           eval_operand length t = SOME (n2w N)` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  `frag_exec ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule typed_copy_dynarray_index_init_frag >> simp[] >>
     goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_cond" _ = _`)) >> simp[]) >>
  `frag_exec ctx st0 stx (Inv 0) (J N) R` by
    (irule frag_exec_loop >> conj_tac
     >- simp[Abbr `Inv`, typed_copy_index_inv_jump, typed_copy_eval_operand_jump] >>
     conj_tac
     >- simp[Abbr `J`, Abbr `Inv`, typed_copy_index_inv_jump, typed_copy_eval_operand_jump] >>
     qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
     goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
     goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
     rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
     qpat_x_assum `fresh_var _ = _` kall_tac >>
     rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
     rpt (qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac) >>
     qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
     conj_tac
     >- (simp[Abbr `J`] >> rpt strip_tac >> Cases_on `k < N` >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
         drule_all typed_copy_runtime_index_body_frag >>
         disch_then (mp_then Any irule frag_exec_conseq) >> simp[]) >>
     rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
     irule typed_copy_runtime_index_header_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]) >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_seq >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_index_inv_def,
       typed_copy_index_prefix_complete]
QED

Theorem typed_copy_dynarray_slow_data_sizes_frag:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\ emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) ==>
  frag_exec ctx sa stx (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv sty))] stb = (so,b1) /\
   emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dty))] b1 = (doff,b2)` by simp[] >>
  drule_all typed_copy_dynarray_slow_data_frag >> simp[]
QED

Theorem typed_copy_dynarray_bulk_guard:
  dty = sty /\ evaluate_type tenv dty = SOME dtv /\
  evaluate_type tenv sty = SOME stv ==> dtv = stv
Proof
  strip_tac >> gvs[]
QED

Theorem typed_copy_dynarray_bulk_data_frag:
  emit_op MUL [length; Lit (n2w (type_memory_size tv))] sa = (bytes,b) /\
  compile_copy_memory_dynamic dst src bytes b = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (w2n sw + i * type_memory_size tv) s.vs_memory) /\
  w2n sw + N * type_memory_size tv < dimword (:256) /\
  w2n dw + N * type_memory_size tv < dimword (:256) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory tv (f i)
      (w2n dw + i * type_memory_size tv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `N * type_memory_size tv < dimword (:256)` by decide_tac >>
  `frag_exec ctx sa b (\u. u = s)
     (\t. eval_operand bytes t = SOME (n2w (N * type_memory_size tv)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)` by
    (irule typed_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def,
          step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, GSYM word_mul_n2w]) >>
  drule frag_exec_then >> disch_then irule >> simp[emit_op_extends] >>
  conj_tac
  >- (rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      drule_all typed_copy_dynamic_raw_frag >>
      disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >>
      simp[w2n_n2w, LESS_MOD] >>
      conj_tac
      >- (rpt strip_tac >>
          irule valueCopyTheory.val_in_memory_relocate >>
          conj_tac >- metis_tac[] >>
          qexistsl_tac [`w2n sw + i * type_memory_size tv`,
                        `type_memory_size tv`, `t.vs_memory`] >>
          simp[] >> conj_tac
          >- metis_tac[exprSimPropsTheory.val_footprint_le] >>
          irule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
          qexists_tac `N * type_memory_size tv` >>
          simp[mcopy_mem_bytes_at_same] >>
          `SUC i <= N` by decide_tac >>
          `SUC i * type_memory_size tv <= N * type_memory_size tv` by
            simp[arithmeticTheory.LE_MULT_RCANCEL] >>
          qpat_x_assum `SUC i * _ <= _` mp_tac >>
          pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
      irule typed_copy_state_frame_trans >>
      qexists_tac `t` >> simp[typed_copy_mcopy_state_frame]) >>
  conj_tac
  >- (gvs[compile_copy_memory_dynamic_def] >>
      `ci_mono b sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
      gvs[ci_mono_def]) >>
  drule typed_copy_emit_op_mono >> simp[ci_mono_def]
QED

Theorem typed_copy_dynarray_representation:
  val_in_memory (ArrayTV tv (Dynamic C)) (ArrayV (DynArrayV vs)) off mem <=>
  mem_word_at off mem = n2w (LENGTH vs) /\
  (!i. i < LENGTH vs ==> val_in_memory tv (EL i vs)
     (off + 32 + i * type_memory_size tv) mem)
Proof
  simp[val_in_memory_def, typed_copy_elems_indexed]
QED

Theorem typed_copy_dynarray_wf:
  val_wf (ArrayTV tv (Dynamic C)) (ArrayV (DynArrayV vs)) <=>
  LENGTH vs <= C /\ (!i. i < LENGTH vs ==> val_wf tv (EL i vs))
Proof
  simp[val_wf_def, typed_copy_elems_wf_indexed]
QED

Theorem typed_copy_dynarray_typed_value:
  value_has_type (ArrayTV tv (Dynamic C)) v ==>
  ?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= C /\
       all_have_type tv vs
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]
QED

Theorem typed_copy_dynarray_reconstruct:
  mem_word_at off s.vs_memory = n2w (LENGTH vs) /\
  typed_copy_state_frame sa (off + 32) len s t /\
  (!i. i < LENGTH vs ==> val_in_memory tv (EL i vs)
      (off + 32 + i * type_memory_size tv) t.vs_memory) ==>
  val_in_memory (ArrayTV tv (Dynamic C)) (ArrayV (DynArrayV vs)) off t.vs_memory
Proof
  simp[typed_copy_dynarray_representation] >> strip_tac >> simp[] >>
  `mem_bytes_at off 32 t.vs_memory = mem_bytes_at off 32 s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     first_x_assum irule >> simp[]) >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem typed_copy_dynarray_prefix_rep_frag:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) ==>
  frag_exec ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w (LENGTH vs)) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
      (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
         (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w (LENGTH vs)) s)` by
    metis_tac[typed_copy_dynarray_mload_step] >>
  drule_all typed_copy_dyn_prefix_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >>
  simp[] >> rpt strip_tac >>
  rename1 `typed_copy_state_frame a (w2n dw) 32 s t` >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) t.vs_memory` suffices_by
    simp[typed_copy_dynarray_representation] >>
  irule typed_copy_frame_preserves_source >> conj_tac >- simp[] >>
  qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >>
  simp[] >> conj_tac
  >- (fs[type_memory_size_def] >> decide_tac) >>
  gvs[typed_copy_state_frame_def]
QED

Theorem typed_copy_dynarray_frag:
  compile_copy_dynarray_typed cenv dst dty C src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (dty = sty ==> dtv = stv) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (!i. i < LENGTH vs ==> typed_copy_entry cenv ctx dty sty dtv stv (EL i vs)) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs))
           (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic C))) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dd,b)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `frag_exec ctx sa b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w (LENGTH vs)) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
      (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
         (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) 32 s t) (\r. F)` by
    (irule typed_copy_dynarray_prefix_rep_frag >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ a5 = _`)) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`dtv`, `scap`] >> simp[]) >>
  drule frag_exec_then >> disch_then irule >>
  conj_tac >- suspend "suffix" >> suspend "extensions"
QED

Resume typed_copy_dynarray_frag[suffix]:
  simp[] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `typed_copy_state_frame sa (w2n dw) 32 s t` >>
  qpat_x_assum `frag_exec ctx sa b _ _ _` kall_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  `LENGTH vs <= scap` by gvs[typed_copy_dynarray_wf] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
   LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv < dimword (:256) /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv < dimword (:256) /\
   (w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= w2n (dw + 32w) \/
    w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= w2n (sw + 32w))` by
    (gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  (`frag_exec ctx b sb (\u. u = t)
    (\u. (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
       (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
      typed_copy_state_frame b (w2n (dw + 32w))
        (LENGTH vs * type_memory_size dtv) t u) (\r. F)` by
    suspend "data") >> suspend "reconstruct"
QED

Resume typed_copy_dynarray_frag[data]:
  markerLib.RESUME_TAC >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  qpat_x_assum `val_in_memory _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `typed_copy_state_frame sa _ _ s t` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` kall_tac >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty` >>
  IF (qpat_assum `type_memory_size dtv = type_memory_size stv /\ dty = sty` kall_tac)
    (suspend "bulk_data") (suspend "slow_data")
QED

Resume typed_copy_dynarray_frag[bulk_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  `dtv = stv` by simp[] >> gvs[] >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  ho_match_mp_tac (GEN_ALL typed_copy_dynarray_bulk_data_frag) >>
  goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >>
  qexists_tac `sw + 32w` >> simp[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  gvs[typed_copy_dynarray_wf]
QED

Resume typed_copy_dynarray_frag[slow_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `!i. i < LENGTH vs ==> typed_copy_entry cenv ctx dty sty dtv stv (EL i vs) /\
      val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)` by
    gvs[typed_copy_dynarray_wf] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  `!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
     (w2n (sw + 32w) + i * type_memory_size stv) t.vs_memory` by
    (qpat_assum `w2n (sw + 32w) = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `!i. _ ==> val_in_memory _ _ _ _` mp_tac >>
     simp_tac std_ss [AC ADD_ASSOC ADD_COMM]) >>
  qpat_assum `fresh_label "typed_dyn_cond" _ = _`
    (mp_then (Pat `fresh_label "typed_dyn_cond" _ = _`) mp_tac
      (GEN_ALL typed_copy_dynarray_slow_data_sizes_frag)) >>
  disch_then (drule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
  disch_then (drule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
  disch_then (drule_at (Pat `fresh_var _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  disch_then (drule_at (Pat `new_block _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op LT _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `new_block _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op MUL [Var _; Lit (n2w (type_memory_size stv))] _ = _`)) >>
  disch_then (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  disch_then (drule_at (Pat `new_block _ _ = _`)) >>
  disch_then ho_match_mp_tac >>
  qexists_tac `sw + 32w` >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  simp[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac
QED
Resume typed_copy_dynarray_frag[reconstruct]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `_ b = ((),sb)` kall_tac >>
  qpat_x_assum `frag_exec ctx b sb _ _ _` mp_tac >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (irule typed_copy_dynarray_reconstruct >> conj_tac
      >- (qpat_assum `!i. _ ==> val_in_memory dtv _ _ _` mp_tac >>
          simp_tac std_ss [AC ADD_ASSOC ADD_COMM]) >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
      simp[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  `typed_copy_state_frame sa (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t s''` by
    (irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule (GEN_ALL typed_copy_state_frame_trans) >> qexists_tac `t` >> conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ s t`)) >>
      simp[type_memory_size_def]) >>
  irule typed_copy_state_frame_subinterval >>
  goal_assum (drule_at (Pat `typed_copy_state_frame sa _ _ t _`)) >>
  simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"])
QED
Resume typed_copy_dynarray_frag[extensions]:
  reverse conj_tac >- gvs[ci_mono_def] >>
  qmatch_asmsub_abbrev_tac `suffix b = ((),sb)` >>
  `ci_mono b (SND (suffix b))` suffices_by gvs[ci_mono_def] >>
  unabbrev_all_tac >>
  IF_CASES_TAC >>
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_inst, ci_mono_new_block,
       ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_comp_return,
       cj 1 ci_mono_typed_memory_family,
       contextTheory.compile_copy_memory_dynamic_def, ci_mono_emit_void]
QED
Finalise typed_copy_dynarray_frag

Theorem typed_copy_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH l ==> typed_copy_entry cenv ctx de se tv' tv (EL i l)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once type_rank_def] >>
     gvs[typed_copy_dynarray_wf, vyperTypingTheory.all_have_type_EVERY,
         EVERY_EL]) >>
  simp[typed_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_dynarray_frag >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`scap`, `tv`, `sw`] >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem typed_copy_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_entry cenv ctx (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typed_copy_default_widening] >>
  `!i. i < cap ==> typed_copy_entry cenv ctx de se tv' tv
      (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once type_rank_def] >>
     `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  simp[typed_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  (reverse (Cases_on `s.vs_inst_idx = LENGTH sa.cs_current_insts`)
   >- simp[frag_exec_def]) >>
  simp[type_memory_size_def] >> irule typed_copy_sarray_frag >>
  (conj_tac >- simp[]) >>
  (conj_tac >- gvs[type_memory_size_def]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[value_has_type_def]) >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw`, `tenv`] >> gvs[type_memory_size_def]
QED

Theorem typed_copy_entries_from_semantics[local]:
  !dtys stys dtvs stvs vs.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dtys ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_entries cenv ctx dtys stys dtvs stvs vs
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[OPT_MMAP_def, AllCaseEqs(), value_has_type_def, val_in_memory_def,
       val_wf_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[typed_copy_memory_size]
QED

Theorem typed_copy_tuple_children_widen:
  !stys dtys dtvs.
    (stys = dtys \/ arg_types_fit stys dtys) /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
    LIST_REL (type_widens_to tenv) stys dtys
Proof
  Induct >> Cases_on `dtys` >>
  simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]
QED

Theorem typed_copy_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (irule typed_copy_tuple_children_widen >>
     (conj_tac >- metis_tac[]) >>
     drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  `typed_copy_entries cenv ctx dtys stys tvs' tvs l` by
    (irule typed_copy_entries_from_semantics >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
     qexists_tac `tenv` >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[member_rank_lt_tuple]) >>
  simp[typed_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_tuple_frag >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  simp[type_memory_size_def, val_in_memory_def] >>
  (impl_tac >- (gvs[val_wf_def, type_memory_size_def, val_in_memory_def] >>
                 decide_tac)) >> simp[]
QED

Theorem typed_copy_struct_values:
  !names tvs fields.
    LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP (names,tvs)) fields /\
    fields_val_wf fields (ZIP (names,tvs)) ==>
    ?vs. fields = ZIP (names,vs) /\ LENGTH vs = LENGTH names /\
         values_have_types tvs vs /\ tuple_val_wf vs tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fields` >>
  simp[value_has_type_def, val_wf_def] >>
  PairCases_on `h'` >> simp[value_has_type_def, val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >> strip_tac >>
  qexists_tac `h'1::vs` >> simp[value_has_type_def, val_wf_def]
QED

Theorem typed_copy_struct_field_bytes:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) ==>
    EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem typed_copy_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_entry cenv ctx (StructT name) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[typed_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule typed_copy_tuple_children_widen >> simp[] >> metis_tac[]) >>
  `typed_copy_entries cenv ctx (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) tvs tvs vs` by
    (irule typed_copy_entries_from_semantics >> simp[] >>
     qexists_tac `tenv` >> gvs[evaluate_types_OPT_MMAP] >>
     (conj_tac >- metis_tac[]) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
     qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
     fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all member_rank_lt_struct >>
     simp[type_rank_def, nsid_to_string_def]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    ((conj_tac >- metis_tac[]) >>
     irule typed_copy_struct_field_bytes >> qexistsl_tac [`tenv`, `tvs`] >>
     simp[] >>
     (conj_tac >- (rpt strip_tac >> irule typed_copy_memory_size >>
       qexists_tac `tenv` >> simp[] >> metis_tac[])) >> metis_tac[]) >>
  simp[typed_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[FORALL_PROD]) >>
  mp_tac (typed_copy_struct_suffix_frag |> Q.SPEC `0` |>
    Q.INST [`full` |-> `fields`]) >> simp[] >>
  disch_then (drule_at (Pat `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`tvs`, `vs`, `s`, `dw`, `sw`] mp_tac) >>
  simp[type_memory_size_def, val_in_memory_def,
       struct_layout_size_zip, typed_copy_fields_tuple_zip] >>
  (impl_tac >- (gvs[type_memory_size_def, val_in_memory_def,
      struct_layout_size_zip, typed_copy_fields_tuple_zip] >> decide_tac)) >> simp[]
QED

Theorem typed_copy_rank_entry:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v ==>
    typed_copy_entry cenv ctx dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- (drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
      simp[typed_copy_entry_def] >> rpt strip_tac >>
      `type_memory_size dtv = 32` by
        (qpat_x_assum `is_word_type dty` mp_tac >>
         qpat_x_assum `evaluate_type tenv dty = SOME dtv` mp_tac >>
         Cases_on `dty` >> simp[is_word_type_def]
         >~ [`FlagT`]
         >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
             gvs[type_memory_size_def]) >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         simp[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
         rpt strip_tac >> gvs[type_memory_size_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, evaluate_type_def, type_memory_size_def,
             AllCaseEqs()]) >>
      `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
        metis_tac[entryDecodePropsTheory.val_in_memory_word] >>
      drule_all typed_copy_word_frag >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- (drule_all typed_copy_bytestring_source >> strip_tac >>
      simp[typed_copy_entry_def] >> rpt strip_tac >>
      qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def] >> strip_tac >>
      `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
         (?cap. tv = BaseTV (BytesT (Dynamic cap))) \/
         (?cap. tv = BaseTV (StringT cap))` by
        (Cases >> simp[is_bytestring_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
         >~ [`BytesT bd`]
         >- (Cases_on `bd` >> rw[is_bytestring_type_def, evaluate_type_def]) >>
         rw[evaluate_type_def]) >>
      `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
       (?cap. stv = BaseTV (StringT cap))` by metis_tac[] >>
      `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
       (?cap. dtv = BaseTV (StringT cap))` by metis_tac[] >>
      `val_footprint dtv v <= type_memory_size dtv` by
        metis_tac[exprSimPropsTheory.val_footprint_le] >>
      `val_footprint stv v <= type_memory_size stv` by
        metis_tac[exprSimPropsTheory.val_footprint_le] >>
      gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
      (irule typed_copy_bytestring_frag_exact >>
       conj_tac >- simp[] >>
       goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
       FIRST [rename1 `StringV str` >> qexistsl_tac [`STRLEN str`, `sw`],
              rename1 `BytesV bs` >> qexistsl_tac [`LENGTH bs`, `sw`]] >>
  gvs[val_in_memory_def, loweringPostsTheory.val_footprint_def,
           type_memory_size_def] >>
       qmatch_goalsub_abbrev_tac `word_size len <= word_size capacity` >>
       `word_size len <= word_size capacity` by
         (irule exprSimHypsTheory.word_size_monotone >>
          simp[Abbr `len`]) >>
       qspec_then `len` assume_tac exprSimPropsTheory.le_word_size_mul >>
       decide_tac)) >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule typed_copy_sarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >>
          rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
      >> (irule typed_copy_dynarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >>
          rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]))
  >~ [`TupleT dtys`]
  >- (irule typed_copy_tuple_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (irule typed_copy_struct_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  simp[typed_copy_entry_def] >> rpt strip_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  irule typed_copy_empty_frag >> simp[val_in_memory_def]
QED

Theorem compile_store_memory_typed_run:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((), sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_entry cenv ctx dty sty dtv stv v` by
    (irule typed_copy_rank_entry >> simp[] >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `typed_copy_entry _ _ _ _ _ _ _` mp_tac >>
  simp[typed_copy_entry_def] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac typed_copy_frag_run) >> simp[] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `t` >> gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  metis_tac[]
QED

(* Every exported copy boundary must be closed, including the recursive
   execution theorem: an old public admission must never be a dependency. *)
val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed typed memory copy theorem: " ^ name)
  end) (DB.thms "typedMemoryCopy");
