(* Destination-rank induction for finite, same-endpoint typed memory paths. *)
Theory typedNormalizeRankPathMem
Ancestors
  typedNormalizeStructEntryPathMem typedNormalizeTupleEntryPathMem
  typedNormalizeArrayEntryPathMem typedNormalizeScalarEntryPathMem
  typedMemoryCopy typedCopyMetadata context compileEnv valueEncoding
  vyperTypeSystem vyperValue vyperTyping vyperTypeArgFits
  list rich_list arithmetic words venomState

(* Reuse the entry's literal recursive interface without duplicating its syntax. *)
val rank_path_child =
  typed_store_array_entry_path_mem |> SPEC_ALL |> concl |> dest_imp |> fst |>
  strip_conj |> List.find (fn tm =>
    is_forall tm andalso fst (dest_var (fst (dest_forall tm))) = "dty") |>
  valOf |> subst [``rank:num`` |-> ``n:num``];

Theorem typed_store_rank_path_mem:
  !n ce tenv dty sty dtv stv v dst src sa sb ctx fn s dw sw.
  type_rank ce.ce_struct_fields dty = n /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  completeInduct_on `n` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN rank_path_child assume_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `!m. m < n ==> _` (drule_then irule) >>
      first_assum (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
      first_assum (irule_at (Pat `type_widens_to _ _ _`)) >>
      first_assum (irule_at (Pat `val_in_memory _ _ _ _`)) >>
      asm_rewrite_tac[]) >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  Cases_on `is_word_type dty`
  >- (drule_all typed_store_word_path_mem >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- (drule_all typed_store_bytestring_path_mem >> simp[]) >>
  Cases_on `dty`
  >~ [`ArrayT elem bd`] >- (drule_all typed_store_array_entry_path_mem >> simp[])
  >~ [`TupleT tys`] >- (drule_all typed_store_tuple_entry_path_mem >> simp[])
  >~ [`StructT name`] >- (drule_all typed_store_struct_entry_path_mem >> simp[])
  >~ [`NoneT`] >- (drule_all (INST_TYPE [alpha |-> ``:256``] typed_store_empty_path_mem) >>
      disch_then (qspecl_then [`fn`, `dw`, `ctx`] mp_tac) >> simp[]) >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()]
QED
