Theory placeMemoryTypedBase
Ancestors
  placeMemoryPrimitiveForward context exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomInst venomExecSemantics emitHelper valueEncodingProps
  entryDecodeProps exprSimProps immutableMemoryFrame list rich_list pair finite_map
  ASCIInumbers emitHelperProps exprSimAggregateEncoding vyperTypeArgFits
  valueEncodingProofs sorting vyperTypeDefaults valueEncodingTyping
  vyperTypeExprSoundness alist

(* Recursive word operands denote pointers; unlike a direct word store this
   branch first loads the represented value. *)
Theorem typed_memory_word_sequence:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
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
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     simp[FLOOKUP_UPDATE]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[eval_operand_def, exec_read1_def, exec_write2_def, lookup_var_update_var]
QED

Theorem typed_memory_word_forward:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME tv /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_word_sequence >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 tv v` by
    metis_tac[val_in_memory_word] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >>
  `val_in_memory tv v (w2n dw) u.vs_memory` by
    (qspecl_then [`tenv`, `dty`, `tv`, `v`] mp_tac val_in_memory_word >>
     simp[] >> disch_then (fn th => rewrite_tac[th]) >>
     simp[Abbr `u`, mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  simp[] >> rpt conj_tac
  >- simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def,
          venom_state_component_equality]
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE])
  >- simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (rpt strip_tac >>
      `s.vs_memory = (update_var (STRING #"%" (toString sa.cs_next_var))
         (mload (w2n sw) s) s).vs_memory` by simp[update_var_def] >>
      simp[Abbr `u`] >> metis_tac[mstore_mem_bytes_at_disjoint])
  >- simp[Abbr `u`, immutable_mstore_capacity, update_var_def, arithmeticTheory.MAX_DEF] >>
  simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

(* C1.4.9.6: recursive interface audit (contracts below are NOT theorems).

   Compiler source: contextScript.sml:671-808, NOT exprLoweringScript.sml.
   Public representation boundaries in valueEncodingProps:
     val_in_memory_dynarray: header=n2w(LENGTH vs), elems_in_memory at p+32.
     val_in_memory_sarray: kvs_in_memory AND every absent in-range key has
       default_value representation. A proof over MEM kvs alone is incomplete.
     val_in_memory_tuple/struct: tuple_in_memory/fields_in_memory respectively.
   Accessible pointwise boundaries in exprSimAggregateEncoding:
     elems_in_memory_EL: elems_in_memory vs p tv mem /\ i<LENGTH vs implies
       val_in_memory tv (EL i vs) (p+i*type_memory_size tv) mem.
     elems_in_memory_intro: converse with all i<LENGTH vs.
     kvs_in_memory_every: equivalent to EVERY over (i,v) pairs.
   valueEncodingProps.val_in_memory_relocate and mcopy_establishes_val_in_memory
   relocate ONE evaluated type; they do not reinterpret equal-sized types.

   Static fast path:
     compile_copy_sarray_typed tests equal element byte sizes AND
     ~is_abi_dynamic sf dty. Needed classification contract:
       arg_type_fits sty dty /\ ~is_abi_dynamic sf dty ==> sty=dty,
     mutually with the arg_types_fit list case. Then widening implies
     evaluated element types coincide and MCOPY relocation applies. This
     classification exists ONLY in inaccessible typedMemoryCopy as
     typed_copy_static_fits; it needs an accessible replacement proof.
     Equal size by itself is not sufficient and is not the proposed rule.

   Fixed slow loop contract:
     Fix N, kvs, stv, dtv; f i = case ALOOKUP kvs i of
       NONE => default_value stv | SOME v => v.
     From represented source, source/destination val_wf and destination
     value_has_type obtain for EVERY i<N the represented source f i and
     both child typing/wf facts. From all destination f i reconstruct the
     destination SArray representation. Missing standalone boundary must
     bridge sparse typing, ALOOKUP, and defaults; do not assume dense keys.
     Accessible vyperTypeArgFits.arg_type_fits_default_value gives
       arg_type_fits sty dty /\ evaluate_type tenv sty=SOME stv /\
       evaluate_type tenv dty=SOME dtv ==> default_value stv=default_value dtv.
     Handle syntactic equality separately for type_widens_to.

   Dynamic loop contract:
     f i=EL i vs, N=LENGTH vs. Destination typing supplies N<=dst_capacity;
     destination evaluate_type supplies dst_capacity<dimword(:256).
     Source evaluate_type gives positive element slot size and hence positive
     memory stride (size=32*slots). Thus zero stride is UNREACHABLE for
     successfully evaluated arrays, even when N=0 is reachable.
     Prove capacity bound using evaluate_type_def's positive element slots
     and type_slot_size(ArrayTV tv bd)<dimword; bound<=bound*slots.
     No division by stride is needed for N*stride or index arithmetic.
     Header MSTORE precedes data copy and must remain framed by child stores.
     Slow loop invariant: counter=i<=N; same full source; destination header;
     every j<i represented at destination; old vars except counter; outside
     full destination unchanged. The generic gas_marked_path_zero_iteration
     handles finite rounds only after real round and exit paths are proved.

   Struct contract:
     Widening to StructT name forces source=StructT name (by cases on source
     using type_widens_to_def/arg_type_fits_def). Thus source/destination
     metadata are identical, not reordered. expr_sim_inv provides
     sfields_tenv_consistent, distinct names, evaluated field byte sizes.
     sfields_tenv_consistent fixes MAP names and MAP types in semantic order.
     evaluate_type StructT initially evaluates children under tenv\\name;
     vyperTypeExprSoundness.evaluate_type_mono is required to transport them
     to tenv for recursive IH. This is not global evaluation injectivity.
     context's struct copier looks up source TYPE/SIZE by name but advances
     a cumulative source offset; this is justified only by identical ordered
     metadata and distinct keys. Needed suffix boundary must relate metadata,
     evaluated fields and values, and show ALOOKUP returns the matching pair.

   Proposed generalized rank IH (notation, not a new predicate):
     For ALL cd,cs,cdt,cst,cv with type_rank sf cd < parent_rank,
       widening, both evaluations, both value_has_type and val_wf, layouts
       and acyclic metadata imply FOR ALL operands, compiler states and
       runtime states: compiler result, operand freshness, pointer evaluation,
       represented source, separated intervals, address bounds, fn_has_code,
       aligned nonhalted start ==> EXISTS ONE endpoint t with gas path 0,
       represented destination cv, explicit non-memory/control record frame,
       old-variable/alloca preservation, outside-destination bytes, memory
       growth and compiler endpoint (as in typed_memory_word_forward).
     List suffix induction is inside rank induction; it must generalize both
     offsets, both metadata/type suffixes and all runtime/compiler states.

   Missing outputs before full runner: accessible static classification,
   sparse representation/typing boundary, metadata suffix boundary, actual
   slow-array round/exit witnesses, header/length preservation and branch
   composition. Existing typedMemoryCopy versions cannot be imported. The
   layout theorem only supplies function lookup, NOT execution or values.
   Fresh staging remains a separate obligation; its output frame permits
   writes to temporary space and cannot promise global outside-dst equality.
*)

(* Only dynamic bounds can permit a proper fitting conversion. *)
Theorem typed_memory_static_fits:
  (!sty dty. arg_type_fits sty dty /\ ~is_abi_dynamic sf dty ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys /\
     ~EXISTS (is_abi_dynamic sf) dtys ==> stys = dtys)
Proof
  ho_match_mp_tac vyperTypeSystemTheory.arg_type_fits_ind >>
  rw[vyperTypeSystemTheory.arg_type_fits_def, is_abi_dynamic_def] >>
  gvs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> fs[]
QED

Theorem typed_memory_static_widening:
  type_widens_to tenv sty dty /\ ~is_abi_dynamic sf dty ==> sty = dty
Proof
  rw[vyperTypeSystemTheory.type_widens_to_def] >> gvs[] >>
  drule (cj 1 typed_memory_static_fits) >>
  disch_then (qspec_then `sf` mp_tac) >> simp[]
QED

Theorem typed_memory_sarray_element:
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
  i < n ==>
  val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (off + i * type_memory_size tv) mem
Proof
  rw[val_in_memory_sarray] >> Cases_on `ALOOKUP kvs i` >> simp[] >>
  metis_tac[kvs_in_memory_lookup]
QED

Theorem typed_memory_sparse_member:
  !kvs tv n i v.
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  MEM (i,v) kvs ==> i < n /\ ALOOKUP kvs i = SOME v
Proof
  rpt gen_tac >> simp[vyperTypingTheory.value_has_type_def] >> strip_tac >>
  `ALL_DISTINCT (MAP FST kvs)` by metis_tac[vyperTypingTheory.SORTED_lt_ALL_DISTINCT] >>
  qpat_x_assum `SORTED _ _` kall_tac >>
  Induct_on `kvs` >> simp[vyperTypingTheory.value_has_type_def] >>
  Cases >> simp[vyperTypingTheory.value_has_type_def] >> rpt strip_tac >> gvs[] >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem typed_memory_sarray_intro:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (!i. i < n ==>
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      (off + i * type_memory_size tv) mem) ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem
Proof
  strip_tac >> rewrite_tac[val_in_memory_sarray] >> conj_tac
  >- (rewrite_tac[kvs_in_memory_every, EVERY_MEM] >>
      simp[FORALL_PROD] >> rpt strip_tac >>
      drule_all typed_memory_sparse_member >> strip_tac >>
      rename1 `ALOOKUP kvs k = SOME v` >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem typed_memory_sparse_lookup_wf:
  !kvs tv n i. kvs_val_wf kvs tv n ==>
    val_wf tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
Proof
  Induct >> simp[valueEncodingDefsTheory.val_wf_def, cj 1 val_wf_default_value_proof] >>
  Cases >> simp[valueEncodingDefsTheory.val_wf_def] >> rpt strip_tac >>
  Cases_on `q = i` >> gvs[] >> metis_tac[]
QED

Theorem typed_memory_sparse_lookup_type:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  evaluate_type tenv et = SOME tv ==>
  value_has_type tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
Proof
  simp[vyperTypingTheory.value_has_type_def] >> strip_tac >>
  Cases_on `ALOOKUP kvs i`
  >- (simp[] >> metis_tac[vyperTypeDefaultsTheory.default_value_has_type_thm]) >>
  simp[] >> metis_tac[sparse_has_type_lookup]
QED

Theorem typed_memory_widening_defaults:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  default_value stv = default_value dtv
Proof
  rw[vyperTypeSystemTheory.type_widens_to_def] >> gvs[] >>
  metis_tac[cj 1 arg_type_fits_default_value]
QED

Theorem typed_memory_array_stride_bounds:
  evaluate_type tenv (ArrayT et bd) = SOME atv ==>
  ?tv. evaluate_type tenv et = SOME tv /\ atv = ArrayTV tv bd /\
       0 < type_slot_size tv /\ 0 < type_memory_size tv /\
       bound_length bd < dimword (:256)
Proof
  rw[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[] >> conj_tac >- metis_tac[cj 1 type_memory_size_pos] >>
  Cases_on `bd` >>
  gvs[vyperValueTheory.type_slot_size_def, vyperASTTheory.bound_length_def] >>
  `n <= n * type_slot_size tv` by
    (Cases_on `type_slot_size tv` >> gvs[arithmeticTheory.MULT_CLAUSES]) >> decide_tac
QED

Theorem typed_memory_dynarray_length:
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) ==>
  LENGTH vs <= n
Proof
  simp[vyperTypingTheory.value_has_type_def]
QED

Theorem typed_memory_struct_widening:
  type_widens_to tenv sty (StructT name) ==> sty = StructT name
Proof
  Cases_on `sty` >>
  simp[vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.arg_type_fits_def] >> metis_tac[]
QED

(* The full environment evaluates the same ordered children as the pruned
   environment used by struct evaluation. *)
Theorem typed_memory_struct_evaluation:
  sfields_tenv_consistent sf tenv /\
  evaluate_type tenv (StructT name) = SOME tv ==>
  ?args fields tvs.
    FLOOKUP tenv name = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string name) = SOME fields /\
    MAP FST fields = MAP FST args /\
    MAP (FST o SND) fields = MAP SND args /\
    evaluate_types tenv (MAP (FST o SND) fields) [] = SOME tvs /\
    LENGTH tvs = LENGTH fields /\ tv = StructTV (ZIP (MAP FST fields,tvs))
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `?fields. FLOOKUP sf (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\
     MAP (FST o SND) fields = MAP SND args` by
    (gvs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 evaluate_type_mono] >>
  qexistsl_tac [`fields`, `tvs`] >> simp[] >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[] >> metis_tac[LENGTH_MAP]
QED

Theorem typed_memory_struct_values:
  !names tvs fields.
    LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP (names,tvs)) fields /\
    fields_val_wf fields (ZIP (names,tvs)) ==>
    ?vs. fields = ZIP (names,vs) /\ LENGTH vs = LENGTH names /\
         values_have_types tvs vs /\ tuple_val_wf vs tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fields` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  PairCases_on `h'` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >> strip_tac >>
  qexists_tac `h'1::vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def]
QED

Theorem typed_memory_fields_tuple_zip:
  !names vs tvs off mem.
    LENGTH names = LENGTH vs /\ LENGTH names = LENGTH tvs ==>
    (fields_in_memory (ZIP(names,vs)) (ZIP(names,tvs)) off mem <=>
     tuple_in_memory vs tvs off mem)
Proof
  Induct >> Cases_on `vs` >> Cases_on `tvs` >>
  simp[valueEncodingDefsTheory.val_in_memory_def]
QED

(* Appended suffixes start after precisely the represented prefix's size. *)
Theorem typed_memory_tuple_append:
  !prefix pts vs tvs off mem.
    LENGTH prefix = LENGTH pts ==>
    (tuple_in_memory (prefix ++ vs) (pts ++ tvs) off mem <=>
     tuple_in_memory prefix pts off mem /\
     tuple_in_memory vs tvs (off + type_memory_size_list pts) mem)
Proof
  Induct >> Cases_on `pts` >>
  simp[valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC, GSYM CONJ_ASSOC] >> REFL_TAC
QED

Theorem typed_memory_struct_copy_fields:
  !fs full cenv dst src doff soff.
    ALL_DISTINCT (MAP FST full) /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full /\
    EVERY (\f. MEM f full) fs ==>
    compile_struct_typed_copy cenv dst src fs full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (FST o SND) fs) (MAP (FST o SND) fs) doff soff
Proof
  Induct >- simp[compile_store_memory_typed_def] >>
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

Theorem typed_memory_struct_copy_suffix:
  ALL_DISTINCT (MAP FST full) /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full ==>
  !n dst src doff soff.
    compile_struct_typed_copy cenv dst src (DROP n full) full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (FST o SND) (DROP n full))
      (MAP (FST o SND) (DROP n full)) doff soff
Proof
  rpt strip_tac >> irule typed_memory_struct_copy_fields >>
  simp[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

(* Joint head/tail projection avoids unfolding the encoding in execution
   consumers. The same equivalence also reconstructs the completed suffix. *)
Theorem typed_memory_tuple_head:
  values_have_types (tv::tvs) (v::vs) /\
  tuple_val_wf (v::vs) (tv::tvs) /\
  tuple_in_memory (v::vs) (tv::tvs) off mem <=>
  value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v off mem /\
  values_have_types tvs vs /\ tuple_val_wf vs tvs /\
  tuple_in_memory vs tvs (off + type_memory_size tv) mem
Proof
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingDefsTheory.val_in_memory_def] >> metis_tac[]
QED

(* C1.4.9.7.4 execution-contract checkpoint (NOT execution theorems).

   Semantic prerequisites from the earlier audit are now checked above:
   - typed_memory_static_widening gives syntactic equality from widening and
     a non-ABI-dynamic destination, irrespective of the equal-size test.
   - typed_memory_sarray_element/intro project/rebuild ALL in-range indices.
     sparse_lookup_type uses successful child evaluation for absent defaults;
     sparse_lookup_wf and value_has_type_val_wf supply child frames.
     typed_memory_widening_defaults identifies the source/destination default.
   - typed_memory_array_stride_bounds supplies successful child evaluation,
     positive slots and bytes, and capacity<dimword for either bound kind.
     typed_memory_dynarray_length supplies LENGTH vs<=capacity.
   - typed_memory_struct_evaluation transports evaluate_types from tenv\\name
     to the full tenv, aligns compiler metadata, and gives equal lengths.
     struct_values and fields_tuple_zip reduce semantic structs to tuples;
     struct_copy_suffix reduces the actual compiler to ordered same-type
     fields using full distinct-metadata lookup, not reordered field lists.
     tuple_head is the joint typing/wf/representation head+tail equivalence;
     tuple_append places a suffix after the SUM of evaluated prefix sizes.

   Actual forward execution still needed, by contextScript.sml:671-808:

   WORD: typed_memory_word_forward is already an actual path/value/frame
   witness. Widening to a word forces source syntax equality. This branch
   takes pointer operands and executes MLOAD then MSTORE.

   BYTESTRING: needs a path lift for compile_store_bytestring with DIFFERENT
   syntactic bounds. Both layouts use one header plus runtime payload; the
   same-type runner is not its signature. Length bound from destination
   typing discharges capacity; preserve source with destination separation.

   FIXED FAST: static classification identifies the element syntax, hence
   both evaluated elements and whole Fixed N types. Raw MCOPY is one sequence
   (or none for zero bytes). Reuse primitive capacity/path boundaries after
   proving compiler branch equality, not after silently changing the source
   operand from pointer to word. Bytes after sparse defaults must be copied.

   DYNAMIC SETUP/FAST: run the seven-instruction MLOAD/GT/ISZERO/ASSERT/MSTORE/
   ADD/ADD prefix, retaining ONE state with header=n2w(LENGTH vs), data
   pointers at source+32/destination+32, and preserved source. Prove ASSERT
   from LENGTH vs<=destination capacity<dimword. Fast test is syntactic
   element equality plus equal sizes; remaining MUL/MCOPY uses actual length,
   not capacity. Header preservation and untouched destination slack must
   both be retained, including runtime length zero.

   FIXED/DYNAMIC SLOW: use a shared condition/round/exit execution boundary
   once lengths and strides are abstracted as N,ss,ds. At condition entry,
   current_bb=cond, inst_idx=0, counter=n2w i, i<=N<dimword. Condition LT,
   ISZERO,JNZ must give a path to body at index 0 if i<N, or exit at index 0
   if i=N. An exit prefix alone is insufficient for these three steps.
   At body entry, MUL/MUL/ADD/ADD must give child pointers to soff+i*ss and
   doff+i*ds, without word wrap. The child IH applies to its exact compiler
   endpoints b4,b5; use fn_has_code_mid, not fn_has_code_same_block, since a
   child may itself contain loops. On its endpoint execute ADD/ASSIGN/JMP to
   return to cond with counter=n2w(SUC i). The child must preserve counter,
   dynamic length operand and data pointers, all not_fresh_at child start.
   The ASSIGN to counter is intentionally not globally fresh after creation:
   loop invariant preserves OLD vars at pre-loop sa and exempts counter.

   Invariant at cond: full source remains represented; each j<i is represented
   at destination; dynamic header remains intact; non-memory/control frame;
   old vars and allocas; outside FULL destination equality and memory growth.
   val_in_memory_outside_write + contained_interval_separated preserve source
   and previous children. Dynamic header is a 32-byte preceding interval and
   also needs the disjoint-write boundary. Semantic completion uses all-index
   sparse intro (defaults identified) or elems_in_memory_intro plus header.
   gas_marked_path_zero_iteration composes these real round/exit paths,
   including N=0; it does not generate their instruction semantics.
   typed_copy_dynarray_slow_code_lookup supplies exact cond/body/end blocks;
   fixed-loop labels have the same shape but no corresponding checked lookup
   wrapper yet. fn_has_code_finished_mid can derive it. No huge layout
   conjunction should be passed directly into each semantic consumer.

   TUPLE/STRUCT: first execute compile_with_byte_offset twice, specialize
   child IH, then suffix IH. Carry original source and completed prefix
   through child writes with interval framing. Sizes must be compiler/evaluated
   equalities, not equal-sized reinterpretations. tuple_head and tuple_append
   close representation glue; OPT_MMAP head/tail equations provide child
   evaluations after struct_evaluation. Compiler suffix consumes distinct
   ordered metadata, not a by-name reordered representation.

   Common recursive result: ONE t with path F/0, destination representation,
   record equality restoring vs_vars,vs_memory,vs_prev_bb,vs_current_bb,
   vs_inst_idx, old variable equality, same allocas, outside-destination byte
   equality, memory length monotonicity, and exact final block/index. Rank IH
   quantifies over all runtime/compiler states, operands, offsets and types.

   STAGING IS DIFFERENT: literal_alloc_buffer_run changes vs_allocas and
   vs_alloca_next, preserves old entries/vars, and separates the temporary
   from old local regions. Its memory is initially unchanged. Frozen source
   bounds relative to alloca_next and all fresh-id regions must separate the
   source from this new region too. Stage-copy then conversion writes BOTH
   temporary and destination, so its frame allows their union, NOT merely
   outside-destination equality. The final state reconstruction only needs
   unchanged other live local regions. Allocation is an actual instruction
   path as well; run_inst_seq alone is not yet the composed assignment path.
*)
