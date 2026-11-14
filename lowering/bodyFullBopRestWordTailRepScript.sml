Theory bodyFullBopRestWordTailRep
Ancestors
  bodyFullBopRestWordCtorHeader bodyFullBopRestWordTailFrame
  bodyPtrBopInLiveMemory exprSimBopRestWordLoads exprSimBopRestWordIndex
  vyperArray vyperAssignPreservesType vyperTyping vyperValueOperation exprLowering list words

(* Enumerate logical indices, rather than the stored sparse entries. *)
Theorem rest_word_membership_indexed_words[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type et needle /\ value_has_type (ArrayTV et bd) (ArrayV av) ==>
  (evaluate_in_array (ArrayTV et bd) needle av <=>
   MEM (typed_val_to_w256 et needle)
     (GENLIST (\i. typed_val_to_w256 et
       (THE (array_index (ArrayTV et bd) av (&i))))
       (array_length (ArrayTV et bd) av)))
Proof
  strip_tac >>
  `!i. i < array_length (ArrayTV et bd) av ==>
     array_index (ArrayTV et bd) av (&i) =
       SOME (THE (array_index (ArrayTV et bd) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
     drule array_index_valid >>
     Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[]) >>
  drule_all rest_word_array_word_membership >>
  simp[MEM_GENLIST] >> metis_tac[optionTheory.THE_DEF]
QED

(* Constructor code operands denote the robust memory supplied by the child,
   not the runtime data section. Coverage and clean contents are separate. *)
Theorem rest_word_membership_robust_index[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  i < array_length (ArrayTV et bd) av /\
  w2n w + type_memory_size (ArrayTV et bd) <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) mem) ==>
  let a = w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 in
    a + 32 <= lo /\ mem_word_taint tn.t_mem a = {} /\
    mload a s = typed_val_to_w256 et v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by
    (irule array_index_has_type >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory et v
      (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) mem` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all rest_word_array_memory_index >> simp[]) >>
  conj_tac
  >- (drule_all rest_word_array_element_extent >> decide_tac) >>
  conj_tac
  >- (irule robust_typed_word_memory_clean >> metis_tac[]) >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  irule rest_word_memory_word >>
  metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Theorem rest_word_membership_robust_header[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety (Dynamic cap)) is_in sm = (out,ct) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV et (Dynamic pcap)) (ArrayV av) (w2n w) mem) ==>
  mem_word_taint tn.t_mem (w2n w) = {} /\
  mload (w2n w) s = n2w (array_length (ArrayTV et (Dynamic cap)) av)
Proof
  strip_tac >> Cases_on `av` >> fs[value_has_type_def, array_length_def] >>
  conj_tac
  >- metis_tac[bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean] >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  drule typedCopyLayoutPtrTheory.dynarray_in_memory_robust_length >>
  simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Theorem rest_word_membership_ctor_rep[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  vv_holds cenv cx (ArrayT ety pbd) tv vv ee u /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  (?val. read_result cx tv ee = (INL val,ee) /\
    !rt w. evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
        val_in_memory rt val (w2n w) mem)) ==>
  ?w. eval_operand (vv_operand vv) u = SOME w /\
    value_has_type (ArrayTV et pbd) (ArrayV av) /\
    w2n w + type_memory_size (ArrayTV et pbd) <= lo /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV et pbd) (ArrayV av) (w2n w) mem)
Proof
  Cases_on `vv` >>
  simp[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  strip_tac >>
  fs[loweringPostsTheory.vv_holds_def] >>
  gvs[loweringPostsTheory.immutable_holds_def] >>
  metis_tac[]
QED
