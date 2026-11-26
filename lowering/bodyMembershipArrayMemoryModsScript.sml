(* Memory membership uses the reached value's physical buffer, whether the
   compiler returns it as a StackValue or as a located memory place. *)
Theory bodyMembershipArrayMemoryMods
Ancestors
  bodyFullPostsMods bodyPtrBopInRepresentation externalReturnBounds
  bodyPtrBopInLiveMemory bodyPtrBopInMemoryContents typedCopyLayoutPtr typedCopyPtr
  bodyPtrBopHashFootprint exprSimBopRestWordLoads exprSimProps valueEncodingProps valueEncoding
  vyperArray vyperAssignPreservesType vyperTypeValues vyperTyping vyperValueOperation
  bodyPtrDefs ptrDiscipline loweringPosts compileEnv context venomState list words

Theorem membership_memory_placement[local]:
  vv_at cenv cx ty sa sm ee tv vv u /\
  read_result cx tv ee = (INL v,ee) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  expr_val_at cenv cx ty sa sm ee v (vv_operand vv) u
Proof
  Cases_on `vv` >> simp[vv_location_def,vv_operand_def]
  >- simp[vv_at_def] >>
  strip_tac >> drule_all membership_memory_value_at >> simp[]
QED

Theorem membership_memory_pointer[local]:
  ptr_vv_ok cx (ArrayT ety pbd) tv vv ee G tn u /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ptr_val_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) G tn u
Proof
  Cases_on `vv` >> simp[vv_location_def,vv_operand_def,ptr_vv_ok_def] >>
  strip_tac >> gvs[ptr_val_ok_def,is_word_type_def]
QED

Theorem membership_memory_index_read[local]:
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et pbd) (ArrayV av) /\
  array_index (ArrayTV et pbd) av (&i) = SOME v /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV et pbd) (ArrayV av) a mem) ==>
  mem_word_taint tn.t_mem
    (a + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
  mload (a + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u =
    typed_val_to_w256 et v
Proof
  strip_tac >>
  drule_all_then assume_tac word_tv_memory_size >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  `value_has_type et v` by (irule array_index_has_type >> metis_tac[]) >>
  qabbrev_tac `addr = a + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32` >>
  `!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory et v addr mem` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all rest_word_array_memory_index >> simp[Abbr `addr`]) >>
  conj_tac
  >- (irule robust_typed_word_memory_clean >> metis_tac[]) >>
  rewrite_tac[GSYM mem_word_at_eq_mload] >> irule rest_word_memory_word >>
  conj_tac >- (qexistsl [`get_tenv cx`,`ety`] >> simp[]) >>
  simp[] >> first_x_assum irule >> simp[mem_agree_outside_def]
QED

Theorem membership_memory_header_read[local]:
  value_has_type (ArrayTV et (Dynamic pcap)) (ArrayV av) /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV et (Dynamic pcap)) (ArrayV av) a mem) ==>
  mem_word_taint tn.t_mem a = {} /\
  mload a u = n2w (array_length (ArrayTV et (Dynamic pcap)) av)
Proof
  Cases_on `av` >> simp[value_has_type_def,array_length_def] >> strip_tac >>
  conj_tac >- metis_tac[dynarray_memory_header_clean] >>
  drule dynarray_in_memory_robust_length >>
  disch_then (qspec_then `u.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def,mem_word_at_eq_mload]
QED

Theorem membership_memory_array_bounds[local]:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic _ => ?pcap. pbd = Dynamic pcap) ==>
  array_length (ArrayTV et pbd) av = array_length (ArrayTV et bd) av /\
  (!i. array_index (ArrayTV et pbd) av (&i) = array_index (ArrayTV et bd) av (&i)) /\
  (case pbd of Fixed _ => 0 | Dynamic _ => 32) =
  (case bd of Fixed _ => 0 | Dynamic _ => 32)
Proof
  Cases_on `bd` >> Cases_on `av` >> simp[value_has_type_def,array_length_def,array_index_def] >>
  strip_tac >> gvs[]
QED

Theorem membership_array_memory_mods:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  post_value_type cenv e = ArrayT ety pbd /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic _ => ?pcap. pbd = Dynamic pcap) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  value_has_type (ArrayTV et pbd) (ArrayV av) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  vv_post_mods H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu Tu u /\
  ws = GENLIST (\i. typed_val_to_w256 et
                   (THE (array_index (ArrayTV et bd) av (&i))))
                (array_length (ArrayTV et bd) av) ==>
  ?w. eval_operand (vv_operand vv) u = SOME w /\
      op_taint Tu (vv_operand vv) = {} /\
      ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) Gu Tu u /\
      expr_val_at cenv cx (ArrayT ety pbd) sa sm ee (ArrayV av) (vv_operand vv) u /\
      (0 < type_memory_size (ArrayTV et pbd) ==>
       w2n w + type_memory_size (ArrayTV et pbd) <= u.vs_alloca_next) /\
      (!off n src dst t G' T'. vv_operand vv = Var src /\
        0 < n /\ off + n <= type_memory_size (ArrayTV et pbd) /\
        lookup_var dst t = SOME (w + n2w off) /\
        FLOOKUP G' dst = FLOOKUP Gu src /\ op_taint T' (Var dst) = {} ==>
        ptr_covers G' T' dst t n) /\
      (!i. i < LENGTH ws ==>
        (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
          type_memory_size (ArrayTV et pbd) /\
        mem_word_taint Tu.t_mem
          (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
        mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i ws) /\
      (!cap. bd = Dynamic cap ==>
        32 <= type_memory_size (ArrayTV et pbd) /\
        mem_word_taint Tu.t_mem (w2n w) = {} /\
        mload (w2n w) u = n2w (LENGTH ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel H ctx fn cenv cx ee u /\
   vv_at cenv cx (ArrayT ety pbd) sa sm ee tv vv u` by
    (qpat_assum `post_value_type cenv e = _` (fn ty =>
       qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
         (mp_tac o REWRITE_RULE [vv_post_mods_def,ty])) >> simp[]) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `post_value_type cenv e = _` (fn ty =>
    qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [ty])) >>
  drule_all_then assume_tac membership_memory_placement >>
  drule_all_then assume_tac membership_memory_pointer >>
  `~is_word_type (ArrayT ety pbd)` by simp[is_word_type_def] >>
  drule_all expr_val_at_frontier >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  `(0 < type_memory_size (ArrayTV et pbd) ==>
    w2n w + type_memory_size (ArrayTV et pbd) <= u.vs_alloca_next)` by
    (qpat_x_assum `val_footprint _ _ = 0 \/ _` mp_tac >>
     simp[val_footprint_def] >> decide_tac) >>
  qpat_x_assum `vv_location vv = NONE \/ _` kall_tac >>
  qpat_x_assum `val_footprint _ _ = 0 \/ _` kall_tac >>
  `op_taint Tu (vv_operand vv) = {} /\
   ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) Gu Tu u` by
    fs[ptr_val_ok_def,is_word_type_def] >>
  qexists `w` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `vv_operand vv = Var src` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      `lookup_var src u = SOME w` by fs[eval_operand_def] >>
      `off + n <= val_footprint (ArrayTV et pbd) (ArrayV av)` by simp[val_footprint_def] >>
      drule_all expr_val_at_ptr_offset_read_covers >> simp[]) >>
  `!mem. mem_agree_outside Tu.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV et pbd) (ArrayV av) (w2n w) mem` by
    (gen_tac >> disch_tac >> drule_all ptr_mem_ok_robust >> simp[]) >>
  drule_all_then strip_assume_tac membership_memory_array_bounds >>
  conj_tac
  >- suspend "elements" >>
  suspend "header"
QED

Resume membership_array_memory_mods[elements]:
  gen_tac >> simp[] >> strip_tac >>
  `i < array_length (ArrayTV et pbd) av` by simp[] >>
  `valid_index (ArrayTV et pbd) av (&i)` by simp[valid_index_def] >>
  drule array_index_valid >>
  Cases_on `array_index (ArrayTV et pbd) av (&i)` >> gvs[EL_GENLIST] >>
  rename1 `array_index (ArrayTV et bd) av (&i) = SOME item` >>
  `array_index (ArrayTV et pbd) av (&i) = SOME item` by simp[] >>
  `i < array_length (ArrayTV et pbd) av` by simp[] >>
  drule_all_then assume_tac word_tv_memory_size >>
  drule_all_then assume_tac (Q.INST [`bd` |-> `pbd`] rest_word_array_element_extent) >>
  drule_all membership_memory_index_read >> simp[]
QED

Resume membership_array_memory_mods[header]:
  gen_tac >> disch_tac >> gvs[] >>
  drule_all membership_memory_header_read >>
  simp[type_memory_size_def]
QED
Finalise membership_array_memory_mods
