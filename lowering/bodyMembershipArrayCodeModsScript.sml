(* Runtime membership reads the selected module's immutable bytes at the
   operand returned by the linked RHS. No rebasing of the compile environment. *)
Theory bodyMembershipArrayCodeMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyPtrBopInHeaderContents bodyPtrBopInCodeContents
  exprSimProps exprSimCopy abiDecodeStaticProps valueEncodingDefs
  bodyFullPostsMods bodyPtrDefs loweringPosts context vyperArray
  vyperAssignPreservesType vyperTyping vyperState vyperValueOperation list words arithmetic

Theorem runtime_code_member[local]:
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  val_in_memory (ArrayTV et bd) (ArrayV av) (w2n (w:bytes32)) s.vs_data_section /\
  w2n w + type_memory_size (ArrayTV et bd) <= LENGTH s.vs_data_section /\
  w2n w + type_memory_size (ArrayTV et bd) < dimword (:256) ==>
  let a = w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) in
    a + 32 <= LENGTH s.vs_data_section /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP a s.vs_data_section ++ REPLICATE 32 0w)) =
      typed_val_to_w256 et v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `type_memory_size et = 32` by (drule_all word_tv_memory_size >> simp[]) >>
  drule_all_then assume_tac membership_array_element_extent >>
  drule_all_then assume_tac membership_array_memory_index >>
  qabbrev_tac `off = (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32` >>
  `w2n ((w:bytes32) + n2w off) = w2n w + off` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  simp[] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by (irule array_index_has_type >> metis_tac[]) >>
  simp[GSYM mem_word_at_def] >> irule val_in_memory_word_type >>
  conj_tac >- (qexistsl [`ety`,`get_tenv cx`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `off + w2n w = w2n w + ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * type_memory_size et)` by
    (simp[Abbr `off`] >> decide_tac) >>
  qpat_assum `off + w2n w = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `val_in_memory et v _ _` mp_tac >> pure_rewrite_tac[ADD_ASSOC] >>
  disch_then ACCEPT_TAC
QED

Theorem membership_array_code_mods:
  ~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  post_value_type cenv e = ArrayT ety pbd /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic _ => ?pcap. pbd = Dynamic pcap) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  vv_post_mods H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu Tu u ==>
  let ws = GENLIST (\i. typed_val_to_w256 et
                 (THE (array_index (ArrayTV et bd) av (&i))))
                   (array_length (ArrayTV et bd) av) in
  ?w. eval_operand (vv_operand vv) u = SOME w /\
      op_taint Tu (vv_operand vv) = {} /\ op_prov Gu (vv_operand vv) = NONE /\
      immutable_holds_mods cenv cx (ArrayT ety pbd) (Value (ArrayV av)) w ee u /\
      value_has_type (ArrayTV et pbd) (ArrayV av) /\
      w2n w + type_memory_size (ArrayTV et pbd) <= LENGTH u.vs_data_section /\
      (!i. i < LENGTH ws ==>
        let a = w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) in
          a + 32 <= LENGTH u.vs_data_section /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP a u.vs_data_section ++ REPLICATE 32 0w)) = EL i ws) /\
      (!cap. bd = Dynamic cap ==>
        w2n w + 32 <= LENGTH u.vs_data_section /\
        word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws))
Proof
  Cases_on `vv` >> simp[vv_location_def,vv_operand_def,LET_THM] >> strip_tac >>
  rename1 `LocatedValue ty p` >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd)` by simp[] >>
  qpat_assum `~cenv.ce_is_ctor` (fn th => drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) [th]
      (Q.INST [`ce` |-> `cenv`] local_copy_raw_code_source_mods))) >>
  gvs[] >>
  `immutable_holds (cenv with ce_module := src) cx (ArrayT ety pbd)
       (Value (ArrayV av)) w ee u /\ value_has_type (ArrayTV et pbd) (ArrayV av)` by
    (qpat_x_assum `immutable_holds _ _ _ tv _ _ _` mp_tac >>
     simp[immutable_holds_def,read_result_def,return_def] >> metis_tac[]) >>
  drule_all_then strip_assume_tac immutable_holds_bounds >>
  simp[] >>
  conj_tac >- (simp[immutable_holds_mods_def] >> qexistsl [`src`,`tops`] >> simp[]) >>
  `array_length (ArrayTV et pbd) av = array_length (ArrayTV et bd) av /\
   (!i. array_index (ArrayTV et pbd) av (&i) = array_index (ArrayTV et bd) av (&i)) /\
   (case pbd of Fixed _ => 0 | Dynamic _ => 32) =
   (case bd of Fixed _ => 0 | Dynamic _ => 32)` by
    (Cases_on `bd` >> Cases_on `av` >> gvs[value_has_type_def,array_length_def,array_index_def]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> simp[EL_GENLIST] >>
      `valid_index (ArrayTV et pbd) av (&i)` by simp[valid_index_def] >>
      drule array_index_valid >>
      Cases_on `array_index (ArrayTV et pbd) av (&i)` >> gvs[] >>
      rename1 `array_index (ArrayTV et bd) av (&i) = SOME item` >>
      mp_tac (Q.INST [`bd` |-> `pbd`, `s` |-> `u`, `v` |-> `item`] runtime_code_member) >>
      simp[LET_THM]) >>
  gen_tac >> disch_tac >> gvs[] >>
  drule_all membership_dynamic_memory_header >>
  simp[mem_word_at_def,mem_bytes_at_def] >> strip_tac >>
  fs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED
