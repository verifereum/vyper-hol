(* Ordinary array membership at the linked RHS's storage or transient place. *)
Theory bodyMembershipArraySlotsMods
Ancestors
  bodyFullPostsMods bodyPtrBopInSlotLoad bodyPtrBopInHeaderContents
  exprSimBopRestWordStorage bodyPtrDefs loweringPosts context
  vyperArray vyperTyping vyperValueOperation list words arithmetic

Theorem membership_array_slots_mods:
  vv_location vv = SOME (if tr then LocTransient else LocStorage) /\
  post_value_type cenv e = ArrayT ety pbd /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic _ => ?pcap. pbd = Dynamic pcap) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  vv_post_mods H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu Tu u /\
  ws = GENLIST (\i. typed_val_to_w256 et
                  (THE (array_index (ArrayTV et bd) av (&i))))
                  (array_length (ArrayTV et bd) av) ==>
  ?w. eval_operand (vv_operand vv) u = SOME w /\
      op_taint Tu (vv_operand vv) = {} /\
      storage_holds cx tr (ArrayT ety pbd) tv w ee u /\
      (!i. i < LENGTH ws ==>
        key_taint (if tr then Tu.t_trans else Tu.t_stor)
          (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) = {} /\
        (if tr then tload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) u
         else sload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) u) = EL i ws) /\
      (!cap. bd = Dynamic cap ==>
        key_taint (if tr then Tu.t_trans else Tu.t_stor) w = {} /\
        (if tr then tload w u else sload w u) = n2w (LENGTH ws))
Proof
  Cases_on `vv` >> simp[vv_location_def,vv_operand_def] >> strip_tac >>
  rename1 `LocatedValue ann p` >>
  `vv_holds_mods cenv cx (ArrayT ety pbd) tv (LocatedValue ann p) ee u` by
    (qhdtm_assum `vv_post_mods`
       (mp_tac o REWRITE_RULE [vv_post_mods_def]) >> simp[]) >>
  `?w. eval_operand p.ptr_operand u = SOME w /\
       storage_holds cx tr (ArrayT ety pbd) tv w ee u` by
    (Cases_on `tr` >> gvs[vv_holds_mods_def,vv_holds_def] >> metis_tac[]) >>
  qexists_tac `w` >>
  `op_taint Tu p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  simp[] >>
  `array_length (ArrayTV et pbd) av = array_length (ArrayTV et bd) av /\
   (!i. array_index (ArrayTV et pbd) av (&i) = array_index (ArrayTV et bd) av (&i)) /\
   (case pbd of Fixed _ => 0 | Dynamic _ => 1) =
     (case bd of Fixed _ => 0 | Dynamic _ => 1)` by
    (Cases_on `bd` >> Cases_on `av` >> gvs[value_has_type_def,array_length_def,array_index_def]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> simp[EL_GENLIST] >>
      `i < array_length (ArrayTV et pbd) av` by simp[] >>
      `valid_index (ArrayTV et pbd) av (&i)` by simp[valid_index_def] >>
      drule array_index_valid >>
      Cases_on `array_index (ArrayTV et pbd) av (&i)` >> gvs[] >>
      conj_tac
      >- (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)
            membership_storage_array_key_clean >>
          disch_then drule >> simp[AC ADD_ASSOC ADD_COMM]) >>
      rename1 `array_index (ArrayTV et bd) av (&i) = SOME item` >>
      `i < array_length (ArrayTV et pbd) av /\
       array_index (ArrayTV et pbd) av (&i) = SOME item` by simp[] >>
      drule_all rest_word_storage_array_load >> simp[AC ADD_ASSOC ADD_COMM]) >>
  gen_tac >> disch_tac >> gvs[] >>
  drule_all membership_located_slot_header >> simp[]
QED
