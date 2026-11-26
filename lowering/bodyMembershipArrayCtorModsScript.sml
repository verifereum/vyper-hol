(* Constructor LocCode points into the staged immutable buffer. *)
Theory bodyMembershipArrayCtorMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrBopInRepresentation
  bodyPtrBopInLiveMemory bodyPtrBopInMemoryContents exprSimBopRestWordLoads
  exprLoweringProps exprSimProps typedCopyLayoutPtr valueEncodingProps
  vyperArray vyperAssignPreservesType vyperTypeValues vyperValueOperation
  bodyPtrDefs ptrDiscipline valueEncoding loweringPosts context
  vyperTyping option list words pred_set

Theorem ctor_membership_index_read[local]:
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  a + type_memory_size (ArrayTV et bd) <= lo /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV et bd) (ArrayV av) a mem) ==>
  a + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <= lo /\
  mem_word_taint tn.t_mem
    (a + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
  mload (a + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u =
    typed_val_to_w256 et v
Proof
  strip_tac >>
  drule_all_then assume_tac word_tv_memory_size >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  conj_tac
  >- (drule_all_then assume_tac rest_word_array_element_extent >> decide_tac) >>
  `value_has_type et v` by (irule array_index_has_type >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory et v
       (a + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) mem` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all rest_word_array_memory_index >> simp[]) >>
  conj_tac
  >- (irule robust_typed_word_memory_clean >> metis_tac[]) >>
  `val_in_memory (ArrayTV et bd) (ArrayV av) a u.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all rest_word_array_memory_load >> simp[mem_word_at_eq_mload]
QED

Theorem ctor_membership_header_read[local]:
  value_has_type (ArrayTV et (Dynamic pcap)) (ArrayV av) /\
  a + type_memory_size (ArrayTV et (Dynamic pcap)) <= lo /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV et (Dynamic pcap)) (ArrayV av) a mem) ==>
  a + 32 <= lo /\ mem_word_taint tn.t_mem a = {} /\
  mload a u = n2w (array_length (ArrayTV et (Dynamic cap)) av)
Proof
  Cases_on `av` >> simp[value_has_type_def, array_length_def] >> strip_tac >>
  conj_tac
  >- (fs[type_memory_size_def] >> decide_tac) >>
  conj_tac
  >- metis_tac[dynarray_memory_header_clean] >>
  drule dynarray_in_memory_robust_length >>
  disch_then (qspec_then `u.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def, mem_word_at_eq_mload]
QED

Theorem ctor_membership_bound_index[local]:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic cap => ?pcap. pbd = Dynamic pcap) /\
  i < array_length (ArrayTV et bd) av ==>
  i < array_length (ArrayTV et pbd) av /\
  array_index (ArrayTV et pbd) av (&i) =
    SOME (THE (array_index (ArrayTV et bd) av (&i))) /\
  (case pbd of Fixed _ => 0 | Dynamic _ => 32) =
    (case bd of Fixed _ => 0 | Dynamic _ => 32)
Proof
  strip_tac >>
  `valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
  drule array_index_valid >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_length_def, array_index_def, IS_SOME_EXISTS] >>
  metis_tac[THE_DEF]
QED

Theorem ctor_membership_base[local]:
  stmt_state_rel H ctx func cenv cx ee u /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\
  cenv.ce_imm_alloca = SOME ib ==>
  eval_operand ib u = SOME 0w /\
  (!x. ib = Var x ==> not_fresh_at sm x) /\
  (lo <> 0 ==> op_prov G ib = NONE /\ op_taint tn ib = {})
Proof
  strip_tac >> drule_all_then assume_tac membership_immutable_base_value >>
  Cases_on `ib` >> gvs[op_prov_def, op_taint_def] >>
  conj_tac
  >- metis_tac[local_ptrs_reserved_imm_base, freshWritesTheory.not_fresh_at_mono] >>
  fs[ghost_inv_at_mods_def, op_taint_def]
QED

Theorem ctor_membership_rep[local]:
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv u /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn u /\
  vv_location vv = SOME LocCode /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd) /\
  read_result cx tv ee = (INL (ArrayV av),ee) ==>
  ?w. eval_operand (vv_operand vv) u = SOME w /\
      value_has_type (ArrayTV et pbd) (ArrayV av) /\
      op_prov G (vv_operand vv) = NONE /\ op_taint tn (vv_operand vv) = {}
Proof
  Cases_on `vv` >>
  gvs[vv_location_def,vv_operand_def,vv_post_mods_def,
      vv_holds_mods_def,immutable_holds_mods_def,ptr_vv_ok_def] >>
  strip_tac >> gvs[immutable_holds_def]
QED

Theorem membership_array_ctor_mods:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv u /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn u /\
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd) /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  (case bd of Fixed n => pbd = Fixed n | Dynamic cap => ?pcap. pbd = Dynamic pcap) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  (?val. read_result cx tv ee = (INL val,ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
  ws = GENLIST (\i. typed_val_to_w256 et
         (THE (array_index (ArrayTV et bd) av (&i))))
         (array_length (ArrayTV et bd) av) ==>
  (!ib. cenv.ce_imm_alloca = SOME ib ==>
    eval_operand ib u = SOME 0w /\
    (!x. ib = Var x ==> not_fresh_at sm x) /\
    (lo <> 0 ==> op_prov G ib = NONE /\ op_taint tn ib = {})) /\
  ?w. eval_operand (vv_operand vv) u = SOME w /\
      op_prov G (vv_operand vv) = NONE /\ op_taint tn (vv_operand vv) = {} /\
      w2n w + type_memory_size (ArrayTV et pbd) <= lo /\
      (!i. i < LENGTH ws ==>
        w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <= lo /\
        mem_word_taint tn.t_mem
          (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
        mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i ws) /\
      (!cap. bd = Dynamic cap ==>
        w2n w + 32 <= lo /\ mem_word_taint tn.t_mem (w2n w) = {} /\
        mload (w2n w) u = n2w (LENGTH ws))
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> disch_tac >>
      `stmt_state_rel H ctx func cenv cx ee u` by fs[vv_post_mods_def] >>
      drule_all ctor_membership_base >> simp[]) >>
  drule_all_then strip_assume_tac ctor_membership_rep >>
  qpat_x_assum `!rt w. _` (drule_all_then strip_assume_tac) >>
  `val = ArrayV av` by fs[] >> gvs[EL_GENLIST] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      drule_all_then strip_assume_tac ctor_membership_bound_index >>
      mp_tac (Q.INST [`a` |-> `w2n (w:bytes32)`, `bd` |-> `pbd`,
        `v` |-> `THE (array_index (ArrayTV et bd) av (&i))`] ctor_membership_index_read) >>
      simp[]) >>
  gen_tac >> disch_tac >> gvs[] >>
  mp_tac (Q.INST [`a` |-> `w2n (w:bytes32)`] ctor_membership_header_read) >> simp[]
QED
