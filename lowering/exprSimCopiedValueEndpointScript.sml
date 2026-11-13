(* A captured array returns a Value child, owned by its snapshot allocation.
   No provenance of the source base is needed after index evaluation. *)
Theory exprSimCopiedValueEndpoint
Ancestors
  exprSimSubscriptArraySuffix placeMemoryStepFrame exprSimProps
  loweringPosts valueEncodingTyping valueEncodingProps vyperValueOperation
  vyperInterpreter vyperState vyperMisc
  context compileEnv venomState finite_map words arithmetic

Theorem copied_array_value_endpoint:
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV etv bd) /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n b) s.vs_memory /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (b + n2w j) /\
  w2n (b + n2w j) = w2n b + j /\
  FLOOKUP s.vs_allocas aid = SOME (w2n b,type_memory_size (ArrayTV etv bd)) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n lb lsz. local_region cenv es'.scopes s n lb lsz ==>
     w2n b + type_memory_size (ArrayTV etv bd) <= lb \/ lb + lsz <= w2n b) /\
  stmt_state_rel ctx func cenv cx es' s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==> FLOOKUP s.vs_allocas id = SOME entry) /\
  (!id off sz. FLOOKUP s0.vs_allocas id = SOME (off,sz) /\ id < sa.cs_next_id /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
        off + sz <= lb \/ lb + lsz <= off) ==>
     mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es es' s0 s /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 s) ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 es' (Value v)
    (LocatedValue et (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by metis_tac[value_has_type_val_wf] >>
  `mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv)` by
    metis_tac[array_element_step_offset] >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  `value_has_type etv v /\ well_formed_type_value etv /\
   val_in_memory etv v (w2n b+j) s.vs_memory` by
    (drule_all typed_memory_step_read >> simp[]) >>
  `j + type_memory_size etv <= type_memory_size (ArrayTV etv bd)` by
    (irule (cj 2 mem_path_offset_sound) >>
     qexists `[ValueSubscript (IntV i)]` >> simp[mem_path_offset_def]) >>
  `val_wf etv v /\ val_footprint etv v <= type_memory_size etv` by
    metis_tac[value_has_type_val_wf, val_footprint_le] >>
  qpat_x_assum `j = _` kall_tac >>
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
       mk_ptr_def, vyperASTTheory.expr_type_def, read_result_def,
       return_def] >>
  conj_tac >-
    (conj_tac >- metis_tac[ADD_COMM] >> strip_tac >>
     irule exprSimPropsTheory.val_in_memory_word_type >>
     conj_tac >- (qexistsl [`et`, `get_tenv cx`] >> simp[]) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  reverse conj_tac >- metis_tac[] >>
  disj1_tac >> qexistsl [`aid`, `w2n b`, `type_memory_size (ArrayTV etv bd)`] >>
  simp[] >> metis_tac[ADD_COMM]
QED
