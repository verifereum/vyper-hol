Theory vyperArray

Ancestors
  vyperInterpreter

Definition array_is_mutable_def[simp]:
  array_is_mutable (DynArrayV _ _ _) = T ∧
  array_is_mutable (SArrayV _ _ _) = T ∧
  array_is_mutable (TupleV _) = F
End

Definition array_is_dynamic_def[simp]:
  array_is_dynamic (DynArrayV _ _ _) = T ∧
  array_is_dynamic (SArrayV _ _ _) = F ∧
  array_is_dynamic (TupleV _) = F
End

Definition valid_index_def[simp]:
  valid_index a (i:int) ⇔ 0 ≤ i ∧ i < &array_length a
End

(* ===== Helper Lemmas for insert_sarray ===== *)

Theorem ALOOKUP_insert_sarray_same[local]:
  ∀k v al. ALOOKUP (insert_sarray k v al) k = SOME v
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
QED

Theorem ALOOKUP_insert_sarray_other[local]:
  ∀k v al k'. k ≠ k' ⇒ ALOOKUP (insert_sarray k v al) k' = ALOOKUP al k'
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
QED

Theorem TAKE_DROP_LUPDATE[local]:
  ∀ls k e. k < LENGTH ls ⇒ TAKE k ls ++ [e] ++ DROP (SUC k) ls = LUPDATE e k ls
Proof
  Induct \\ simp[]
  \\ rpt gen_tac \\ Cases_on`k`
  \\ simp[listTheory.LUPDATE_DEF]
  \\ strip_tac \\ gvs[]
QED

Theorem array_index_valid:
  ∀a i. valid_index a i ⇔ IS_SOME (array_index a i)
Proof
  Cases \\ rw[array_index_def, array_length_def, listTheory.oEL_THM]
  \\ gvs[]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ CASE_TAC \\ simp[]
QED

Theorem array_set_index_valid:
  ∀a i v. array_is_mutable a ∧ valid_index a i ⇔ ∃a'. array_set_index a i v = INL (ArrayV a')
Proof
  Cases \\ rw[array_set_index_def, array_length_def, EQ_IMP_THM]
  \\ gvs[]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
QED

Theorem array_length_after_set:
  ∀a a' i v. array_set_index a i v = INL (ArrayV a') ⇒ array_length a' = array_length a
Proof
  Cases \\ rw[array_set_index_def, array_length_def]
  \\ gvs[AllCaseEqs()]
QED

Theorem array_index_after_set_same:
  ∀a a' i v. array_set_index a i v = INL (ArrayV a') ⇒ array_index a' i = SOME v
Proof
  Cases \\ simp[array_set_index_def, AllCaseEqs()]
  \\ rw[] \\ simp[array_index_def, listTheory.oEL_THM,
                   listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE_EQ,
                   ALOOKUP_insert_sarray_same, alistTheory.ALOOKUP_ADELKEY]
QED

Theorem array_index_after_set_other:
  ∀a a' i j v. i ≠ j ∧ array_set_index a i v = INL (ArrayV a') ⇒ array_index a' j = array_index a j
Proof
  Cases \\ simp[array_set_index_def, AllCaseEqs()]
  \\ rpt gen_tac \\ strip_tac
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[array_index_def, TAKE_DROP_LUPDATE,
          listTheory.oEL_LUPDATE, alistTheory.ALOOKUP_ADELKEY,
          ALOOKUP_insert_sarray_other]
  \\ rw[] \\ gvs[]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[alistTheory.ALOOKUP_ADELKEY, ALOOKUP_insert_sarray_other]
QED

Theorem array_length_after_pop:
  ∀a a'. pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_length a' = array_length a - 1
Proof
  Cases \\ simp[pop_element_def, array_length_def]
  \\ rw[] \\ gvs[rich_listTheory.LENGTH_FRONT]
QED

Theorem array_index_after_pop:
  ∀a a' i. valid_index a' i ∧ pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_index a i = array_index a' i
Proof
  Cases \\ simp[pop_element_def]
  \\ rw[] \\ gvs[array_index_def, array_length_def]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ Cases_on`l`
  \\ gvs[listTheory.oEL_THM, rich_listTheory.LENGTH_FRONT,
         rich_listTheory.EL_FRONT, listTheory.NULL_EQ]
QED

Theorem array_pop_valid:
  ∀a. array_is_dynamic a ∧ array_length a ≠ 0 ⇔ ∃a'. pop_element (ArrayV a) = INL (ArrayV a')
Proof
  Cases \\ rw[pop_element_def, array_length_def, EQ_IMP_THM]
  \\ gvs[listTheory.LENGTH_NIL_SYM]
QED

Theorem array_length_after_append:
  ∀a a' v. append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_length a' = array_length a + 1
Proof
  Cases \\ simp[append_element_def, array_length_def, AllCaseEqs()]
  \\ rw[] \\ gvs[listTheory.LENGTH_SNOC, arithmeticTheory.ADD1]
QED

Theorem array_index_after_append:
  ∀a a' v. append_element (ArrayV a) v = INL (ArrayV a') ⇒ ∃ty v'. safe_cast ty v = SOME v' ∧ array_index a' &(array_length a) = SOME v'
Proof
  Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rw[] \\ gvs[]
  \\ qexists_tac`t` \\ qexists_tac`v'`
  \\ simp[array_index_def, array_length_def,
          listTheory.oEL_EQ_EL, listTheory.LENGTH_SNOC,
          listTheory.EL_LENGTH_SNOC]
QED

Theorem array_index_after_append_other:
  ∀a a' i v. valid_index a i ∧ append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_index a' i = array_index a i
Proof
  Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rw[] \\ gvs[array_index_def, array_length_def]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[listTheory.oEL_THM, listTheory.LENGTH_SNOC, listTheory.EL_SNOC]
QED

Theorem array_elements_length:
  ∀a. LENGTH (array_elements a) = array_length a
Proof
  Cases \\ simp[array_elements_def, array_length_def]
QED

Theorem array_elements_index:
  ∀a i v. valid_index a i ⇒ (EL (Num i) (array_elements a) = v ⇔ array_index a i = SOME v)
Proof
  Cases \\ simp[array_elements_def, array_index_def, array_length_def]
  \\ rw[] \\ gvs[]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[listTheory.oEL_EQ_EL, EQ_SYM_EQ]
  \\ CASE_TAC \\ simp[]
QED

Theorem array_elements_after_set:
  ∀a a' i v.
    array_set_index a i v = INL (ArrayV a') ⇒
    array_elements a' = (TAKE (Num i) (array_elements a) ++ [v] ++ DROP (SUC (Num i)) (array_elements a))
Proof
  Cases \\ simp[array_set_index_def, array_elements_def, AllCaseEqs()]
  \\ rw[]
  \\ simp[TAKE_DROP_LUPDATE, listTheory.LENGTH_GENLIST,
          listTheory.LUPDATE_GENLIST, listTheory.GENLIST_FUN_EQ]
  \\ rw[combinTheory.APPLY_UPDATE_THM]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY,
         ALOOKUP_insert_sarray_same, ALOOKUP_insert_sarray_other]
QED

Theorem array_elements_after_pop:
  ∀a a'.
    pop_element (ArrayV a) = INL (ArrayV a') ⇒
    array_elements a' = FRONT (array_elements a)
Proof
  Cases \\ simp[pop_element_def, array_elements_def]
  \\ rw[] \\ gvs[]
QED

Theorem array_elements_after_append:
  ∀a a' v.
    append_element (ArrayV a) v = INL (ArrayV a') ⇒
    ∃ty v'. safe_cast ty v = SOME v' ∧ array_elements a' = array_elements a ++ [v']
Proof
  Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs[]
  \\ qexists_tac`t` \\ qexists_tac`v'`
  \\ simp[array_elements_def, listTheory.SNOC_APPEND]
QED
