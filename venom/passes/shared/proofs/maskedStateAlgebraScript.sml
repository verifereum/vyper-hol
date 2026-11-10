Theory maskedStateAlgebra
Ancestors ptrDiscipline finite_map pred_set combin

Theorem storage_agree_except_read:
  storage_agree_except X st su ==>
  word_agree_except (key_taint X k) (st k) (su k)
Proof
  simp[storage_agree_except_def, key_taint_def]
QED

Theorem key_taint_update:
  key_taint (key_update X k m) j =
  (if j = k then m INTER {b | b < 32} else key_taint X j)
Proof
  Cases_on `j = k` >> simp[key_taint_def, key_update_def, EXTENSION, CONJ_COMM]
QED

Theorem storage_agree_except_update:
  storage_agree_except X st su /\ word_agree_except m x y ==>
  storage_agree_except (key_update X k m) ((k =+ x) st) ((k =+ y) su)
Proof
  simp[storage_agree_except_def] >> rpt strip_tac >>
  Cases_on `k' = k` >>
  gvs[key_taint_update, combinTheory.APPLY_UPDATE_THM, word_agree_except_def] >>
  metis_tac[]
QED

Theorem imms_agree_except_update:
  imms_agree_except (D with d_imm := K X) im jm /\
  word_agree_except m x y ==>
  imms_agree_except (D with d_imm := K (key_update X k m))
    (im |+ (k,x)) (jm |+ (k,y))
Proof
  simp[imms_agree_except_def] >> rpt strip_tac >>
  Cases_on `k' = k` >> gvs[key_update_def, FAPPLY_FUPDATE_THM]
QED
