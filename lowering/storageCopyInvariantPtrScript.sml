(* One resource predicate prevents repeating the exact copied-taint prefix and
   stable register conjunction in each phase of the counted storage-copy loop.
   Control position and halted status deliberately remain outside this predicate. *)
Theory storageCopyInvariantPtr
Ancestors
  storageCopyBodyPtr exprSimStorageCopy bodyPtrDefs ptrDiscipline ptrSafeRun
  venomState memLocDefs finite_map pred_set words

Definition storage_copy_inv_ptr_def:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s <=>
    copy_prefix loc a b n sbase k s /\
    eval_operand src s = SOME a /\ lookup_var root s = SOME (n2w b) /\
    ptr_covers G tn root s (32*n) /\ lookup_var cv s = SOME (n2w k) /\
    op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
    op_taint tn src = {} /\
    tn.t_stor = tnbase.t_stor /\ tn.t_trans = tnbase.t_trans /\
    tn.t_imm = tnbase.t_imm /\
    tn.t_mem =
      (tnbase.t_mem DIFF {x | b <= x /\ x < b+32*k}) UNION
      {b+32*i+r | i < k /\ r < 32 /\
        (a+n2w i,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans)} /\
    (!x. x NOTIN scratch ==>
      lookup_var x s = lookup_var x sbase /\ FLOOKUP G x = FLOOKUP Gbase x /\
      op_taint tn (Var x) = op_taint tnbase (Var x))
End

Theorem storage_copy_inv_ptr_zero:
  eval_operand src s = SOME a /\ lookup_var root s = SOME (n2w b) /\
  ptr_covers G tn root s (32*n) /\ lookup_var cv s = SOME 0w /\
  op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
  op_taint tn src = {} ==>
  storage_copy_inv_ptr loc src root cv scratch a b n s G tn 0 G tn s
Proof
  simp[storage_copy_inv_ptr_def, copy_prefix_zero, EXTENSION]
QED

Theorem storage_copy_inv_ptr_idx[simp]:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn
    (s with vs_inst_idx := i) =
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s
Proof
  simp[storage_copy_inv_ptr_def, copy_prefix_idx, eval_operand_def, lookup_var_def,
       ptr_covers_def]
QED

Theorem storage_copy_inv_ptr_jump[simp]:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn
    (jump_to lbl s) =
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s
Proof
  simp[storage_copy_inv_ptr_def, copy_prefix_jump, eval_operand_def, lookup_var_def,
       ptr_covers_def, jump_to_def]
QED

Theorem storage_copy_taint_image_suc:
  {b+32*i+r | i < k+1 /\ r < 32 /\ P i r} =
  {b+32*i+r | i < k /\ r < 32 /\ P i r} UNION
  {x | ?r. r < 32 /\ P k r /\ x = b+32*k+r}
Proof
  simp[EXTENSION] >> gen_tac >> eq_tac >> rpt strip_tac
  >- (Cases_on `i < k` >> metis_tac[arithmeticTheory.LT_SUC_LE, arithmeticTheory.LESS_OR_EQ,
                                  arithmeticTheory.ADD1])
  >- (`i < k+1` by decide_tac >> metis_tac[])
  >- (`k < k+1` by decide_tac >> metis_tac[])
QED

Theorem storage_copy_taint_image_frame:
  {b+32*i+r | i < k /\ r < 32 /\ P i r} DIFF
    {x | b+32*k <= x /\ x < b+32*(k+1)} =
  {b+32*i+r | i < k /\ r < 32 /\ P i r}
Proof
  simp[EXTENSION] >> gen_tac >> eq_tac
  >- simp[] >>
  strip_tac >> conj_tac
  >- metis_tac[] >> gvs[] >> decide_tac
QED

Theorem storage_copy_taint_prefix_suc:
  (((M DIFF {x | b <= x /\ x < b+32*k}) UNION
     {b+32*i+r | i < k /\ r < 32 /\ P i r}) DIFF
     {x | b+32*k <= x /\ x < b+32*(k+1)}) UNION
     {x | ?r. r < 32 /\ P k r /\ x = b+32*k+r} =
  (M DIFF {x | b <= x /\ x < b+32*(k+1)}) UNION
     {b+32*i+r | i < k+1 /\ r < 32 /\ P i r}
Proof
  `{b+32*i+r | i < k /\ r < 32 /\ P i r} DIFF
     {x | b+32*k <= x /\ x < b+32*(k+1)} =
    {b+32*i+r | i < k /\ r < 32 /\ P i r}` by
    irule storage_copy_taint_image_frame >>
  once_rewrite_tac[storage_copy_taint_image_suc] >>
  `((M DIFF {x | b <= x /\ x < b+32*k}) DIFF
      {x | b+32*k <= x /\ x < b+32*(k+1)}) =
    M DIFF {x | b <= x /\ x < b+32*(k+1)}` by
    (simp[EXTENSION] >> gen_tac >> eq_tac >> rpt strip_tac >>
     gvs[] >> decide_tac) >> ASM_SET_TAC[]
QED

Theorem storage_copy_inv_ptr_scratch:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  x IN scratch /\ x <> root /\ x <> cv /\ src <> Var x /\
  (!y. y <> x ==> FLOOKUP G' y = FLOOKUP G y) ==>
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G'
    (tn with t_var := tn.t_var |+ (x,payload)) (update_var x w s)
Proof
  strip_tac >>
  Cases_on `src` >>
  gvs[storage_copy_inv_ptr_def, copy_prefix_update_var, eval_operand_def,
      lookup_var_def, update_var_def, op_prov_def, op_taint_def,
      FLOOKUP_UPDATE, ptr_covers_def] >> metis_tac[]
QED

Theorem storage_copy_inv_ptr_extend:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  k < n /\ cv IN scratch /\ cv <> root /\ src <> Var cv /\
  (!x. x <> cv ==> FLOOKUP G' x = FLOOKUP G x) /\
  op_prov G' (Var cv) = NONE ==>
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase (k+1) G'
    (tn with <| t_var := tn.t_var |+ (cv,{});
       t_mem := (tn.t_mem DIFF {x | b+32*k <= x /\ x < b+32*(k+1)}) UNION
         {x | ?r. r < 32 /\
            (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) /\
            x = b+32*k+r} |> )
    (update_var cv (n2w (k+1))
      (mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) s))
Proof
  strip_tac >> gvs[storage_copy_inv_ptr_def] >>
  `copy_prefix loc a b n sbase (k+1)
     (mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) s)` by
    (irule copy_prefix_extend >> simp[]) >>
  conj_tac >- simp[copy_prefix_update_var] >>
  Cases_on `src` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, mstore_def,
       write_memory_with_expansion_def, FLOOKUP_UPDATE, ptr_covers_def,
       op_taint_def, op_prov_def] >>
  gvs[eval_operand_def, lookup_var_def, ptr_covers_def, op_prov_def, op_taint_def] >>
  (conj_tac >-
    (mp_tac (Q.INST [`M` |-> `tnbase.t_mem`,
       `P` |-> `\i r. (a+n2w i,r) IN
         (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans)`]
       storage_copy_taint_prefix_suc) >> BETA_TAC >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> disch_then ACCEPT_TAC)) >>
  rpt strip_tac >> `x <> cv` by metis_tac[] >> simp[] >> metis_tac[]
QED

Theorem storage_copy_inv_ptr_store_increment:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  k < n /\ cv IN scratch /\ nv IN scratch /\
  cv <> root /\ nv <> root /\ nv <> cv /\
  src <> Var cv /\ src <> Var nv ==>
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase (k+1)
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with <| t_var := (tn.t_var |+ (nv,{})) |+ (cv,{});
      t_mem := (tn.t_mem DIFF {x | b+32*k <= x /\ x < b+32*(k+1)}) UNION
        {x | ?r. r < 32 /\
          (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) /\
          x = b+32*k+r} |> )
    (update_var cv (n2w (k+1))
      (update_var nv (n2w (k+1))
        (mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) s)))
Proof
  strip_tac >>
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k
    (DRESTRICT G (COMPL {nv})) (tn with t_var := tn.t_var |+ (nv,{}))
    (update_var nv (n2w (k+1)) s)` by
    (irule storage_copy_inv_ptr_scratch >> simp[] >>
     qexists_tac `G` >> simp[FLOOKUP_DRESTRICT]) >>
  drule_at (Pat `storage_copy_inv_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    storage_copy_inv_ptr_extend >>
  disch_then (qspec_then `DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})` mp_tac) >>
  simp[FLOOKUP_DRESTRICT, op_prov_def] >>
  simp[update_var_def, mstore_def, write_memory_with_expansion_def]
QED
