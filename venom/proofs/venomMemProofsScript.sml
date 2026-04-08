(*
 * Venom Memory Proofs
 *
 * TOP-LEVEL:
 *   alloca_inv_empty_proof                    — alloca_inv for empty allocas
 *   alloca_inv_step_inst_proof                 — alloca_inv preserved by step_inst
 *   alloca_inv_exec_block_proof                — alloca_inv preserved by exec_block
 *   alloca_inv_run_block_proof                 — alloca_inv preserved by run_block
 *   alloca_inv_run_blocks_proof                — alloca_inv preserved by run_blocks
 *   alloca_inv_run_function_proof              — alloca_inv preserved by run_function
 *   allocas_non_overlapping_empty_proof       — base case
 *   allocas_non_overlapping_step_inst_proof   — preserved by step_inst
 *   allocas_non_overlapping_exec_block_proof  — preserved by exec_block
 *   mload_mstore_disjoint_proof               — 32-byte write/read independence
 *   mload_mstore8_disjoint_proof              — 1-byte write / 32-byte read
 *)

Theory venomMemProofs
Ancestors
  venomMemDefs venomExecSemantics venomState venomInstProofs
  finite_map list rich_list words byte arithmetic divides
Libs
  wordsLib dep_rewrite

(* ===================================================================
   Infrastructure: dimindex, word_to_bytes length
   =================================================================== *)

Theorem dimindex_256[local]:
  dimindex (:256) = 256
Proof
  rw[fcpTheory.index_bit0, fcpTheory.index_bit1, fcpTheory.index_one,
     fcpTheory.finite_bit0, fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

Theorem len_word_to_bytes_256[local]:
  LENGTH (word_to_bytes (w:bytes32) be) = 32
Proof
  rw[byteTheory.LENGTH_word_to_bytes, dimindex_256]
QED

(* ===================================================================
   List splice lemma: replacing [a, a+n) doesn't affect [b, b+m)
   when ranges are disjoint. Used by both mstore and mstore8 proofs.
   =================================================================== *)

(* Case 1: read range entirely before write range *)
Theorem take_drop_splice_before[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\ b + m <= a ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[rich_listTheory.TAKE_DROP_SWAP] >>
  `LENGTH (TAKE a l) = a` by (irule listTheory.LENGTH_TAKE >> fs[]) >>
  (* Re-associate: (TAKE a l ++ mid) ++ DROP ... => TAKE a l ++ (mid ++ DROP ...) *)
  `TAKE a l ++ mid ++ DROP (a + LENGTH mid) l =
   TAKE a l ++ (mid ++ DROP (a + LENGTH mid) l)` by
    rw[GSYM listTheory.APPEND_ASSOC] >>
  ASM_REWRITE_TAC[] >>
  (* Now TAKE (b+m) (TAKE a l ++ ...) = TAKE (b+m) (TAKE a l) since b+m <= a *)
  `TAKE (b + m) (TAKE a l ++ (mid ++ DROP (a + LENGTH mid) l)) =
   TAKE (b + m) (TAKE a l)` by
    (irule rich_listTheory.TAKE_APPEND1 >> fs[]) >>
  ASM_REWRITE_TAC[] >>
  (* TAKE (b+m) (TAKE a l) = TAKE (b+m) l since b+m <= a *)
  `TAKE (b + m) (TAKE a l) = TAKE (b + m) l` by
    (irule rich_listTheory.TAKE_TAKE_T >> fs[]) >>
  ASM_REWRITE_TAC[]
QED

(* Case 2: read range entirely after write range *)
Theorem take_drop_splice_after[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\ a + n <= b ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[] >>
  (* DROP b skips past (TAKE a l ++ mid), landing in DROP (a+n) l *)
  `LENGTH (TAKE a l ++ mid) = a + LENGTH mid` by
    (rw[LENGTH_APPEND] >> irule LENGTH_TAKE >> fs[]) >>
  `DROP b (TAKE a l ++ mid ++ DROP (a + LENGTH mid) l) =
   DROP (b - (a + LENGTH mid)) (DROP (a + LENGTH mid) l)` by
    (`b - LENGTH (TAKE a l ++ mid) = b - (a + LENGTH mid)` by fs[] >>
     metis_tac[DROP_APPEND2]) >>
  ASM_REWRITE_TAC[] >>
  rw[rich_listTheory.DROP_DROP_T]
QED

(* Combined: disjoint ranges *)
Theorem take_drop_splice_disjoint[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\
    (b + m <= a \/ a + n <= b) ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[] >> metis_tac[take_drop_splice_before, take_drop_splice_after]
QED

(* ===================================================================
   Padding lemma: if off + 32 <= LENGTH l, padding is irrelevant
   =================================================================== *)

Theorem take_drop_no_pad[local]:
  !(l : word8 list) off.
    off + 32 <= LENGTH l ==>
    TAKE 32 (DROP off l ++ REPLICATE 32 0w) = TAKE 32 (DROP off l)
Proof
  rw[] >>
  `LENGTH (DROP off l) = LENGTH l - off` by rw[listTheory.LENGTH_DROP] >>
  `32 <= LENGTH (DROP off l)` by fs[] >>
  irule rich_listTheory.TAKE_APPEND1 >> fs[]
QED

(* Padding-length-insensitive TAKE: only the payload matters, not how much padding *)
Theorem take_append_pad[local]:
  !n (l:'a list) a b x.
    n <= LENGTH l + a /\ n <= LENGTH l + b ==>
    TAKE n (l ++ REPLICATE a x) = TAKE n (l ++ REPLICATE b x)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND, LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

(* DROP distributes over APPEND with REPLICATE tail *)
(* Combined: TAKE n (DROP m (l ++ pad) ++ more_pad) = TAKE n (DROP m l ++ combined_pad) *)
Theorem take_drop_pad_irrelevant[local]:
  !off (mem : word8 list) k.
    off <= LENGTH mem ==>
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >>
  `DROP off (mem ++ REPLICATE k 0w) = DROP off mem ++ REPLICATE k 0w` by
    rw[DROP_APPEND1] >>
  rw[] >>
  `DROP off mem ++ REPLICATE k 0w ++ REPLICATE 32 0w =
   DROP off mem ++ REPLICATE (k + 32) (0w:word8)` by
    rw[GSYM APPEND_ASSOC, GSYM rich_listTheory.REPLICATE_APPEND] >>
  ASM_REWRITE_TAC[] >>
  irule take_append_pad >>
  rw[LENGTH_DROP, LENGTH_REPLICATE]
QED

(* When off >= LENGTH mem, padding doesn't matter for reads *)
Theorem take_drop_pad_beyond[local]:
  !off (mem : word8 list) k.
    LENGTH mem <= off ==>
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >>
  `DROP off mem = []` by rw[DROP_LENGTH_TOO_LONG] >> rw[] >>
  (* Both sides = REPLICATE 32 0w; prove via LIST_EQ_REWRITE *)
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND,
     LENGTH_DROP, LENGTH_REPLICATE, EL_TAKE,
     EL_APPEND_EQN, EL_REPLICATE, EL_DROP]
QED

(* Combining both padding cases *)
Theorem take_drop_pad_combined[local]:
  !off (mem : word8 list) k.
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >> Cases_on `off <= LENGTH mem`
  >- rw[take_drop_pad_irrelevant]
  >- (`LENGTH mem <= off` by fs[] >> rw[take_drop_pad_beyond])
QED

(* If TAKE agrees, then TAKE-with-padding also agrees *)
Theorem take_cong_append[local]:
  !m (x:'a list) y pad.
    TAKE m x = TAKE m y ==>
    TAKE m (x ++ pad) = TAKE m (y ++ pad)
Proof
  Induct >- rw[] >>
  Cases_on `x` >> Cases_on `y` >> rw[]
QED

(* ===================================================================
   Memory disjointness: mload after mstore on disjoint regions
   =================================================================== *)

Theorem mload_mstore_disjoint_proof:
  !off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ==>
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  rpt strip_tac >>
  fs[mload_def, mstore_def, LET_THM, regions_disjoint_def] >>
  qabbrev_tac `mem = s.vs_memory` >>
  qabbrev_tac `expanded = if off1 + 32 > LENGTH mem
    then mem ++ REPLICATE (off1 + 32 - LENGTH mem) 0w else mem` >>
  `LENGTH (word_to_bytes val T) = 32` by rw[len_word_to_bytes_256] >>
  `off1 + 32 <= LENGTH expanded` by
    (rw[Abbr `expanded`] >> rw[LENGTH_APPEND, LENGTH_REPLICATE] >> fs[]) >>
  (* Step 1: splice lemma on the inner TAKE/DROP *)
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ word_to_bytes val T ++
     DROP (off1 + 32) expanded)) = TAKE 32 (DROP off2 expanded)` by
    (irule take_drop_splice_disjoint >> rw[]) >>
  (* Step 2: lift to padded version via take_cong_append *)
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ word_to_bytes val T ++
     DROP (off1 + 32) expanded) ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w)` by
    (irule take_cong_append >> rw[]) >>
  (* Step 3: padding irrelevance *)
  `TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 mem ++ REPLICATE 32 0w)` by
    (rw[Abbr `expanded`] >> rw[take_drop_pad_combined]) >>
  ASM_REWRITE_TAC[]
QED

Theorem mload_mstore8_disjoint_proof:
  !off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ==>
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  rpt strip_tac >>
  fs[mload_def, mstore8_def, LET_THM, regions_disjoint_def] >>
  qabbrev_tac `mem = s.vs_memory` >>
  qabbrev_tac `expanded = if off1 + 1 > LENGTH mem
    then mem ++ REPLICATE (off1 + 1 - LENGTH mem) 0w else mem` >>
  `LENGTH [w2w val : word8] = 1` by rw[] >>
  `off1 + 1 <= LENGTH expanded` by
    (rw[Abbr `expanded`] >> rw[LENGTH_APPEND, LENGTH_REPLICATE] >> fs[]) >>
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ [w2w val] ++
     DROP (off1 + 1) expanded)) = TAKE 32 (DROP off2 expanded)` by
    (irule take_drop_splice_disjoint >> rw[]) >>
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ [w2w val] ++
     DROP (off1 + 1) expanded) ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w)` by
    (irule take_cong_append >> rw[]) >>
  `TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 mem ++ REPLICATE 32 0w)` by
    (rw[Abbr `expanded`] >> rw[take_drop_pad_combined]) >>
  ASM_REWRITE_TAC[]
QED

(* ===================================================================
   allocas_non_overlapping + alloca_next_valid preservation
   =================================================================== *)

(* Combined alloca invariant: non-overlapping + bump pointer valid *)
(* next_alloca_offset >= base + sz for any existing alloca (conditional) *)
Theorem next_alloca_offset_ge[local]:
  !s aid base sz.
    alloca_next_valid s /\
    FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
    base + sz <= next_alloca_offset s
Proof
  rw[alloca_next_valid_def, next_alloca_offset_def] >>
  res_tac >> fs[]
QED

(* exec_alloca preserves alloca_inv *)
Theorem exec_alloca_preserves_inv[local]:
  !inst s s' alloc_size.
    exec_alloca inst s alloc_size = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[exec_alloca_def, LET_THM] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, update_var_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  res_tac >> fs[next_alloca_offset_def, arithmeticTheory.MAX_DEF]
QED

(* exec_alloca: vs_alloca_next monotone *)
Theorem exec_alloca_next_mono[local]:
  !inst s s' alloc_size.
    exec_alloca inst s alloc_size = OK s' ==>
    s.vs_alloca_next <= s'.vs_alloca_next
Proof
  rw[exec_alloca_def, LET_THM, update_var_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  simp[next_alloca_offset_def, arithmeticTheory.MAX_DEF]
QED

(* Non-ALLOCA, non-INVOKE step_inst_base preserves vs_allocas *)
Theorem step_inst_base_preserves_allocas[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  fs[step_inst_base_def, AllCaseEqs()] >>
  gvs[AllCaseEqs(),
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, extract_venom_result_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def,
      revert_state_def, eval_operands_def, jump_to_def,
      lookup_var_def, FLOOKUP_UPDATE, halt_state_def, set_returndata_def]
QED

(* Same for vs_alloca_next *)
Theorem step_inst_base_preserves_alloca_next[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  fs[step_inst_base_def, AllCaseEqs()] >>
  gvs[AllCaseEqs(),
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, extract_venom_result_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def,
      revert_state_def, eval_operands_def, jump_to_def,
      lookup_var_def, FLOOKUP_UPDATE, halt_state_def, set_returndata_def]
QED

(* Combined *)
Theorem step_inst_base_preserves_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  metis_tac[step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

(* Result predicate: alloca_inv + monotonicity *)
Definition result_alloca_inv_def:
  result_alloca_inv n0 (OK s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (IntRet vals s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Halt s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Abort a s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Error e) = T
End

(* exec_alloca lifted to result *)
Theorem exec_alloca_result_inv[local]:
  !inst (s:venom_state) alloc_size.
    alloca_inv s ==>
    result_alloca_inv s.vs_alloca_next (exec_alloca inst s alloc_size)
Proof
  rw[exec_alloca_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[result_alloca_inv_def] >>
  `exec_alloca inst s alloc_size =
     OK (update_var h (n2w (next_alloca_offset s))
       (s with <| vs_allocas :=
          s.vs_allocas |+ (inst.inst_id, (next_alloca_offset s, w2n alloc_size));
          vs_alloca_next := next_alloca_offset s + w2n alloc_size |>))` by
    simp[exec_alloca_def] >>
  metis_tac[exec_alloca_preserves_inv, exec_alloca_next_mono]
QED

(* FOLDL of update_var preserves vs_allocas and vs_alloca_next *)
Theorem foldl_update_var_alloca_fields[local]:
  !kvs base.
    (FOLDL (\s' (k,v). update_var k v s') base kvs).vs_allocas =
      base.vs_allocas /\
    (FOLDL (\s' (k,v). update_var k v s') base kvs).vs_alloca_next =
      base.vs_alloca_next
Proof
  Induct >> rw[] >> Cases_on `h` >> rw[update_var_def]
QED

Theorem setup_callee_inv[local]:
  !fn args s s'.
    setup_callee fn args s = SOME s' ==>
    alloca_inv s' /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[setup_callee_def, alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_DEF]
QED

Theorem merge_callee_inv[local]:
  !caller callee.
    alloca_inv caller /\
    caller.vs_alloca_next <= callee.vs_alloca_next ==>
    alloca_inv (merge_callee_state caller callee)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, merge_callee_state_def] >>
  res_tac >> fs[]
QED

Theorem foldl_update_var_inv[local]:
  !kvs base.
    alloca_inv base ==>
    alloca_inv (FOLDL (\s' (k,v). update_var k v s') base kvs)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  gvs[foldl_update_var_alloca_fields] >> metis_tac[]
QED

Theorem alloca_fields_eq_inv[local]:
  !s s'.
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

(* Monotonicity: weaker n0 is easier to satisfy *)
Theorem result_alloca_inv_mono[local]:
  !n0 n1 r. n0 <= n1 /\ result_alloca_inv n1 r ==> result_alloca_inv n0 r
Proof
  rpt gen_tac >> Cases_on `r` >> rw[result_alloca_inv_def]
QED

(* Joint induction: step_inst/exec_block/run_blocks preserve alloca_inv *)
Theorem alloca_inv_joint[local]:
  (!fuel ctx inst s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (run_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (
    (* P0: step_inst *)
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
      imp_res_tac setup_callee_inv >> gvs[] >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      conj_tac
      >- (irule foldl_update_var_inv >>
          irule merge_callee_inv >> gvs[])
      >- gvs[foldl_update_var_alloca_fields, merge_callee_state_def]
    )
    >> Cases_on `inst.inst_opcode = ALLOCA`
    >- (
      ONCE_REWRITE_TAC[step_inst_def] >> simp[step_inst_base_def] >>
      gvs[venomInstTheory.is_alloca_op_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
      metis_tac[exec_alloca_result_inv]
    )
    >> (
      (`step_inst fuel ctx inst s = step_inst_base inst s` by
        (ONCE_REWRITE_TAC[step_inst_def] >> simp[])) >>
      Cases_on `step_inst_base inst s` >>
      gvs[result_alloca_inv_def] >>
      imp_res_tac step_inst_base_preserves_alloca_fields >>
      imp_res_tac alloca_fields_eq_inv >> gvs[]
    )
  )
  >- (
    (* P1: exec_block *)
    ONCE_REWRITE_TAC[exec_block_def] >> simp[] >>
    rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
    (* Remaining: recursive case, ¬is_terminator *)
    `alloca_inv (v with vs_inst_idx := SUC s.vs_inst_idx)` by
      (irule alloca_fields_eq_inv >> qexists_tac `v` >> simp[]) >>
    first_x_assum drule >> strip_tac >>
    irule result_alloca_inv_mono >>
    qexists_tac `v.vs_alloca_next` >> gvs[]
  )
  >- (
    (* P2: run_blocks *)
    ONCE_REWRITE_TAC[run_blocks_def] >> simp[] >>
    rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
    (* Recursive case: exec_block returned OK, not halted *)
    (* Use exec_block IH to get alloca_inv on exec_block result *)
    `alloca_inv (s with vs_inst_idx := 0)` by
      (irule alloca_fields_eq_inv >> qexists_tac `s` >> simp[]) >>
    `alloca_inv v` by (
      first_x_assum drule >> strip_tac >>
      gvs[result_alloca_inv_def, AllCaseEqs()]) >>
    (* Use run_blocks IH *)
    first_x_assum drule >> simp[] >> strip_tac >>
    irule result_alloca_inv_mono >>
    qexists_tac `v.vs_alloca_next` >> gvs[] >>
    (* alloca_next monotonicity from exec_block *)
    first_x_assum (qspec_then `s with vs_inst_idx := 0` mp_tac) >>
    simp[] >> strip_tac >>
    gvs[result_alloca_inv_def, AllCaseEqs()]
  )
QED

(* ===== Exported theorems ===== *)

Theorem allocas_non_overlapping_empty_proof:
  !s. s.vs_allocas = FEMPTY ==> allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
QED

Theorem alloca_inv_empty_proof:
  !s. s.vs_allocas = FEMPTY ==> alloca_inv s
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, FLOOKUP_DEF]
QED

Theorem alloca_inv_step_inst_proof:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_exec_block_proof:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_run_block_proof:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[run_block_def] >> rpt strip_tac >>
  `alloca_inv (s with vs_inst_idx := 0)` by
    (irule alloca_fields_eq_inv >> qexists_tac `s` >> simp[]) >>
  metis_tac[alloca_inv_exec_block_proof]
QED

Theorem alloca_inv_run_blocks_proof:
  !fuel ctx fn s s'.
    run_blocks fuel ctx fn s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_run_function_proof:
  !fuel ctx fn s s'.
    run_function fuel ctx fn s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[run_function_def] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  `alloca_inv (s with <| vs_current_bb := x; vs_inst_idx := 0 |>)` by
    (irule alloca_fields_eq_inv >> qexists_tac `s` >> simp[]) >>
  metis_tac[alloca_inv_run_blocks_proof]
QED

(* Backward-compatible: allocas_non_overlapping preserved under alloca_inv *)
Theorem allocas_non_overlapping_step_inst_proof:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    alloca_inv s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_step_inst_proof, alloca_inv_def]
QED

Theorem allocas_non_overlapping_run_block_proof:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_run_block_proof, alloca_inv_def]
QED

Theorem allocas_non_overlapping_exec_block_proof:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_exec_block_proof, alloca_inv_def]
QED

Theorem did8[local] = EVAL``dimindex(:256) DIV 8``

Theorem mload_mstore_same_proof:
  ∀off val s.
    mload off (mstore off val s) = val
Proof
  simp[mload_def, mstore_def] >>
  rpt gen_tac >>
  rewrite_tac[TAKE_APPEND] >>
  rewrite_tac[DROP_APPEND, DROP_TAKE_EQ_NIL] >>
  simp_tac (std_ss ++ listSimps.LIST_ss)
    [LENGTH_word_to_bytes, LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [did8,
       iterateTheory.ADD_SUBR2, TAKE_APPEND,
       LENGTH_word_to_bytes] >>
    simp[LENGTH_word_to_bytes, TAKE_LENGTH_TOO_LONG]) >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [LENGTH_REPLICATE, did8, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
    simp[iterateTheory.ADD_SUBR2, TAKE_APPEND,
         TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] ) >>
  fs[]
QED

Theorem word_bytes_roundtrip_proof:
  ∀ (bytes : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bytes = dimindex(:α) DIV 8 ⇒
    word_to_bytes (word_of_bytes T (0w : α word) bytes) T = bytes
Proof
  rw[LIST_EQ_REWRITE, LENGTH_word_to_bytes]
  >> fs[]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux]
  >> simp[get_byte_word_of_bytes_be]
  >> DEP_REWRITE_TAC[first_byte_at_0w]
  >> rw[DIV_LE_X, dimindex_lt_dimword]
QED

Theorem word_of_bytes_be_inj_proof:
  ∀ (bs1 : byte list) (bs2 : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bs1 = dimindex(:α) DIV 8 ∧
    LENGTH bs2 = dimindex(:α) DIV 8 ∧
    word_of_bytes T (0w : α word) bs1 = word_of_bytes T (0w : α word) bs2 ⇒
    bs1 = bs2
Proof
  rw[] >>
  `word_to_bytes (word_of_bytes T 0w bs1 : α word) T =
   word_to_bytes (word_of_bytes T 0w bs2 : α word) T` by simp[] >>
  metis_tac[word_bytes_roundtrip_proof]
QED

Theorem word_to_bytes_be_w2w_proof:
  ∀ (w : α word).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β)
    ⇒
    word_to_bytes (w2w w : β word) T =
    PAD_LEFT 0w (dimindex(:β) DIV 8) (word_to_bytes w T)
Proof
  rw[PAD_LEFT, GSYM REPLICATE_GENLIST] >>
  simp[word_to_bytes_be_def, word_to_bytes_def] >>
  simp[LIST_EQ_REWRITE, LENGTH_word_to_bytes_aux] >>
  rw[]
  >- (
    irule $ GSYM SUB_ADD >>
    gvs[DIV_LE_X, LEFT_ADD_DISTRIB, DIVIDES_DIV] ) >>
  simp[EL_word_to_bytes_aux, EL_APPEND,
       LENGTH_word_to_bytes_aux, EL_REPLICATE] >>
  IF_CASES_TAC >- (
    simp[word_eq_0, w2w, word_lsr_def, get_byte_def, byte_index_def] >>
    simp[fcpTheory.FCP_BETA] >>
    gen_tac >> strip_tac >>
    qmatch_goalsub_abbrev_tac`x MOD db MOD b8` >>
    disj2_tac >>
    qmatch_goalsub_abbrev_tac`w2w w ' ii` >>
    `b8 < dimindex(:'b)` by gvs[Abbr`b8`] >>
    `dimindex(:'b) < db` by gvs[dimindex_lt_dimword,Abbr`db`] >>
    `x < db` by gvs[] >> gvs[] >>
    gvs[LEFT_SUB_DISTRIB] >>
    `8 * b8 = dimindex(:'b)` by gvs[Abbr`b8`, DIVIDES_DIV] >>
    gvs[] >>
    `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
    drule_at(Pos(el 2))DIV_SUB >>
    impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
    strip_tac >> gvs[X_LT_DIV] >>
    `ii < dimindex(:'b)` by gvs[Abbr`ii`] >>
    simp[w2w] >> gvs[Abbr`ii`] ) >>
  `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
  drule_at(Pos(el 2))DIV_SUB >>
  impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
  disch_then (strip_assume_tac o SYM) >> gvs[X_LT_DIV] >>
  simp[get_byte_def] >>
  qmatch_goalsub_abbrev_tac`ba DIV 8` >>
  qmatch_asmsub_abbrev_tac`db - da = _`>>
  simp[byte_index_def] >>
  assume_tac(INST_TYPE[alpha|->beta]dimindex_lt_dimword) >>
  gvs[] >>
  `x < db` by gvs[Abbr`db`,X_LT_DIV] >> gvs[] >>
  qmatch_goalsub_abbrev_tac`xxx MOD dw MOD da` >>
  `da < dimindex(:'a)` by simp[Abbr`da`] >>
  `dimindex(:'a) < dimword(:'a)` by simp[dimindex_lt_dimword] >> gvs[] >>
  `xxx < dw` by gvs[Abbr`xxx`] >> gvs[] >>
  `xxx < da` by gvs[Abbr`xxx`,Abbr`da`,X_LT_DIV] >> gvs[] >>
  `db - (x + 1) = da - (xxx + 1)` by (
    gvs[Abbr`xxx`] >>
    rewrite_tac[SUB_PLUS] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    qspecl_then[`x`,`ba DIV 8`]mp_tac SUB_SUB >>
    impl_tac >- simp[DIV_LE_X] >> simp[] >> disch_then kall_tac >>
    AP_THM_TAC >> AP_TERM_TAC >>
    `da <= db` suffices_by gvs[] >>
    unabbrev_all_tac >>
    irule DIV_LE_MONOTONE >> rw[] ) >>
  gvs[] >>
  simp[GSYM WORD_EQ, word_bit_def, w2w, word_lsr_def, fcpTheory.FCP_BETA]
QED

Theorem w2w_word_of_bytes_be_pad_left_proof:
  ∀ (l : byte list).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β) ∧
    LENGTH l = dimindex(:α) DIV 8
    ⇒
    w2w (word_of_bytes_be l : α word) =
    (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word)
Proof
  rw[] >>
  `word_to_bytes (w2w (word_of_bytes_be l : α word) : β word) T =
   word_to_bytes (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word) T`
    suffices_by metis_tac[word_of_bytes_word_to_bytes] >>
  simp[GSYM word_to_bytes_be_def, GSYM word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  simp[word_to_bytes_be_def, word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >>
  simp[bitstringTheory.length_pad_left, DIV_LE_MONOTONE] >>
  rw[] >> gvs[NOT_LESS]
  >- (qspec_then`8`imp_res_tac DIV_LE_MONOTONE >> gvs[]) >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >> simp[]
QED
