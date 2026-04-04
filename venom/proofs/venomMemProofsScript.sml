(*
 * Venom Memory Proofs
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty_proof     — base case
 *   allocas_non_overlapping_step_inst_proof — preserved by step_inst
 *   allocas_non_overlapping_run_block_proof — preserved by run_block
 *   mload_mstore_disjoint_proof             — 32-byte write/read independence
 *   mload_mstore8_disjoint_proof            — 1-byte write / 32-byte read
 *)

Theory venomMemProofs
Ancestors
  venomMemDefs venomExecSemantics venomState venomInstProofs
  finite_map list rich_list

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

Theorem allocas_non_overlapping_empty_proof:
  !s. s.vs_allocas = FEMPTY ==> allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
QED

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
   allocas_non_overlapping preservation
   =================================================================== *)

(* FOLDL MAX >= init: accumulator only grows *)
Theorem foldl_max_ge_init[local]:
  !(l : (num # num # num) list) acc.
    acc <= FOLDL (\m (k,off,sz). MAX m (off + sz)) acc l
Proof
  Induct >> rw[] >> PairCases_on `h` >> rw[] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `MAX acc (h1 + h2)` >>
  simp[arithmeticTheory.MAX_LE] >>
  first_x_assum (qspec_then `MAX acc (h1 + h2)` assume_tac) >> fs[]
QED

(* next_alloca_offset >= base + sz for any existing alloca *)
Theorem next_alloca_offset_ge[local]:
  !s aid base sz.
    FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
    base + sz <= next_alloca_offset s
Proof
  rw[next_alloca_offset_def] >>
  `aid IN FDOM s.vs_allocas /\ s.vs_allocas ' aid = (base', sz)` by
    fs[FLOOKUP_DEF] >>
  `MEM (aid, base', sz) (fmap_to_alist s.vs_allocas)` by
    metis_tac[alistTheory.MEM_fmap_to_alist] >>
  pop_assum mp_tac >>
  qspec_tac (`LENGTH s.vs_memory`, `acc`) >>
  qspec_tac (`fmap_to_alist s.vs_allocas`, `l`) >>
  Induct >> rw[] >> simp[] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `MAX acc (base' + sz)` >> conj_tac
  >- simp[arithmeticTheory.MAX_LE]
  >- metis_tac[foldl_max_ge_init]
QED

(* Helper: exec_alloca preserves allocas_non_overlapping *)
Theorem exec_alloca_preserves_non_overlapping[local]:
  !inst s s' alloc_size.
    exec_alloca inst s alloc_size = OK s' /\
    allocas_non_overlapping s ==>
    allocas_non_overlapping s'
Proof
  rw[exec_alloca_def, allocas_non_overlapping_def, LET_THM,
     update_var_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rpt strip_tac >>
  gvs[FLOOKUP_UPDATE] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  metis_tac[next_alloca_offset_ge]
QED

(* Non-ALLOCA, non-INVOKE step_inst preserves vs_allocas *)
(* Strengthened: covers ALL result types (OK, Halt, Abort, IntRet), not just OK *)
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

(* Result-state predicate: extract state from any non-Error result *)
Definition result_allocas_ok_def:
  result_allocas_ok (OK s') = allocas_non_overlapping s' /\
  result_allocas_ok (IntRet vals s') = allocas_non_overlapping s' /\
  result_allocas_ok (Halt s') = allocas_non_overlapping s' /\
  result_allocas_ok (Abort a s') = allocas_non_overlapping s' /\
  result_allocas_ok (Error e) = T
End

(* Lifted to result_allocas_ok for use in joint proof *)
Theorem exec_alloca_result_allocas_ok[local]:
  !inst (s:venom_state) alloc_size.
    allocas_non_overlapping s ==>
    result_allocas_ok (exec_alloca inst s alloc_size)
Proof
  rw[exec_alloca_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[result_allocas_ok_def] >>
  `exec_alloca inst s alloc_size =
     OK (update_var h (n2w (next_alloca_offset s))
       (s with vs_allocas :=
          s.vs_allocas |+ (inst.inst_id, (next_alloca_offset s, w2n alloc_size))))` by
    simp[exec_alloca_def] >>
  metis_tac[exec_alloca_preserves_non_overlapping]
QED

(* FOLDL of update_var preserves vs_allocas *)
Theorem foldl_update_var_allocas[local]:
  !kvs base. (FOLDL (\s' (k,v). update_var k v s') base kvs).vs_allocas =
             base.vs_allocas
Proof
  Induct >> rw[] >> Cases_on `h` >> rw[update_var_def]
QED

Theorem setup_callee_preserves_allocas[local]:
  !fn args s s'. setup_callee fn args s = SOME s' /\
    allocas_non_overlapping s ==> allocas_non_overlapping s'
Proof
  rw[setup_callee_def, allocas_non_overlapping_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem merge_callee_preserves_allocas[local]:
  !caller callee. allocas_non_overlapping callee ==>
    allocas_non_overlapping (merge_callee_state caller callee)
Proof
  rw[allocas_non_overlapping_def, merge_callee_state_def]
QED

Theorem foldl_update_var_preserves_allocas[local]:
  !kvs base. allocas_non_overlapping base ==>
    allocas_non_overlapping (FOLDL (\s' (k,v). update_var k v s') base kvs)
Proof
  rw[allocas_non_overlapping_def, foldl_update_var_allocas]
QED

Theorem vs_allocas_eq_preserves[local]:
  !s s'. s'.vs_allocas = s.vs_allocas /\ allocas_non_overlapping s ==>
    allocas_non_overlapping s'
Proof
  rw[allocas_non_overlapping_def]
QED

(* Joint induction: step_inst/run_block/run_function all preserve allocas_non_overlapping *)
Theorem allocas_non_overlapping_joint[local]:
  (!fuel ctx inst s.
     allocas_non_overlapping s ==>
     result_allocas_ok (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
     allocas_non_overlapping s ==>
     result_allocas_ok (run_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
     allocas_non_overlapping s ==>
     result_allocas_ok (run_function fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (
    (* P0: step_inst *)
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      simp[Once step_inst_def] >>
      BasicProvers.EVERY_CASE_TAC >> gvs[result_allocas_ok_def] >>
      imp_res_tac setup_callee_preserves_allocas >> gvs[] >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      irule foldl_update_var_preserves_allocas >>
      irule merge_callee_preserves_allocas >> gvs[]
    )
    >> Cases_on `inst.inst_opcode = ALLOCA`
    >- (
      simp[Once step_inst_def, step_inst_base_def] >>
      gvs[venomInstTheory.is_alloca_op_def] >>
      BasicProvers.EVERY_CASE_TAC >> gvs[result_allocas_ok_def] >>
      metis_tac[exec_alloca_result_allocas_ok]
    )
    >> (
      `step_inst fuel ctx inst s = step_inst_base inst s` by
        fs[Once step_inst_def] >>
      Cases_on `step_inst_base inst s` >>
      gvs[result_allocas_ok_def] >>
      imp_res_tac step_inst_base_preserves_allocas >>
      metis_tac[vs_allocas_eq_preserves]
    )
  )
  >- (
    (* P1: run_block *)
    simp[Once run_block_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[result_allocas_ok_def] >>
    first_x_assum irule >>
    irule vs_allocas_eq_preserves >> simp[] >> metis_tac[]
  )
  >- (
    (* P2: run_function *)
    simp[Once run_function_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[result_allocas_ok_def] >>
    first_x_assum drule >> simp[result_allocas_ok_def] >> strip_tac >>
    first_x_assum irule >> gvs[]
  )
QED

Theorem allocas_non_overlapping_step_inst_proof:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    allocas_non_overlapping s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[allocas_non_overlapping_joint, result_allocas_ok_def]
QED

Theorem allocas_non_overlapping_run_block_proof:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    allocas_non_overlapping s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[allocas_non_overlapping_joint, result_allocas_ok_def]
QED
