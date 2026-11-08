(* Exact bounded list summaries retain full records, including operand names.
   These algebraic facts do not certify any supported compiler producer. *)
Theory bodyPtrBytestringBuiltinsImageBoundary
Ancestors bodyPtrBytestringBuiltinsWindows compileEnv list rich_list arithmetic

Theorem bounded_prefix_append:
  !n xs ys.
    TAKE n (TAKE n xs ++ TAKE n ys) = TAKE n (xs ++ ys)
Proof
  rpt gen_tac >> Cases_on `n <= LENGTH xs`
  >- simp[rich_listTheory.TAKE_APPEND, LENGTH_TAKE_EQ, TAKE_TAKE_MIN, MIN_DEF] >>
  `LENGTH xs <= n` by decide_tac >>
  simp[rich_listTheory.TAKE_APPEND, LENGTH_TAKE_EQ, TAKE_TAKE_MIN, MIN_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem bounded_suffix_append:
  !n xs ys.
    REVERSE (TAKE n (REVERSE
      (REVERSE (TAKE n (REVERSE xs)) ++
       REVERSE (TAKE n (REVERSE ys))))) =
    REVERSE (TAKE n (REVERSE (xs ++ ys)))
Proof
  simp[REVERSE_APPEND, bounded_prefix_append]
QED

Theorem bounded_prefix_associative:
  !n xs ys zs.
    TAKE n (TAKE n (xs ++ ys) ++ TAKE n zs) =
    TAKE n (TAKE n xs ++ TAKE n (ys ++ zs))
Proof
  simp[bounded_prefix_append, APPEND_ASSOC]
QED

Theorem bounded_suffix_associative:
  !n xs ys zs.
    REVERSE (TAKE n (REVERSE
      (REVERSE (TAKE n (REVERSE (xs ++ ys))) ++
       REVERSE (TAKE n (REVERSE zs))))) =
    REVERSE (TAKE n (REVERSE
      (REVERSE (TAKE n (REVERSE xs)) ++
       REVERSE (TAKE n (REVERSE (ys ++ zs))))))
Proof
  simp[REVERSE_APPEND, bounded_prefix_append, APPEND_ASSOC]
QED

Theorem bounded_summary_empty:
  !n. TAKE n [] = ([]:'a list) /\
      REVERSE (TAKE n (REVERSE [])) = ([]:'a list)
Proof
  simp[]
QED

Theorem bounded_prefix_detect:
  !n pat xs. LENGTH pat <= n ==>
    ((?q. xs = pat ++ q) <=>
     (?q. TAKE n xs = pat ++ q))
Proof
  rpt strip_tac >> eq_tac
  >- (strip_tac >> gvs[] >>
      qexists_tac `TAKE (n - LENGTH pat) q` >>
      simp[rich_listTheory.TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  strip_tac >> qexists_tac `q ++ DROP n xs` >>
  metis_tac[TAKE_DROP, APPEND_ASSOC]
QED

Theorem bounded_suffix_detect:
  !n pat xs. LENGTH pat <= n ==>
    ((?p. xs = p ++ pat) <=>
     (?p. REVERSE (TAKE n (REVERSE xs)) = p ++ pat))
Proof
  rpt strip_tac >>
  `LENGTH (REVERSE pat) <= n` by simp[] >>
  drule bounded_prefix_detect >>
  disch_then (qspec_then `REVERSE xs` mp_tac) >>
  metis_tac[REVERSE_REVERSE, REVERSE_APPEND]
QED


Theorem bounded_crossing_detect:
  !n left right xs ys.
    LENGTH left <= n /\ LENGTH right <= n ==>
    ((?p q. xs = p ++ left /\ ys = right ++ q) <=>
     (?p q. REVERSE (TAKE n (REVERSE xs)) = p ++ left /\
            TAKE n ys = right ++ q))
Proof
  rpt strip_tac >>
  `!A B. ((?p q. A p /\ B q) <=> ((?p. A p) /\ (?q. B q)))`
    by metis_tac[] >>
  first_x_assum (fn th => pure_rewrite_tac[th]) >>
  metis_tac[bounded_suffix_detect, bounded_prefix_detect]
QED

Theorem four_window_boundary:
  !xs ys a b c d.
    (?p q. xs ++ ys = p ++ [a;b;c;d] ++ q) <=>
    (?p q. xs = p ++ [a;b;c;d] ++ q) \/
    (?p q. ys = p ++ [a;b;c;d] ++ q) \/
    (?p q. REVERSE (TAKE 3 (REVERSE xs)) = p ++ [a] /\
           TAKE 3 ys = [b;c;d] ++ q) \/
    (?p q. REVERSE (TAKE 3 (REVERSE xs)) = p ++ [a;b] /\
           TAKE 3 ys = [c;d] ++ q) \/
    (?p q. REVERSE (TAKE 3 (REVERSE xs)) = p ++ [a;b;c] /\
           TAKE 3 ys = [d] ++ q)
Proof
  rpt gen_tac >> pure_rewrite_tac[four_window_append] >>
  simp[GSYM bounded_crossing_detect]
QED

(* Finalization is per block: no relation between consecutive blocks' records.
   P may be the absence of the linked window in one instruction list. *)
Theorem new_block_per_block:
  !P label st old st'.
    new_block label st = (old,st') ==>
    ((EVERY (\bb. P bb.bb_instructions) st'.cs_blocks /\
      P st'.cs_current_insts) <=>
     (EVERY (\bb. P bb.bb_instructions) st.cs_blocks /\
      P st.cs_current_insts /\ P []))
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Producer contract audit (not a proved compiler-image invariant).

   Write H(xs)=TAKE 3 xs and T(xs)=REVERSE(TAKE 3(REVERSE xs)).
   A live fragment xs carries H(xs), T(xs), and a SEPARATE internal-window
   exclusion/classification. four_window_boundary accounts for every append
   xs++ys using both internal properties and its three explicit cut premises.
   bounded_prefix_append and bounded_suffix_append compute the new endpoints;
   their associativity facts permit regrouping, never omission of cut premises.

   Actual state operations, compileEnvScript.sml:
   emit_def: (label,xs,blocks) -> (label,xs++[inst],blocks).
     Apply the append contract, including the linked-record cut test.
   fresh_var_def/fresh_id_def/fresh_label_def change counters only.
   comp_get_def saves the entire state without changing any fragment.
   comp_set_def can replace the ENTIRE state arbitrarily. There is no automatic
     preservation fact for comp_set. For a saved parent (label,xs,blocks), a
     restore to exactly those fields recovers its endpoints/internal property,
     NOT the child's tail. An arbitrary replacement requires its own contract.
     The production defs search found no comp_set consumer. compile_stmt If
     uses comp_get only to test termination, not to rewind code or counters.
   new_block_def: (label,xs,blocks) -> (newlabel,[],bb(label,xs)::blocks).
     No suffix is added by this operation; new_block_per_block is exact.
     emitHelper.emit_jmp_if_not_terminated_def MAY append a JMP BEFORE
     new_block; that append must discharge its own cut premises first.

   Saved OPERANDS are distinct from saved instruction frontiers. The existing
   CompilerSeams.emit_op_ne_saved_allocation retains parent buffer buf from
   compile_alloc_buffer bytes sa=(buf,sb), requires sb.next_var<=sc.next_var,
   and separates emit_op at sc from buf. Its safe_operand_mono interface
   transports saved operand age through nested producers provided counters
   are monotone. No assumption of arbitrary environment freshness is needed.
   That does not classify all nested producers' internal windows or cuts.
   Counter rollback via arbitrary comp_set would invalidate this argument.

   Installation, vyperCompilerScript.sml:
   extract_context_def packages REVERSE blocks ++ [bb(label,xs)] into a raw
   function; package_internal_blocks_def partitions WHOLE blocks at labels;
   mk_internal_function_def changes ABI metadata only. fn_reachable_blocks_def
   filters WHOLE blocks. These operations must transport per-block properties,
   not a property of the flattened stream. Other imports/rewrites/splices must
   independently establish the same per-block property.

   Remaining interface obligations: supported recursive producers must prove
   internal-window classification and all three cuts, counter monotonicity,
   and saved operand preservation. Wrappers and unit installation must prove
   these for their complete block carriers. The list theory and state transfer
   above do NOT establish those obligations or concat_header_free for an
   actual supported compiler image. Downstream image risks remain unchanged.
*)
