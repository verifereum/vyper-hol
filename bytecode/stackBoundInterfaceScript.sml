(* Proof interface for checker edges and a frame at fixed bottom depth.
   A suspended frame denotes its eventual continuation, not its saved stack. *)
Theory stackBoundInterface
Ancestors
  stackBoundDefs vfmExecution vfmExecutionProp vfmConstants
  list rich_list pair option finite_map words

Definition sb_successors_def:
  sb_successors code q =
    bytecode_stack_successors (parse_code 0 FEMPTY code)
      (FILTER (\pc. FLOOKUP (parse_code 0 FEMPTY code) pc = SOME JumpDest)
        (GENLIST I (LENGTH code))) q
End

Definition sb_decoded_def:
  sb_decoded c op <=>
    case FLOOKUP c.msgParams.parsed c.pc of
      SOME op' => op = op'
    | NONE => op = if LENGTH c.msgParams.code <= c.pc then Stop else Invalid
End

Definition sb_at_def:
  sb_at code (p,a) d s <=>
    0 < d /\ d <= LENGTH s.contexts /\
    let c = FST (EL (LENGTH s.contexts - d) s.contexts) in
      c.msgParams.code = code /\ c.jumpDest = NONE /\
      if LENGTH s.contexts = d then
        p = c.pc /\ bytecode_stack_describes a c.stack
      else
        p = c.pc + 1 /\
        ?b. a = NONE::b /\ bytecode_stack_describes b c.stack
End

Definition sb_inner_def:
  sb_inner op = bind (step_inst op) (\u. inc_pc_or_jump op)
End

Definition sb_opcode_contract_def:
  sb_opcode_contract op <=>
    !s a.
      wf_state s /\ s.contexts <> [] /\
      sb_decoded (FST (HD s.contexts)) op /\
      (FST (HD s.contexts)).jumpDest = NONE /\
      bytecode_stack_describes a (FST (HD s.contexts)).stack ==>
      (EVERY (\q. LENGTH (SND q) <= stack_limit)
         (sb_successors (FST (HD s.contexts)).msgParams.code
           ((FST (HD s.contexts)).pc,a)) ==>
       !t. ~(step_inst op s = (INR (SOME StackOverflow),t) /\
             LENGTH t.contexts = LENGTH s.contexts)) /\
      (!r t. sb_inner op s = (r,t) /\
             (r = INL () \/ LENGTH s.contexts < LENGTH t.contexts) ==>
       ?q. MEM q (sb_successors (FST (HD s.contexts)).msgParams.code
                    ((FST (HD s.contexts)).pc,a)) /\
           sb_at (FST (HD s.contexts)).msgParams.code q
             (LENGTH s.contexts) t)
End

Definition sb_step_simulates_def:
  sb_step_simulates <=>
    !s a t.
      wf_state s /\ s.contexts <> [] /\
      (FST (HD s.contexts)).jumpDest = NONE /\
      bytecode_stack_describes a (FST (HD s.contexts)).stack /\
      step s = (INL (),t) /\ LENGTH s.contexts <= LENGTH t.contexts ==>
      ?q. MEM q (sb_successors (FST (HD s.contexts)).msgParams.code
                  ((FST (HD s.contexts)).pc,a)) /\
          sb_at (FST (HD s.contexts)).msgParams.code q
            (LENGTH s.contexts) t
End

Definition sb_deeper_preserved_def:
  sb_deeper_preserved <=>
    !code q d s t.
      wf_state s /\ sb_at code q d s /\ d < LENGTH s.contexts /\
      step s = (INL (),t) /\ d <= LENGTH t.contexts ==>
      sb_at code q d t
End

Theorem sb_at_active:
  s.contexts = (c,rb)::rest ==>
  (sb_at code (p,a) (LENGTH s.contexts) s <=>
   c.msgParams.code = code /\ c.jumpDest = NONE /\
   p = c.pc /\ bytecode_stack_describes a c.stack)
Proof
  simp[sb_at_def]
QED

Theorem sb_at_suspended:
  0 < d /\ d < LENGTH s.contexts /\
  FST (EL (LENGTH s.contexts - d) s.contexts) = c ==>
  (sb_at code (p,a) d s <=>
   c.msgParams.code = code /\ c.jumpDest = NONE /\ p = c.pc + 1 /\
   ?b. a = NONE::b /\ bytecode_stack_describes b c.stack)
Proof
  simp[sb_at_def]
QED

(* Abstract stacks expose only their length and individual known words. *)
Theorem bytecode_stack_describes_length:
  bytecode_stack_describes a ws ==> LENGTH a = LENGTH ws
Proof
  simp[bytecode_stack_describes_def, LIST_REL_EL_EQN]
QED

Theorem bytecode_stack_describes_EL:
  bytecode_stack_describes a ws /\ n < LENGTH a ==>
  (case EL n a of NONE => T | SOME v => v = w2n (EL n ws))
Proof
  simp[bytecode_stack_describes_def, LIST_REL_EL_EQN]
QED

Theorem bytecode_stack_describes_drop:
  bytecode_stack_describes a ws ==>
  bytecode_stack_describes (DROP n a) (DROP n ws)
Proof
  simp[bytecode_stack_describes_def, LIST_REL_DROP]
QED

Theorem bytecode_stack_describes_dup:
  bytecode_stack_describes a ws /\ n < LENGTH a ==>
  bytecode_stack_describes (EL n a :: a) (EL n ws :: ws)
Proof
  strip_tac >> simp[bytecode_stack_describes_def] >>
  conj_tac >- (irule bytecode_stack_describes_EL >> metis_tac[]) >>
  gvs[bytecode_stack_describes_def]
QED

Theorem bytecode_stack_describes_swap:
  bytecode_stack_describes a ws /\ SUC n < LENGTH a ==>
  bytecode_stack_describes
    ([EL (SUC n) a] ++ TAKE n (TL a) ++ [HD a] ++ DROP (n+2) a)
    ([EL (SUC n) ws] ++ TAKE n (TL ws) ++ [HD ws] ++ DROP (n+2) ws)
Proof
  strip_tac >>
  `bytecode_stack_describes (DROP (n+2) a) (DROP (n+2) ws)` by
    metis_tac[bytecode_stack_describes_drop] >>
  Cases_on `a` >> Cases_on `ws` >>
  gvs[bytecode_stack_describes_def] >>
  conj_tac >- gvs[LIST_REL_EL_EQN] >>
  irule LIST_REL_APPEND_suff >>
  conj_tac >- simp[LIST_REL_TAKE] >>
  simp[]
QED

(* The same suspended promise works for every possible returned result word. *)
Theorem sb_at_resume:
  s.contexts = (child,rb0)::(c,rb)::rest /\
  sb_at code (p,a) (SUC (LENGTH rest)) s /\
  t.contexts = (c with <|pc := c.pc + 1; stack := w::c.stack|>,rb)::rest ==>
  sb_at code (p,a) (SUC (LENGTH rest)) t
Proof
  strip_tac >> gvs[sb_at_def, bytecode_stack_describes_def]
QED
