Theory bodyPtrIfExpWordMemory
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps loweringPosts
  valueEncoding vyperAST vyperTyping vyperValue

(* Runtime type evaluation alone does not type the returned value.  NoneV
   has a vacuous robust memory representation even at a word type.  This
   probe is not a counterexample to the frozen IfExp statement: its actual
   expression precondition may supply the missing value_has_type fact. *)
Theorem word_memory_untyped_none_probe[local]:
  is_word_type (BaseT BoolT) /\ val_wf (BaseTV BoolT) NoneV /\
  (!mem. val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~value_has_type (BaseTV BoolT) NoneV /\
  (!mem. mem_agree_outside {0} m mem ==>
         val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~(!i. 0 <= i /\ i < 32 ==> i NOTIN ({0}:num set))
Proof
  EVAL_TAC >> simp[]
QED
