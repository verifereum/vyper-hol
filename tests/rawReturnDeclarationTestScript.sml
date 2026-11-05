Theory rawReturnDeclarationTest
Ancestors
  vyperTypeContract
Libs
  vyperCheckContractLib

fun raw_check vis ty literal =
  vyperCheckContractLib.check_contract_conv
    ``check_contract F [] 0w
        [(NONE, [FunctionDecl ^vis Pure F T "raw" [] [] ^ty
          [Return (SOME (Literal ^ty ^literal))]])]``

fun expect_some th =
  if optionSyntax.is_some (rhs (concl th)) then ()
  else raise Fail "raw-return contract unexpectedly rejected"

fun expect_none th =
  if optionSyntax.is_none (rhs (concl th)) then ()
  else raise Fail "invalid raw-return declaration accepted"

val () = expect_some
  (raw_check ``External`` ``BaseT (BytesT (Dynamic 8))`` ``BytesL [1w]``)

val () = expect_none
  (raw_check ``External`` ``BaseT (StringT 8)`` ``StringL "a"``)
val () = expect_none
  (raw_check ``External`` ``BaseT (UintT 256)`` ``IntL 1``)
val () = expect_none
  (raw_check ``Internal`` ``BaseT (BytesT (Dynamic 8))`` ``BytesL [1w]``)
