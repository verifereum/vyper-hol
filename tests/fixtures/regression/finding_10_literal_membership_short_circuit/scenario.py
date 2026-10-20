"""Finding 10: legacy membership stops after finding an equal item."""

CONTRACT = """
@external
@pure
def contains(divisor: uint256) -> bool:
    return 1 in [1, 1 // divisor]
"""


def test_matching_prefix_avoids_later_division_by_zero(
    get_contract, compiler_settings, tx_failed
):
    contract = get_contract(CONTRACT, compiler_settings=compiler_settings)

    # Legacy codegen evaluates membership left-to-right and returns immediately.
    # Experimental codegen evaluates the literal first and therefore reverts.
    if compiler_settings.experimental_codegen:
        with tx_failed():
            contract.contains(0)
    else:
        assert contract.contains(0) is True

    assert contract.contains(1) is True
    assert contract.contains(2) is True
