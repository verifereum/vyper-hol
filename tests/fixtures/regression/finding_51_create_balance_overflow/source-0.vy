
@external
def attempt(salt: bytes32) -> address:
    return create_minimal_proxy_to(
        self,
        value=1,
        salt=salt,
        revert_on_failure=False,
    )
