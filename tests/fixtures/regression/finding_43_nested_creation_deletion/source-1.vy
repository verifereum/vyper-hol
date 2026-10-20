
interface Helper:
    def spawn_and_destroy() -> address: nonpayable

@external
def run(helper: address) -> address:
    return extcall Helper(helper).spawn_and_destroy()
