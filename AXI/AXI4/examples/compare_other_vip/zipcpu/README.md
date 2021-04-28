# AMBA AXI4 Monitor
Comparing (or testing) different Formal-based SVA IPs found on the wild.
TBD: Fully document this example.

## Notes:
FIXED with the **OPTIONAL_RESET** parameter.
My monitor is not being tested because the reset properties in `faxil_master` and `faxil_slave` are failing. My monitor does not provide any assumptions, it is supposed that both `faxil_master` and `faxil_slave` should handle this scenario themselves but seems that they are not, so I don't know if this demo is really useful (the goal is to find problems **on my formal IP**, not to debug any other existing formal IP.

Note 2: I need to find a better formal IP, this one should't fail from the internals (I mean, their source with their sink are failing). I would expect something that pass with their internals and fails with my monitor, or in the other way around.

Note 3: At least all covers are reached.
