# AXI4 Lite/Full
This section is still in progress.

## Architecture
The AXI4 Lite/Full will be able to be configured as follows:
* **Source**: Assumptions as sink component with assertions for source outputs.
	* Usage: Verify source components.
* **Sink**: Assumptions as source component with assertions for sink outputs.
	* Usage: Verify sink components.
* **Constraints**: Assumptions as sink and source components.
	* Usage: 
		* Isolate issues. 
		* Fast verification of external props.
		* RTL-Bringup. 
		* Verify other VIP.
* **Monitor**: Assertions as sink and source components.
	* Usage: 
		* Isolate issues.
		* Verify transactions.
		* End-to-end checks.

---

## Development Plan
The file `AXI4 Lite_Full Propositions.xlsx` contains the development plan for this VIP.


